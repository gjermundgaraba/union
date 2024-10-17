use std::{
    borrow::Borrow, cmp::Eq, collections::HashMap, future::Future, hash::Hash, marker::PhantomData,
    time::Duration,
};

use frame_support_procedural::{CloneNoBound, DebugNoBound};
use futures_util::TryStreamExt;
use itertools::Itertools;
use schemars::JsonSchema;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use sqlx::{postgres::PgPoolOptions, prelude::FromRow, types::Json, Either, Executor, PgPool};
use tracing::{debug, debug_span, info_span, instrument, trace, Instrument};
use voyager_vm::{
    filter::{FilterResult, InterestFilter},
    pass::{Pass, PassResult},
    Captures, Op, QueueMessage,
};

use crate::metrics::{ITEM_PROCESSING_DURATION, OPTIMIZE_ITEM_COUNT, OPTIMIZE_PROCESSING_DURATION};

pub mod metrics;

/// A fifo queue backed by a postgres table. Not suitable for high-throughput, but enough for ~1k items/sec.
///
/// The queue assumes the following database schema:
///
/// ```ignore
/// id SERIAL AUTO INCREMENT
/// status 0..2
/// item JSONB
/// error TEXT
/// ```
#[derive(DebugNoBound, CloneNoBound)]
pub struct PgQueue<T> {
    client: PgPool,
    __marker: PhantomData<fn() -> T>,
}

#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct PgQueueConfig {
    pub database_url: String,
    pub max_connections: Option<u32>,
    pub min_connections: Option<u32>,
    pub idle_timeout: Option<Duration>,
    pub max_lifetime: Option<Duration>,
}

impl PgQueueConfig {
    pub async fn into_pg_pool(self) -> sqlx::Result<PgPool> {
        PgPoolOptions::new()
            .max_connections(self.max_connections.unwrap_or(10))
            .min_connections(self.min_connections.unwrap_or(0))
            .idle_timeout(self.idle_timeout)
            .max_lifetime(self.max_lifetime)
            .connect(&self.database_url)
            .await
    }
}

#[derive(FromRow)]
struct Id {
    id: i64,
}

#[derive(Debug, FromRow)]
struct Record {
    id: i64,
    parents: Vec<i64>,
    item: String,
    created_at: sqlx::types::time::OffsetDateTime,
}

#[derive(Debug, FromRow, Serialize)]
#[serde(bound(serialize = ""))]
pub struct FailedRecord<T: QueueMessage> {
    pub id: i64,
    pub parents: Vec<i64>,
    pub item: Json<Op<T>>,
    pub message: String,
    // pub created_at: sqlx::types::time::OffsetDateTime,
}

impl<T: QueueMessage> PgQueue<T> {
    pub async fn query_failed(
        &self,
        page: i64,
        per_page: i64,
        mut item_filters: Vec<String>,
        mut message_filters: Vec<String>,
    ) -> Result<Vec<FailedRecord<T>>, sqlx::Error> {
        // default to all-inclusive filter if none are provided
        if item_filters.is_empty() {
            item_filters.push("%".to_owned())
        }

        if message_filters.is_empty() {
            message_filters.push("%".to_owned())
        }

        sqlx::query(
            r#"
            SELECT
                id,
                parents,
                item,
                message
            FROM
                failed 
            WHERE
                item::TEXT LIKE ANY($1) 
                AND message LIKE ANY($2) 
            ORDER BY
                id DESC
            LIMIT
                $3
            OFFSET
                $4
            "#,
        )
        .bind(item_filters)
        .bind(message_filters)
        .bind(per_page)
        .bind((page - 1) * per_page)
        .map(|row| FailedRecord::<T>::from_row(&row))
        .fetch_all(&self.client)
        .await?
        .into_iter()
        .collect()
    }

    pub async fn query_failed_by_id(
        &self,
        id: i64,
    ) -> Result<Option<FailedRecord<T>>, sqlx::Error> {
        sqlx::query(
            r#"
            SELECT
               id,
               parents,
               item,
               message
            FROM
               failed 
            WHERE
               id = $1
            "#,
        )
        .bind(id)
        .map(|row| FailedRecord::<T>::from_row(&row))
        .fetch_optional(&self.client)
        .await?
        .transpose()
    }
}

impl<T: QueueMessage> voyager_vm::Queue<T> for PgQueue<T> {
    type Config = PgQueueConfig;
    // type Error = tokio_postgres::Error;
    type Error = sqlx::Error;

    async fn new(config: Self::Config) -> Result<Self, Self::Error> {
        // // Connect to the database.
        // let (client, connection) = tokio_postgres::connect(&config.database_url, NoTls).await?;

        // // The connection object performs the actual communication with the database,
        // // so spawn it off to run on its own.
        // tokio::spawn(async move {
        //     if let Err(e) = connection.await {
        //         eprintln!("connection error: {}", e);
        //     }
        // });

        let pool = config.into_pg_pool().await?;

        pool.execute_many(
            r#"
            CREATE TABLE IF NOT EXISTS queue(
                id BIGSERIAL PRIMARY KEY,
                item JSONB NOT NULL,
                parents BIGINT[] DEFAULT '{}',
                created_at timestamptz NOT NULL DEFAULT now()
            );

            CREATE TABLE IF NOT EXISTS optimize(
                -- TODO: Figure out how to do this properly
                id BIGINT PRIMARY KEY DEFAULT nextval('queue_id_seq'::regclass),
                item JSONB NOT NULL,
                tag text NOT NULL,
                parents BIGINT[] DEFAULT '{}',
                created_at timestamptz NOT NULL DEFAULT now()
            );

            CREATE TABLE IF NOT EXISTS done(
                id BIGINT,
                item JSONB NOT NULL,
                parents BIGINT[] DEFAULT '{}',
                created_at timestamptz NOT NULL DEFAULT now(),
                PRIMARY KEY (id, created_at)
            );

            CREATE TABLE IF NOT EXISTS failed(
                id BIGINT PRIMARY KEY,
                item JSONB NOT NULL,
                parents BIGINT[] DEFAULT '{}',
                message TEXT,
                created_at timestamptz NOT NULL DEFAULT now()
            );

            CREATE INDEX IF NOT EXISTS index_queue_id ON queue(id);
            "#,
        )
        .try_for_each(
            |result| async move { Ok(trace!("rows affected: {}", result.rows_affected())) },
        )
        .instrument(info_span!("init"))
        .await?;

        Ok(Self {
            client: pool,
            __marker: PhantomData,
        })
    }

    async fn enqueue<'a>(&'a self, op: Op<T>, filter: &'a T::Filter) -> Result<(), Self::Error> {
        trace!("enqueue");

        let (optimize, ready): (Vec<_>, Vec<_>) =
            op.normalize()
                .into_iter()
                .partition_map(|op| match filter.check_interest(&op) {
                    FilterResult::Interest(tag) => Either::Left((op, tag)),
                    FilterResult::NoInterest => Either::Right(op),
                });

        let mut tx = self.client.begin().await?;

        let ready_ids = sqlx::query(
            "
            INSERT INTO queue (item)
            SELECT * FROM UNNEST($1::JSONB[])
            RETURNING id
            ",
        )
        .bind(ready.into_iter().map(Json).collect::<Vec<_>>())
        .try_map(|x| Id::from_row(&x))
        .fetch_all(tx.as_mut())
        .await?;

        for ready in ready_ids {
            debug!(id = ready.id, "enqueued ready item");
        }

        let optimize_further_ids = sqlx::query(
            "
            INSERT INTO optimize (item, tag)
            SELECT * FROM UNNEST($1::JSONB[], $2::TEXT[])
            RETURNING id
            ",
        )
        .bind(
            optimize
                .clone()
                .into_iter()
                .map(|x| Json(x.0))
                .collect::<Vec<_>>(),
        )
        .bind(optimize.into_iter().map(|x| x.1).collect::<Vec<_>>())
        .try_map(|x| Id::from_row(&x))
        .fetch_all(tx.as_mut())
        .await?;

        for ready in optimize_further_ids {
            debug!(id = ready.id, "enqueued optimize item");
        }

        tx.commit().await?;

        Ok(())
    }

    #[instrument(skip_all)]
    async fn process<'a, F, Fut, R>(
        &'a self,
        filter: &'a T::Filter,
        f: F,
    ) -> Result<Option<R>, Self::Error>
    where
        F: (FnOnce(Op<T>) -> Fut) + Send + Captures<'a>,
        Fut: Future<Output = (R, Result<Vec<Op<T>>, String>)> + Send + Captures<'a>,
        R: Send + Sync + 'static,
    {
        trace!("process");

        let mut tx = self.client.begin().await?;

        let row = sqlx::query(
            r#"
            DELETE FROM
              queue
            WHERE
              id = (
                SELECT
                  id
                FROM
                  queue
                ORDER BY
                  id ASC
                FOR UPDATE
                  SKIP LOCKED
                LIMIT 1)
            RETURNING
              id,
              parents,
              item::text,
              created_at
            "#,
        )
        .try_map(|x| Record::from_row(&x))
        .fetch_optional(tx.as_mut())
        .await?;

        match row {
            Some(row) => {
                let span = info_span!("processing item", id = row.id);

                trace!(%row.item);

                // really don't feel like defining a new error type right now
                let op = de(&row.item).map_err(|e| sqlx::Error::Decode(Box::new(e)))?;

                let timer = ITEM_PROCESSING_DURATION.start_timer();
                let (r, res) = f(op).instrument(span).await;
                let _ = timer.stop_and_record();

                match res {
                    Err(error) => {
                        // insert error message and the op into failed
                        sqlx::query(
                            r#"
                            INSERT INTO
                            failed (id, parents, item,      created_at, message)
                            VALUES ($1, $2,      $3::JSONB, $4,         $5     )
                            "#,
                        )
                        .bind(row.id)
                        .bind(row.parents)
                        .bind(row.item)
                        .bind(row.created_at)
                        .bind(error)
                        .execute(tx.as_mut())
                        .await?;
                        tx.commit().await?;
                    }
                    Ok(ops) => {
                        'block: {
                            // insert the op we just processed into done
                            sqlx::query(
                                "
                                INSERT INTO
                                done   (id, parents, item,      created_at)
                                VALUES ($1, $2,      $3::JSONB, $4        )
                                ",
                            )
                            .bind(row.id)
                            .bind(row.parents)
                            .bind(row.item)
                            .bind(row.created_at)
                            .execute(tx.as_mut())
                            .await?;

                            if ops.is_empty() {
                                break 'block;
                            }

                            let (optimize, ready): (Vec<_>, Vec<_>) = ops
                                .into_iter()
                                .flat_map(Op::normalize)
                                .partition_map(|op| match filter.check_interest(&op) {
                                    FilterResult::Interest(tag) => Either::Left((op, tag)),
                                    FilterResult::NoInterest => Either::Right(op),
                                });

                            sqlx::query(
                                "
                                INSERT INTO queue (item)
                                SELECT * FROM UNNEST($1::JSONB[])
                                ",
                            )
                            .bind(ready.into_iter().map(Json).collect::<Vec<_>>())
                            .execute(tx.as_mut())
                            .await?;

                            sqlx::query(
                                "
                                INSERT INTO optimize (item, tag)
                                SELECT * FROM UNNEST($1::JSONB[], $2::TEXT[])
                                ",
                            )
                            .bind(optimize.iter().map(|(op, _)| Json(op)).collect::<Vec<_>>())
                            .bind(optimize.iter().map(|(_, tag)| *tag).collect::<Vec<_>>())
                            .execute(tx.as_mut())
                            .await?;
                        }

                        tx.commit().await?;
                    }
                }

                Ok(Some(r))
            }
            None => {
                // trace!("queue is empty");

                // self.lock.store(true, Ordering::SeqCst);
                // tokio::time::sleep(std::time::Duration::from_millis(2000)).await;

                Ok(None)
            }
        }
    }

    async fn optimize<'a, O: Pass<T>>(
        &'a self,
        tag: &'a str,
        optimizer: &'a O,
    ) -> Result<(), Either<Self::Error, O::Error>> {
        trace!(%tag, "optimize");

        // if self.lock.swap(false, Ordering::SeqCst) {
        //     debug!("queue is locked");
        //     tokio::time::sleep(std::time::Duration::from_millis(1000)).await;
        // }

        let mut tx = self.client.begin().await.map_err(Either::Left)?;

        let msgs = sqlx::query(
            r#"
            DELETE FROM
              optimize
            WHERE
              id = ANY(
                SELECT
                  id
                FROM
                  optimize
                WHERE
                  tag = $1
                ORDER BY
                  id ASC
                FOR UPDATE
                  SKIP LOCKED
              )
            RETURNING
              id,
              parents,
              item::text,
              created_at
            "#,
        )
        .bind(tag)
        .try_map(|x| Record::from_row(&x))
        .fetch_all(tx.as_mut())
        .await
        .map_err(Either::Left)?;

        if msgs.is_empty() {
            trace!("optimizer queue is empty");
            tokio::time::sleep(Duration::from_millis(100)).await;
            return Ok(());
        }

        let (ids, msgs) = msgs
            .into_iter()
            .map(|r| {
                Ok((
                    r.id,
                    de(&r.item).map_err(|e| sqlx::Error::Decode(Box::new(e)))?,
                ))
            })
            .collect::<Result<(Vec<_>, Vec<_>), sqlx::Error>>()
            .map_err(Either::Left)?;

        OPTIMIZE_ITEM_COUNT.observe(msgs.len() as f64);
        let timer = OPTIMIZE_PROCESSING_DURATION.start_timer();

        let PassResult {
            optimize_further,
            ready,
        } = optimizer
            .run_pass(msgs.clone())
            .instrument(debug_span!(
                "optimizing items",
                ids = ids
                    .iter()
                    .map(|id| id.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ))
            .await
            .map_err(Either::Right)?;
        let _ = timer.stop_and_record();

        trace!(
            ready = ready.len(),
            optimize_further = optimize_further.len(),
            "optimized items"
        );

        let get_parent_ids = |parent_idxs: &[usize]| {
            ids.iter()
                .enumerate()
                .filter_map(|(idx, id)| parent_idxs.contains(&idx).then_some(*id))
                .collect::<Vec<_>>()
        };

        for (parent_idxs, new_msg, tag) in optimize_further {
            let parents = get_parent_ids(&parent_idxs);
            trace!(parent_idxs = ?&parent_idxs, parents = ?&parents);

            let new_row = sqlx::query(
                "
                INSERT INTO optimize (item, parents, tag)
                VALUES
                    ($1::JSONB, $2, $3)
                RETURNING id
                ",
            )
            .bind(Json(new_msg))
            .bind(&parents)
            .bind(tag)
            .try_map(|row| Id::from_row(&row))
            .fetch_one(tx.as_mut())
            .await
            .map_err(Either::Left)?;

            debug!(id = new_row.id, "inserted new optimizer message");
        }

        for (parent_idxs, new_msg) in ready {
            let parents = get_parent_ids(&parent_idxs);
            trace!(parent_idxs = ?&parent_idxs, parents = ?&parents);

            let new_row = sqlx::query(
                "
                INSERT INTO queue (item, parents)
                VALUES
                    ($1::JSONB, $2)
                RETURNING id
                ",
            )
            .bind(Json(new_msg))
            .bind(&parents)
            .try_map(|x| Id::from_row(&x))
            .fetch_one(tx.as_mut())
            .await
            .map_err(Either::Left)?;

            debug!(id = new_row.id, "inserted new message");
        }

        tx.commit().await.map_err(Either::Left)?;

        Ok(())
    }
}

#[derive(sqlx::Type)]
#[sqlx(type_name = "status", rename_all = "lowercase")]
pub enum EnqueueStatus {
    Ready,
    Optimize,
}

fn de<T: DeserializeOwned>(s: &str) -> Result<T, serde_json::Error> {
    let mut deserializer = serde_json::Deserializer::from_str(s);
    deserializer.disable_recursion_limit();
    // let deserializer = serde_stacker::Deserializer::new(&mut deserializer);
    let json = T::deserialize(&mut deserializer)?;
    Ok(json)
}

pub trait MapExt<K, V> {
    fn get_many<'a, Q>(&'a self, ks: impl IntoIterator<Item = &'a Q>) -> Vec<&'a V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq + 'a;
}

impl<K: Hash + Eq, V> MapExt<K, V> for HashMap<K, V> {
    fn get_many<'a, Q>(&'a self, ks: impl IntoIterator<Item = &'a Q>) -> Vec<&'a V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq + 'a,
    {
        let mut out = vec![];

        for k in ks {
            out.extend(self.get(k));
        }

        out
    }
}
