pub mod client;
pub mod consensus_state;
pub mod context;
#[cfg(any(test, not(feature = "library")))]
pub mod contract;
pub mod custom_query;
pub mod errors;

#[cfg(feature = "mainnet")]
pub use unionlabs::ethereum::config::Minimal as Config;
#[cfg(feature = "minimal")]
pub use unionlabs::ethereum::config::Minimal as Config;

#[cfg(all(feature = "minimal", feature = "mainnet"))]
compile_error!(r#"cannot enable both "minimal" and "mainnet""#);

#[cfg(all(not(feature = "minimal"), not(feature = "mainnet")))]
compile_error!(r#"one of "minimal" or "mainnet" must be enabled"#);
