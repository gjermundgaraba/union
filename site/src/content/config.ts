import { defineCollection, z } from "astro:content"

const blogCollection = defineCollection({
  type: "content",
  schema: ({ image }) =>
    z.object({
      layout: z.string().optional(),
      title: z.string(),
      // yyyy-MM-dd
      date: z.date(),
      author: z.string().default("union_build"),
      description: z.string().optional(),
      cover: image().optional(),
      editUrl: z.union([z.string().url(), z.boolean()]).optional().default(true),
      lastUpdated: z.union([z.date(), z.boolean()]).optional(),
      hidden: z.boolean().optional().default(false)
    })
})

export const collections = {
  blog: blogCollection
}
