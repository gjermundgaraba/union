import { browser } from "$app/environment"
import { twMerge } from "tailwind-merge"
import { type ClassValue, clsx } from "clsx"

export const cn = (...inputs: Array<ClassValue>) => twMerge(clsx(inputs))
export function getNumberSuffix(n: number | null): string {
  if (n == null) return ""

  const lastDigit = n % 10
  const lastTwoDigits = n % 100

  switch (lastDigit) {
    case 1:
      if (lastTwoDigits !== 11) return "st"
      break
    case 2:
      if (lastTwoDigits !== 12) return "nd"
      break
    case 3:
      if (lastTwoDigits !== 13) return "rd"
      break
    default:
      break
  }

  return "th"
}

export function isSafari(): boolean {
  if (!browser) {
    return false
  }

  const ua = navigator.userAgent.toLowerCase()
  return ua.indexOf("safari") > -1 && ua.indexOf("chrome") === -1
}

export function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms))
}

export async function detectOS(): Promise<DetectedOS> {
  //@ts-ignore
  if ("userAgentData" in navigator && "getHighEntropyValues" in navigator.userAgentData) {
    try {
      const ua = navigator.userAgentData as any
      const highEntropyValues = await ua.getHighEntropyValues(["platform", "platformVersion"])
      const platform = highEntropyValues.platform.toLowerCase()

      if (platform.includes("win")) {
        return "Windows"
      }
      if (platform.includes("mac")) {
        return "macOS"
      }
      if (platform.includes("linux")) {
        return "Linux"
      }
    } catch (error) {
      console.error("Error getting high entropy values:", error)
    }
  }

  const userAgent = navigator.userAgent.toLowerCase()

  if (userAgent.includes("win")) {
    return "Windows"
  }
  if (userAgent.includes("mac")) {
    return "macOS"
  }
  if (userAgent.includes("linux") || userAgent.includes("x11")) {
    return "Linux"
  }

  return "Unknown"
}

export type DetectedOS = "Linux" | "macOS" | "Windows" | "Unknown"

export function timeToMs(timeStr: string | null): number {
  if (!timeStr) return 0
  const [time, milliseconds] = timeStr.split(".")
  const [hours, minutes, seconds] = time.split(":").map(Number)
  return hours * 3600000 + minutes * 60000 + seconds * 1000 + Number(milliseconds || 0)
}

export function msToTimeString(ms: number): string {
  const hours = Math.floor(ms / 3600000)
  const minutes = Math.floor((ms % 3600000) / 60000)
  const seconds = Math.floor((ms % 60000) / 1000)
  const milliseconds = ms % 1000
  return `${hours.toString().padStart(2, "0")}:${minutes.toString().padStart(2, "0")}:${seconds.toString().padStart(2, "0")}.${milliseconds.toString().padStart(3, "0")}`
}

export function formatWaitTime(minutes: number) {
  const hours = Math.floor(minutes / 60)
  const remainingMinutes = Math.round(minutes % 60)

  if (hours === 0) {
    return `${remainingMinutes} minute${remainingMinutes !== 1 ? "s" : ""}`
  }

  if (remainingMinutes === 0) {
    return `${hours} hour${hours !== 1 ? "s" : ""}`
  }

  return `${hours} hour${hours !== 1 ? "s" : ""} and ${remainingMinutes} minute${remainingMinutes !== 1 ? "s" : ""}`
}
