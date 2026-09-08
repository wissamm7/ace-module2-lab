/*
 * Copyright (c) 2014-2026 Bjoern Kimminich & the OWASP Juice Shop contributors.
 * SPDX-License-Identifier: MIT
 */

import dns from 'node:dns'
import fs from 'node:fs'
import net from 'node:net'
import { Readable } from 'node:stream'
import { finished } from 'node:stream/promises'
import { type Request, type Response, type NextFunction } from 'express'

import * as security from '../lib/insecurity'
import { UserModel } from '../models/user'
import * as utils from '../lib/utils'
import logger from '../lib/logger'

function isPrivateOrReservedIPv4 (ip: string): boolean {
  const parts = ip.split('.').map(p => parseInt(p, 10))
  if (parts.length !== 4 || parts.some(p => isNaN(p) || p < 0 || p > 255)) {
    return true
  }
  const [a, b, c] = parts

  // 0.0.0.0/8
  if (a === 0) return true
  // 10.0.0.0/8
  if (a === 10) return true
  // 100.64.0.0/10
  if (a === 100 && b >= 64 && b <= 127) return true
  // 127.0.0.0/8
  if (a === 127) return true
  // 169.254.0.0/16
  if (a === 169 && b === 254) return true
  // 172.16.0.0/12
  if (a === 172 && b >= 16 && b <= 31) return true
  // 192.0.0.0/24
  if (a === 192 && b === 0 && c === 0) return true
  // 192.0.2.0/24
  if (a === 192 && b === 0 && c === 2) return true
  // 192.168.0.0/16
  if (a === 192 && b === 168) return true
  // 198.18.0.0/15
  if (a === 198 && (b === 18 || b === 19)) return true
  // 198.51.100.0/24
  if (a === 198 && b === 51 && c === 100) return true
  // 203.0.113.0/24
  if (a === 203 && b === 0 && c === 113) return true
  // 224.0.0.0/4
  if (a >= 224 && a <= 239) return true
  // 240.0.0.0/4
  if (a >= 240) return true

  return false
}

function parseIPv6 (ip: string): number[] | null {
  let cleanIp = ip.toLowerCase()
  if (cleanIp.includes('.')) {
    const lastColon = cleanIp.lastIndexOf(':')
    if (lastColon === -1) return null
    const ipv4Part = cleanIp.substring(lastColon + 1)
    if (!net.isIPv4(ipv4Part)) return null
    const parts = ipv4Part.split('.').map(p => parseInt(p, 10))
    const hex1 = ((parts[0] << 8) | parts[1]).toString(16)
    const hex2 = ((parts[2] << 8) | parts[3]).toString(16)
    cleanIp = cleanIp.substring(0, lastColon + 1) + hex1 + ':' + hex2
  }

  const parts = cleanIp.split('::')
  if (parts.length > 2) return null

  let head: string[] = []
  let tail: string[] = []

  if (parts.length === 1) {
    head = parts[0].split(':')
    if (head.length !== 8) return null
  } else {
    head = parts[0] ? parts[0].split(':') : []
    tail = parts[1] ? parts[1].split(':') : []
    const missing = 8 - (head.length + tail.length)
    if (missing < 1) return null
  }

  const fullParts: number[] = []
  for (const h of head) {
    const val = parseInt(h, 16)
    if (isNaN(val) || val < 0 || val > 0xffff) return null
    fullParts.push(val)
  }
  const numZeros = 8 - head.length - tail.length
  for (let i = 0; i < numZeros; i++) {
    fullParts.push(0)
  }
  for (const t of tail) {
    const val = parseInt(t, 16)
    if (isNaN(val) || val < 0 || val > 0xffff) return null
    fullParts.push(val)
  }

  return fullParts
}

function isPrivateOrReservedIPv6 (ip: string): boolean {
  const words = parseIPv6(ip)
  if (!words) return true

  const [w0, w1, w2, w3, w4, w5, w6, w7] = words

  // Loopback ::1
  if (w0 === 0 && w1 === 0 && w2 === 0 && w3 === 0 && w4 === 0 && w5 === 0 && w6 === 0 && w7 === 1) {
    return true
  }

  // Unspecified ::
  if (w0 === 0 && w1 === 0 && w2 === 0 && w3 === 0 && w4 === 0 && w5 === 0 && w6 === 0 && w7 === 0) {
    return true
  }

  // IPv4-mapped IPv6 (::ffff:x.x.x.x)
  if (w0 === 0 && w1 === 0 && w2 === 0 && w3 === 0 && w4 === 0 && w5 === 0xffff) {
    const v4 = `${(w6 >> 8) & 0xff}.${w6 & 0xff}.${(w7 >> 8) & 0xff}.${w7 & 0xff}`
    return isPrivateOrReservedIPv4(v4)
  }

  // IPv4-translated (::ffff:0:x.x.x.x)
  if (w0 === 0 && w1 === 0 && w2 === 0 && w3 === 0 && w4 === 0xffff && w5 === 0) {
    const v4 = `${(w6 >> 8) & 0xff}.${w6 & 0xff}.${(w7 >> 8) & 0xff}.${w7 & 0xff}`
    return isPrivateOrReservedIPv4(v4)
  }

  // NAT64 / Well-known prefix (64:ff9b::/96)
  if (w0 === 0x64 && w1 === 0xff9b && w2 === 0 && w3 === 0 && w4 === 0 && w5 === 0) {
    const v4 = `${(w6 >> 8) & 0xff}.${w6 & 0xff}.${(w7 >> 8) & 0xff}.${w7 & 0xff}`
    return isPrivateOrReservedIPv4(v4)
  }

  // Unique Local Address (fc00::/7)
  if ((w0 & 0xfe00) === 0xfc00) {
    return true
  }

  // Link-Local (fe80::/10)
  if ((w0 & 0xffc0) === 0xfe80) {
    return true
  }

  // Site-Local deprecated (fec0::/10)
  if ((w0 & 0xffc0) === 0xfec0) {
    return true
  }

  // Multicast (ff00::/8)
  if ((w0 & 0xff00) === 0xff00) {
    return true
  }

  // Documentation (2001:db8::/32)
  if (w0 === 0x2001 && w1 === 0xdb8) {
    return true
  }

  // Discard prefix (100::/64)
  if (w0 === 0x100 && w1 === 0 && w2 === 0 && w3 === 0) {
    return true
  }

  // Benchmarking (2001:2::/48)
  if (w0 === 0x2001 && w1 === 0x2 && w2 === 0) {
    return true
  }

  // ORCHIDv2 (2001:20::/28)
  if (w0 === 0x2001 && (w1 & 0xfff0) === 0x20) {
    return true
  }

  return false
}

async function isSafeUrl (urlString: string): Promise<boolean> {
  let parsedUrl: URL
  try {
    parsedUrl = new URL(urlString)
  } catch {
    return false
  }

  if (parsedUrl.protocol !== 'http:' && parsedUrl.protocol !== 'https:') {
    return false
  }

  const rawHostname = parsedUrl.hostname.toLowerCase()
  const hostname = rawHostname.replace(/^\[|\]$/g, '')

  if (!hostname || hostname === 'localhost' || hostname.endsWith('.localhost') || hostname.endsWith('.local') || hostname.endsWith('.internal') || hostname.endsWith('.lan') || hostname.endsWith('.onion')) {
    return false
  }

  if (net.isIPv4(hostname)) {
    return !isPrivateOrReservedIPv4(hostname)
  }

  if (net.isIPv6(hostname)) {
    return !isPrivateOrReservedIPv6(hostname)
  }

  try {
    const addresses = await dns.promises.lookup(hostname, { all: true })
    if (!addresses || addresses.length === 0) {
      return false
    }
    for (const addr of addresses) {
      if (addr.family === 4 && isPrivateOrReservedIPv4(addr.address)) {
        return false
      }
      if (addr.family === 6 && isPrivateOrReservedIPv6(addr.address)) {
        return false
      }
    }
  } catch {
    return false
  }

  return true
}

async function fetchSafeImage (initialUrl: string, maxRedirects = 5): Promise<Response> {
  let currentUrl = initialUrl
  for (let i = 0; i <= maxRedirects; i++) {
    if (!await isSafeUrl(currentUrl)) {
      throw new Error('Disallowed or unsafe image URL')
    }
    const response = await fetch(currentUrl, { redirect: 'manual' })
    if (response.status >= 300 && response.status < 400) {
      const location = response.headers.get('location')
      if (!location) {
        throw new Error('Redirect without location header')
      }
      currentUrl = new URL(location, currentUrl).toString()
      continue
    }
    return response
  }
  throw new Error('Too many redirects')
}

export function profileImageUrlUpload () {
  return async (req: Request, res: Response, next: NextFunction) => {
    if (req.body.imageUrl !== undefined) {
      const url = req.body.imageUrl
      if (typeof url === 'string' && url.match(/(.)*solve\/challenges\/server-side(.)*/) !== null) req.app.locals.abused_ssrf_bug = true
      const loggedInUser = security.authenticatedUsers.get(req.cookies.token)
      if (loggedInUser) {
        if (typeof url !== 'string' || !await isSafeUrl(url)) {
          res.status(400)
          next(new Error('Invalid or disallowed image URL'))
          return
        }
        try {
          const response = await fetchSafeImage(url)
          if (!response.ok || !response.body) {
            throw new Error('url returned a non-OK status code or an empty body')
          }
          const ext = ['jpg', 'jpeg', 'png', 'svg', 'gif'].includes(url.split('.').slice(-1)[0].toLowerCase()) ? url.split('.').slice(-1)[0].toLowerCase() : 'jpg'
          const fileStream = fs.createWriteStream(`frontend/dist/frontend/assets/public/images/uploads/${loggedInUser.data.id}.${ext}`, { flags: 'w' })
          await finished(Readable.fromWeb(response.body as any).pipe(fileStream))
          const user = await UserModel.findByPk(loggedInUser.data.id)
          await user?.update({ profileImage: `/assets/public/images/uploads/${loggedInUser.data.id}.${ext}` })
        } catch (error) {
          try {
            const user = await UserModel.findByPk(loggedInUser.data.id)
            await user?.update({ profileImage: url })
            logger.warn(`Error retrieving user profile image: ${utils.getErrorMessage(error)}; using image link directly`)
          } catch (error) {
            next(error)
            return
          }
        }
      } else {
        next(new Error('Blocked illegal activity by ' + req.socket.remoteAddress))
        return
      }
    }
    res.location(process.env.BASE_PATH + '/profile')
    res.redirect(process.env.BASE_PATH + '/profile')
  }
}
