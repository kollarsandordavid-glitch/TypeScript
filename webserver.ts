/**
 * Claude Code Web — Backend Server
 *
 * Single-file backend that:
 *  1. Serves the built React PWA (static files)
 *  2. Exposes a REST API  (/api/*)
 *  3. Runs a WebSocket server (/ws) for real-time agent communication
 *  4. Manages Claude Code subprocesses (one per conversation)
 *  5. Parses the CLI's stream-json output and relays it to the browser
 */

import * as http from 'http'
import * as fs from 'fs'
import * as path from 'path'
import * as url from 'url'
import { spawn } from 'child_process'
import type { ChildProcessWithoutNullStreams } from 'child_process'
import { WebSocketServer, WebSocket } from 'ws'

// ─────────────────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────────────────

const CONFIG = {
  port: Number(process.env.PORT ?? 5000),
  host: '0.0.0.0',
  publicDir: path.join(path.dirname(url.fileURLToPath(import.meta.url)), 'public'),
  /** Kill idle sessions after this many ms of inactivity */
  sessionIdleTimeoutMs: 30 * 60 * 1000,
  /** Heartbeat interval to detect dead WebSocket connections */
  wsHeartbeatIntervalMs: 30_000,
  /** Maximum simultaneous sessions per WebSocket client */
  maxSessionsPerClient: 10,
  claude: {
    entrypoint: 'main.tsx',
    runtime: 'bun',
  },
} as const

const MIME_TYPES: Record<string, string> = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'application/javascript',
  '.mjs': 'application/javascript',
  '.css': 'text/css',
  '.json': 'application/json',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon',
  '.woff': 'font/woff',
  '.woff2': 'font/woff2',
  '.ttf': 'font/ttf',
  '.webmanifest': 'application/manifest+json',
  '.map': 'application/json',
}

// ─────────────────────────────────────────────────────────────────────────────
// Types
// ─────────────────────────────────────────────────────────────────────────────

interface ClientMessage {
  type: 'message' | 'interrupt' | 'resize' | 'ping'
  content?: string
  conversationId?: string
  cwd?: string
  cols?: number
  rows?: number
}

interface ServerMessage {
  type: string
  conversationId?: string
  [key: string]: unknown
}

interface Session {
  id: string
  proc: ChildProcessWithoutNullStreams
  clientWs: WebSocket
  workDir: string
  startedAt: number
  lastActivityAt: number
  /** Accumulation buffer for partial stdout lines */
  stdoutBuf: string
  /** Number of complete turns exchanged */
  turnCount: number
}

interface ConnectedClient {
  ws: WebSocket
  /** Sessions owned by this client */
  sessionIds: Set<string>
  /** Used for heartbeat ping/pong detection */
  isAlive: boolean
  connectedAt: number
}

// ─────────────────────────────────────────────────────────────────────────────
// Session Registry
// ─────────────────────────────────────────────────────────────────────────────

class SessionRegistry {
  private sessions = new Map<string, Session>()
  private idleTimer: ReturnType<typeof setInterval>

  constructor() {
    // Periodically sweep and kill sessions that have been idle too long
    this.idleTimer = setInterval(() => this.sweepIdleSessions(), 60_000)
  }

  get(id: string): Session | undefined {
    return this.sessions.get(id)
  }

  add(session: Session): void {
    this.sessions.set(session.id, session)
    session.clientWs['_client']?.sessionIds.add(session.id)
  }

  remove(id: string): void {
    const sess = this.sessions.get(id)
    if (!sess) return
    sess.clientWs['_client']?.sessionIds.delete(id)
    this.sessions.delete(id)
  }

  isAlive(id: string): boolean {
    const sess = this.sessions.get(id)
    return !!sess && sess.proc.exitCode === null
  }

  touch(id: string): void {
    const sess = this.sessions.get(id)
    if (sess) sess.lastActivityAt = Date.now()
  }

  allForClient(clientWs: WebSocket): Session[] {
    return [...this.sessions.values()].filter(s => s.clientWs === clientWs)
  }

  summary() {
    return [...this.sessions.values()].map(s => ({
      id: s.id,
      workDir: s.workDir,
      startedAt: s.startedAt,
      lastActivityAt: s.lastActivityAt,
      turnCount: s.turnCount,
      alive: s.proc.exitCode === null,
    }))
  }

  private sweepIdleSessions(): void {
    const cutoff = Date.now() - CONFIG.sessionIdleTimeoutMs
    for (const [id, sess] of this.sessions) {
      if (sess.lastActivityAt < cutoff && sess.proc.exitCode === null) {
        log('session', id, `idle timeout — killing process`)
        sess.proc.kill('SIGTERM')
        this.sessions.delete(id)
      }
    }
  }

  destroy(): void {
    clearInterval(this.idleTimer)
    for (const [, sess] of this.sessions) {
      if (sess.proc.exitCode === null) sess.proc.kill('SIGTERM')
    }
    this.sessions.clear()
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// Claude Process Manager
// ─────────────────────────────────────────────────────────────────────────────

/**
 * Spawns a new `bun main.tsx` process in stream-json mode and wires up
 * stdout → WebSocket message relay and stdin ← client message feed.
 */
function spawnClaudeSession(
  convId: string,
  initialPrompt: string,
  clientWs: WebSocket,
  registry: SessionRegistry,
  cwd?: string,
): void {
  const workDir = resolveWorkDir(cwd)
  const apiKey = process.env.ANTHROPIC_API_KEY

  if (!apiKey) {
    send(clientWs, {
      type: 'error',
      conversationId: convId,
      content: 'ANTHROPIC_API_KEY is not set. Add it to your environment variables and restart the server.',
      fatal: true,
    })
    return
  }

  const args = [
    CONFIG.claude.entrypoint,
    '--print',
    '--output-format', 'stream-json',
    '--verbose',
    '--input-format', 'stream-json',
    '--include-partial-messages',
    '--dangerously-skip-permissions',
    '--',
    initialPrompt,
  ]

  log('proc', convId, `spawn: ${CONFIG.claude.runtime} ${args[0]} [${workDir}]`)

  const proc = spawn(CONFIG.claude.runtime, args, {
    cwd: workDir,
    stdio: ['pipe', 'pipe', 'pipe'],
    env: {
      ...process.env,
      TERM: 'dumb',
      NO_COLOR: '1',
      FORCE_COLOR: '0',
      ANTHROPIC_API_KEY: apiKey,
    },
  })

  const session: Session = {
    id: convId,
    proc,
    clientWs,
    workDir,
    startedAt: Date.now(),
    lastActivityAt: Date.now(),
    stdoutBuf: '',
    turnCount: 1,
  }

  registry.add(session)
  send(clientWs, { type: 'session_start', conversationId: convId, workDir })

  // stdout — parse newline-delimited JSON
  proc.stdout.on('data', (chunk: Buffer) => {
    registry.touch(convId)
    session.stdoutBuf += chunk.toString('utf8')
    const lines = session.stdoutBuf.split('\n')
    session.stdoutBuf = lines.pop() ?? ''

    for (const line of lines) {
      const trimmed = line.trim()
      if (!trimmed) continue
      try {
        const msg = JSON.parse(trimmed) as Record<string, unknown>
        const relayed = parseClaudeMessage(msg)
        for (const out of relayed) {
          send(clientWs, { ...out, conversationId: convId })
        }
      } catch {
        // Not JSON — forward as plain text (shouldn't normally happen in stream-json mode)
        send(clientWs, { type: 'text', content: trimmed, conversationId: convId })
      }
    }
  })

  // stderr — log locally, forward to client as non-fatal info
  proc.stderr.on('data', (chunk: Buffer) => {
    const text = chunk.toString('utf8').trim()
    if (!text) return
    log('proc', convId, `stderr: ${text.slice(0, 160)}`)
    // Only forward user-relevant stderr (not internal debug noise)
    if (!text.startsWith('profileCheckpoint') && !text.includes('[DEBUG]')) {
      send(clientWs, { type: 'stderr', content: text, conversationId: convId })
    }
  })

  // process exit
  proc.on('exit', (code, signal) => {
    log('proc', convId, `exited — code=${code} signal=${signal}`)
    registry.remove(convId)
    send(clientWs, { type: 'session_end', conversationId: convId, exitCode: code })
  })

  // spawn error (e.g. bun not found)
  proc.on('error', (err) => {
    log('proc', convId, `spawn error: ${err.message}`)
    registry.remove(convId)
    send(clientWs, { type: 'error', conversationId: convId, content: `Failed to start Claude: ${err.message}`, fatal: true })
  })
}

/**
 * Sends a follow-up user message to an already-running session via stdin.
 * The Claude CLI reads stream-json from stdin so we write a JSON user turn.
 */
function sendTurnToSession(session: Session, content: string): void {
  const payload = JSON.stringify({
    type: 'user',
    message: { role: 'user', content },
  }) + '\n'
  session.proc.stdin.write(payload, 'utf8')
  session.turnCount++
  session.lastActivityAt = Date.now()
  log('proc', session.id, `→ turn ${session.turnCount}: ${content.slice(0, 80)}`)
}

// ─────────────────────────────────────────────────────────────────────────────
// stream-json Message Parser
// ─────────────────────────────────────────────────────────────────────────────

/**
 * Translates a single Claude stream-json message into one or more
 * WebSocket messages for the browser client.
 */
function parseClaudeMessage(msg: Record<string, unknown>): ServerMessage[] {
  const type = msg.type as string
  const out: ServerMessage[] = []

  switch (type) {

    case 'assistant': {
      const message = msg.message as Record<string, unknown> | undefined
      const content = message?.content
      if (!Array.isArray(content)) break
      for (const raw of content) {
        const block = raw as Record<string, unknown>
        switch (block.type) {
          case 'text':
            out.push({ type: 'assistant_text', content: block.text })
            break
          case 'tool_use':
            out.push({
              type: 'tool_call',
              toolId: block.id,
              toolName: block.name,
              input: block.input,
            })
            break
          case 'thinking':
            out.push({ type: 'thinking', content: block.thinking })
            break
        }
      }
      break
    }

    case 'user': {
      // Tool results arrive wrapped as user messages in the conversation history
      const message = msg.message as Record<string, unknown> | undefined
      const content = message?.content
      if (!Array.isArray(content)) break
      for (const raw of content) {
        const block = raw as Record<string, unknown>
        if (block.type !== 'tool_result') continue
        const blockContent = block.content
        const text = Array.isArray(blockContent)
          ? (blockContent as Array<Record<string, unknown>>).map(c => String(c.text ?? '')).join('\n')
          : String(blockContent ?? '')
        out.push({
          type: 'tool_result',
          toolId: block.tool_use_id,
          content: text,
          isError: block.is_error ?? false,
        })
      }
      break
    }

    case 'stream_event': {
      // Real-time token streaming
      const event = msg.event as Record<string, unknown> | undefined
      if (event?.type === 'content_block_delta') {
        const delta = event.delta as Record<string, unknown> | undefined
        if (delta?.type === 'text_delta') {
          out.push({ type: 'delta', content: delta.text })
        } else if (delta?.type === 'thinking_delta') {
          out.push({ type: 'thinking_delta', content: delta.thinking })
        }
      }
      break
    }

    case 'system':
      out.push({ type: 'system', subtype: msg.subtype, content: msg.message })
      break

    case 'result':
      out.push({
        type: 'result',
        result: msg.result,
        isError: msg.is_error,
        costUsd: msg.total_cost_usd,
        durationMs: msg.duration_ms,
        turns: msg.num_turns,
        usage: msg.usage,
      })
      break

    case 'permission_request':
      out.push({ type: 'permission_request', data: msg })
      break

    default:
      // Forward unknown message types transparently so nothing is lost
      out.push({ type: 'raw', rawType: type, data: msg })
      break
  }

  return out
}

// ─────────────────────────────────────────────────────────────────────────────
// WebSocket Server
// ─────────────────────────────────────────────────────────────────────────────

function createWebSocketServer(
  httpServer: http.Server,
  registry: SessionRegistry,
): WebSocketServer {
  const wss = new WebSocketServer({ server: httpServer, path: '/ws' })
  const clients = new Map<WebSocket, ConnectedClient>()

  // Heartbeat — drops dead connections
  const heartbeat = setInterval(() => {
    for (const [ws, client] of clients) {
      if (!client.isAlive) {
        log('ws', '-', 'client did not respond to ping — terminating')
        ws.terminate()
        clients.delete(ws)
        continue
      }
      client.isAlive = false
      ws.ping()
    }
  }, CONFIG.wsHeartbeatIntervalMs)

  wss.on('close', () => clearInterval(heartbeat))

  wss.on('connection', (ws, req) => {
    const remoteAddr = req.socket.remoteAddress ?? '?'
    log('ws', '-', `connected from ${remoteAddr}`)

    const client: ConnectedClient = {
      ws,
      sessionIds: new Set(),
      isAlive: true,
      connectedAt: Date.now(),
    }
    clients.set(ws, client)

    // Attach client reference for registry lookups
    ;(ws as Record<string, unknown>)['_client'] = client

    // Send a welcome handshake so the browser knows it's connected
    send(ws, {
      type: 'connected',
      serverTime: Date.now(),
      hasApiKey: !!process.env.ANTHROPIC_API_KEY,
    })

    ws.on('pong', () => { client.isAlive = true })

    ws.on('message', (raw) => {
      let data: ClientMessage
      try { data = JSON.parse(raw.toString()) as ClientMessage }
      catch { return }

      switch (data.type) {
        case 'ping':
          send(ws, { type: 'pong' })
          break

        case 'message': {
          if (!data.content?.trim()) break
          const convId = data.conversationId ?? crypto.randomUUID()

          if (registry.isAlive(convId)) {
            // Existing session — send follow-up turn
            const sess = registry.get(convId)!
            sendTurnToSession(sess, data.content)
          } else {
            // New session
            if (client.sessionIds.size >= CONFIG.maxSessionsPerClient) {
              send(ws, {
                type: 'error',
                conversationId: convId,
                content: `Maximum of ${CONFIG.maxSessionsPerClient} simultaneous sessions reached.`,
              })
              break
            }
            spawnClaudeSession(convId, data.content, ws, registry, data.cwd)
          }
          break
        }

        case 'interrupt': {
          const sess = registry.get(data.conversationId ?? '')
          if (sess && sess.proc.exitCode === null) {
            sess.proc.kill('SIGINT')
            log('proc', sess.id, 'interrupted by client')
          }
          break
        }
      }
    })

    ws.on('close', (code, reason) => {
      log('ws', '-', `disconnected (${code} ${reason.toString().slice(0, 40)})`)
      clients.delete(ws)
      // Kill all sessions owned by this client
      for (const sess of registry.allForClient(ws)) {
        if (sess.proc.exitCode === null) {
          sess.proc.kill('SIGTERM')
        }
        registry.remove(sess.id)
      }
    })

    ws.on('error', (err) => {
      log('ws', '-', `error: ${err.message}`)
    })
  })

  return wss
}

// ─────────────────────────────────────────────────────────────────────────────
// HTTP Server — Static files + REST API
// ─────────────────────────────────────────────────────────────────────────────

function createHttpServer(registry: SessionRegistry): http.Server {
  return http.createServer((req, res) => {
    const parsed = new URL(req.url ?? '/', `http://${req.headers.host}`)
    const pathname = parsed.pathname

    // Security: prevent path traversal
    const safePath = path.normalize(pathname).replace(/^(\.\.[/\\])+/, '')

    // ── REST API ──────────────────────────────────────────────────────────
    if (pathname.startsWith('/api/')) {
      return handleApi(req, res, pathname, registry)
    }

    // ── Static file serving with SPA fallback ────────────────────────────
    setSecurityHeaders(res)
    res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate')

    let filePath = path.join(CONFIG.publicDir, safePath === '/' || safePath === '' ? 'index.html' : safePath)

    // Directory → try index.html inside it
    if (fs.existsSync(filePath) && fs.statSync(filePath).isDirectory()) {
      filePath = path.join(filePath, 'index.html')
    }

    // File not found → SPA fallback
    if (!fs.existsSync(filePath)) {
      filePath = path.join(CONFIG.publicDir, 'index.html')
    }

    const ext = path.extname(filePath)
    const contentType = MIME_TYPES[ext] ?? 'application/octet-stream'

    // Long-lived cache for hashed assets
    if (/\/assets\//.test(pathname)) {
      res.setHeader('Cache-Control', 'public, max-age=31536000, immutable')
    }

    try {
      const data = fs.readFileSync(filePath)
      res.writeHead(200, { 'Content-Type': contentType })
      res.end(data)
    } catch {
      res.writeHead(404, { 'Content-Type': 'text/plain' })
      res.end('Not Found')
    }
  })
}

function handleApi(
  req: http.IncomingMessage,
  res: http.ServerResponse,
  pathname: string,
  registry: SessionRegistry,
): void {
  res.setHeader('Content-Type', 'application/json')
  res.setHeader('Access-Control-Allow-Origin', '*')
  setSecurityHeaders(res)

  if (pathname === '/api/health') {
    res.writeHead(200)
    res.end(JSON.stringify({
      status: 'ok',
      uptime: process.uptime(),
      sessions: registry.summary().length,
      hasApiKey: !!process.env.ANTHROPIC_API_KEY,
      timestamp: new Date().toISOString(),
    }))
    return
  }

  if (pathname === '/api/sessions') {
    res.writeHead(200)
    res.end(JSON.stringify({ sessions: registry.summary() }))
    return
  }

  res.writeHead(404)
  res.end(JSON.stringify({ error: 'Not found' }))
}

function setSecurityHeaders(res: http.ServerResponse): void {
  res.setHeader('X-Content-Type-Options', 'nosniff')
  res.setHeader('X-Frame-Options', 'DENY')
  res.setHeader('Referrer-Policy', 'strict-origin-when-cross-origin')
}

// ─────────────────────────────────────────────────────────────────────────────
// Utilities
// ─────────────────────────────────────────────────────────────────────────────

function send(ws: WebSocket, data: ServerMessage): void {
  if (ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify(data))
  }
}

function resolveWorkDir(cwd?: string): string {
  if (!cwd) return process.cwd()
  try {
    const resolved = path.resolve(cwd)
    if (fs.existsSync(resolved) && fs.statSync(resolved).isDirectory()) return resolved
  } catch { /* fall through */ }
  return process.cwd()
}

function log(area: string, id: string, msg: string): void {
  const time = new Date().toISOString().slice(11, 23)
  const label = `[${time}][${area}${id !== '-' ? ':' + id.slice(0, 8) : ''}]`
  console.log(`${label} ${msg}`)
}

// ─────────────────────────────────────────────────────────────────────────────
// Graceful Shutdown
// ─────────────────────────────────────────────────────────────────────────────

function registerShutdown(server: http.Server, registry: SessionRegistry): void {
  const shutdown = (signal: string) => {
    log('server', '-', `received ${signal} — shutting down`)
    registry.destroy()
    server.close(() => {
      log('server', '-', 'HTTP server closed')
      process.exit(0)
    })
    // Force-exit if graceful shutdown takes too long
    setTimeout(() => process.exit(1), 5_000)
  }
  process.on('SIGTERM', () => shutdown('SIGTERM'))
  process.on('SIGINT', () => shutdown('SIGINT'))
}

// ─────────────────────────────────────────────────────────────────────────────
// Bootstrap
// ─────────────────────────────────────────────────────────────────────────────

function start(): void {
  if (!fs.existsSync(CONFIG.publicDir)) {
    console.error(`[error] Public directory not found: ${CONFIG.publicDir}`)
    console.error(`        Run "cd frontend && npm run build" first.`)
    process.exit(1)
  }

  const registry = new SessionRegistry()
  const httpServer = createHttpServer(registry)
  createWebSocketServer(httpServer, registry)
  registerShutdown(httpServer, registry)

  httpServer.listen(CONFIG.port, CONFIG.host, () => {
    console.log(`\n  Claude Code Web`)
    console.log(`  ───────────────────────────────────`)
    console.log(`  🌐  http://${CONFIG.host}:${CONFIG.port}`)
    console.log(`  🔌  ws://${CONFIG.host}:${CONFIG.port}/ws`)
    console.log(`  📡  REST API: /api/health  /api/sessions`)
    console.log(`  🤖  Claude runtime: ${CONFIG.claude.runtime} ${CONFIG.claude.entrypoint}`)
    console.log(`  🔑  API key: ${process.env.ANTHROPIC_API_KEY ? '✓ set' : '✗ NOT SET — add ANTHROPIC_API_KEY'}`)
    console.log(`  ───────────────────────────────────\n`)
  })
}

start()
