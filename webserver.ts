/**
 * Claude Code Web — Backend Server
 *
 * Single-file backend:
 *  1. Serves the built React PWA (static files)
 *  2. REST API  (/api/*)
 *  3. WebSocket (/ws) — real-time agent communication
 *  4. Agentic loop — OpenRouter LLM + full tool set (Bash, Read, Write, Edit, Glob, Grep)
 *  5. Session registry — lifecycle, idle timeout, interrupt support
 */

import * as http from 'http'
import * as fs from 'fs'
import * as path from 'path'
import * as url from 'url'
import * as child_process from 'child_process'
import { WebSocketServer, WebSocket } from 'ws'
import OpenAI from 'openai'

// ─────────────────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────────────────

const CONFIG = {
  port: Number(process.env.PORT ?? 5000),
  host: '0.0.0.0',
  publicDir: path.join(path.dirname(url.fileURLToPath(import.meta.url)), 'public'),
  sessionIdleTimeoutMs: 30 * 60 * 1000,
  wsHeartbeatIntervalMs: 30_000,
  maxSessionsPerClient: 10,
  model: 'minimax/minimax-m2.5:free',
  openrouter: {
    baseURL: 'https://openrouter.ai/api/v1',
    apiKeyEnv: 'OPENROUTER_API_KEY',
  },
  bash: {
    defaultTimeoutMs: 30_000,
    maxOutputBytes: 50_000,
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
  '.webmanifest': 'application/manifest+json',
  '.map': 'application/json',
}

// ─────────────────────────────────────────────────────────────────────────────
// OpenRouter client
// ─────────────────────────────────────────────────────────────────────────────

function createClient(): OpenAI | null {
  const apiKey = process.env[CONFIG.openrouter.apiKeyEnv]
  if (!apiKey) return null
  return new OpenAI({ baseURL: CONFIG.openrouter.baseURL, apiKey })
}

// ─────────────────────────────────────────────────────────────────────────────
// Types
// ─────────────────────────────────────────────────────────────────────────────

// Extended message type that preserves reasoning_details across turns
type ConversationMessage =
  | { role: 'system'; content: string }
  | { role: 'user'; content: string }
  | { role: 'assistant'; content: string | null; tool_calls?: OpenAI.Chat.ChatCompletionMessageToolCall[]; reasoning_details?: unknown }
  | { role: 'tool'; tool_call_id: string; content: string }

interface Session {
  id: string
  clientWs: WebSocket
  workDir: string
  messages: ConversationMessage[]
  startedAt: number
  lastActivityAt: number
  turnCount: number
  abort?: AbortController
  running: boolean
}

interface ConnectedClient {
  ws: WebSocket
  sessionIds: Set<string>
  isAlive: boolean
  connectedAt: number
}

interface ClientMessage {
  type: 'message' | 'interrupt' | 'ping'
  content?: string
  conversationId?: string
  cwd?: string
}

interface ServerMessage {
  type: string
  conversationId?: string
  [key: string]: unknown
}

// ─────────────────────────────────────────────────────────────────────────────
// Tool Definitions (OpenAI function-calling format)
// ─────────────────────────────────────────────────────────────────────────────

const TOOLS: OpenAI.Chat.ChatCompletionTool[] = [
  {
    type: 'function',
    function: {
      name: 'bash',
      description: 'Execute a shell command and return stdout + stderr. Use for running code, installing packages, git operations, etc.',
      parameters: {
        type: 'object',
        properties: {
          command: { type: 'string', description: 'The shell command to execute.' },
          timeout: { type: 'number', description: 'Timeout in seconds (default 30, max 120).' },
        },
        required: ['command'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'read_file',
      description: 'Read the contents of a file. Returns the file text.',
      parameters: {
        type: 'object',
        properties: {
          path: { type: 'string', description: 'Absolute or relative file path.' },
          offset: { type: 'number', description: 'Line number to start reading from (1-indexed).' },
          limit: { type: 'number', description: 'Max number of lines to read.' },
        },
        required: ['path'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'write_file',
      description: 'Write content to a file, creating it or overwriting it entirely.',
      parameters: {
        type: 'object',
        properties: {
          path: { type: 'string', description: 'File path to write to.' },
          content: { type: 'string', description: 'Full file content.' },
        },
        required: ['path', 'content'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'edit_file',
      description: 'Replace an exact string in a file with new content. Fails if old_string is not found or is not unique.',
      parameters: {
        type: 'object',
        properties: {
          path: { type: 'string', description: 'File path to edit.' },
          old_string: { type: 'string', description: 'Exact string to replace (must be unique in the file).' },
          new_string: { type: 'string', description: 'Replacement string.' },
        },
        required: ['path', 'old_string', 'new_string'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'glob',
      description: 'Find files matching a glob pattern. Returns a list of matching file paths.',
      parameters: {
        type: 'object',
        properties: {
          pattern: { type: 'string', description: 'Glob pattern, e.g. "**/*.ts" or "src/**/*.css".' },
          cwd: { type: 'string', description: 'Directory to search from (defaults to working directory).' },
        },
        required: ['pattern'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'grep',
      description: 'Search for a pattern in files. Returns matching lines with file names and line numbers.',
      parameters: {
        type: 'object',
        properties: {
          pattern: { type: 'string', description: 'Regex or literal search pattern.' },
          path: { type: 'string', description: 'File or directory to search in.' },
          glob: { type: 'string', description: 'Glob filter for files, e.g. "*.ts".' },
          case_insensitive: { type: 'boolean', description: 'Case-insensitive search.' },
        },
        required: ['pattern'],
      },
    },
  },
]

// ─────────────────────────────────────────────────────────────────────────────
// Tool Executor
// ─────────────────────────────────────────────────────────────────────────────

async function executeTool(
  name: string,
  input: Record<string, unknown>,
  workDir: string,
): Promise<{ output: string; isError: boolean }> {
  try {
    switch (name) {
      case 'bash': {
        const command = String(input.command ?? '')
        const timeout = Math.min(Number(input.timeout ?? 30), 120) * 1000
        const result = await runShell(command, workDir, timeout)
        return { output: result, isError: false }
      }

      case 'read_file': {
        const filePath = resolvePath(String(input.path ?? ''), workDir)
        if (!fs.existsSync(filePath)) return { output: `File not found: ${filePath}`, isError: true }
        const raw = fs.readFileSync(filePath, 'utf8')
        const lines = raw.split('\n')
        const offset = Number(input.offset ?? 1) - 1
        const limit = Number(input.limit ?? lines.length)
        const sliced = lines.slice(Math.max(0, offset), offset + limit)
        return { output: sliced.join('\n'), isError: false }
      }

      case 'write_file': {
        const filePath = resolvePath(String(input.path ?? ''), workDir)
        fs.mkdirSync(path.dirname(filePath), { recursive: true })
        fs.writeFileSync(filePath, String(input.content ?? ''), 'utf8')
        return { output: `Wrote ${filePath}`, isError: false }
      }

      case 'edit_file': {
        const filePath = resolvePath(String(input.path ?? ''), workDir)
        if (!fs.existsSync(filePath)) return { output: `File not found: ${filePath}`, isError: true }
        const content = fs.readFileSync(filePath, 'utf8')
        const oldStr = String(input.old_string ?? '')
        const newStr = String(input.new_string ?? '')
        const count = content.split(oldStr).length - 1
        if (count === 0) return { output: `String not found in ${filePath}`, isError: true }
        if (count > 1) return { output: `String is not unique in ${filePath} (found ${count} times)`, isError: true }
        fs.writeFileSync(filePath, content.replace(oldStr, newStr), 'utf8')
        return { output: `Edited ${filePath}`, isError: false }
      }

      case 'glob': {
        const pattern = String(input.pattern ?? '**/*')
        const searchDir = input.cwd ? resolvePath(String(input.cwd), workDir) : workDir
        const results = await runShell(`find . -path "${pattern.replace(/\*\*/g, '*').replace(/\*/g, '*')}" 2>/dev/null || true`, searchDir, 10_000)
        // Use a proper glob via shell
        const globResult = await runShell(
          `node -e "const g=require('glob');g.sync(process.argv[1],{cwd:process.argv[2]}).forEach(f=>console.log(f))" ${JSON.stringify(pattern)} ${JSON.stringify(searchDir)} 2>/dev/null || find . -name "*.${pattern.split('.').pop()}" 2>/dev/null | head -200`,
          workDir,
          10_000,
        )
        return { output: globResult || results, isError: false }
      }

      case 'grep': {
        const pattern = String(input.pattern ?? '')
        const target = input.path ? resolvePath(String(input.path), workDir) : workDir
        const glob = input.glob ? `--include="${input.glob}"` : ''
        const flags = input.case_insensitive ? '-ri' : '-rn'
        const cmd = `grep ${flags} ${glob} -E ${JSON.stringify(pattern)} ${JSON.stringify(target)} 2>/dev/null | head -100`
        const result = await runShell(cmd, workDir, 15_000)
        return { output: result || '(no matches)', isError: false }
      }

      default:
        return { output: `Unknown tool: ${name}`, isError: true }
    }
  } catch (err) {
    return { output: String(err), isError: true }
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// Agentic Loop
// ─────────────────────────────────────────────────────────────────────────────

async function runAgentLoop(session: Session, ws: WebSocket): Promise<void> {
  const client = createClient()
  if (!client) {
    send(ws, { type: 'error', conversationId: session.id, content: `${CONFIG.openrouter.apiKeyEnv} is not set.`, fatal: true })
    return
  }

  session.running = true
  session.abort = new AbortController()

  try {
    while (session.running) {
      const requestMessages = session.messages as OpenAI.Chat.ChatCompletionMessageParam[]

      // ── API call with streaming ──────────────────────────────────────────
      let stream: AsyncIterable<OpenAI.Chat.Completions.ChatCompletionChunk>
      try {
        stream = await client.chat.completions.create(
          {
            model: CONFIG.model,
            messages: requestMessages,
            tools: TOOLS,
            tool_choice: 'auto',
            stream: true,
            // @ts-expect-error — OpenRouter reasoning extension
            reasoning: { enabled: true },
          },
          { signal: session.abort.signal },
        )
      } catch (err: unknown) {
        const msg = err instanceof Error ? err.message : String(err)
        if (msg.includes('aborted')) {
          send(ws, { type: 'interrupted', conversationId: session.id })
        } else {
          send(ws, { type: 'error', conversationId: session.id, content: `API error: ${msg}` })
        }
        break
      }

      // ── Accumulate streaming response ────────────────────────────────────
      let assistantText = ''
      let finishReason: string | null = null
      const toolCallAccum: Record<number, {
        id: string; name: string; arguments: string
      }> = {}
      let reasoningDetails: unknown = undefined

      for await (const chunk of stream) {
        const delta = chunk.choices[0]?.delta as Record<string, unknown> | undefined
        finishReason = chunk.choices[0]?.finish_reason ?? finishReason

        if (!delta) continue

        // Text token
        if (typeof delta.content === 'string' && delta.content) {
          assistantText += delta.content
          send(ws, { type: 'delta', content: delta.content, conversationId: session.id })
        }

        // Reasoning delta (OpenRouter extension)
        if (delta.reasoning && typeof delta.reasoning === 'string') {
          send(ws, { type: 'thinking_delta', content: delta.reasoning, conversationId: session.id })
        }

        // Preserve reasoning_details (for multi-turn)
        if (delta.reasoning_details !== undefined) {
          reasoningDetails = delta.reasoning_details
        }

        // Tool call deltas — accumulate by index
        const toolCallDeltas = delta.tool_calls as Array<{
          index: number; id?: string
          function?: { name?: string; arguments?: string }
        }> | undefined

        if (toolCallDeltas) {
          for (const tc of toolCallDeltas) {
            const idx = tc.index
            if (!toolCallAccum[idx]) {
              toolCallAccum[idx] = { id: '', name: '', arguments: '' }
            }
            if (tc.id) toolCallAccum[idx].id = tc.id
            if (tc.function?.name) toolCallAccum[idx].name = tc.function.name
            if (tc.function?.arguments) toolCallAccum[idx].arguments += tc.function.arguments
          }
        }
      }

      // ── Build tool calls array ───────────────────────────────────────────
      const toolCalls: OpenAI.Chat.ChatCompletionMessageToolCall[] = Object.values(toolCallAccum).map(tc => ({
        id: tc.id,
        type: 'function' as const,
        function: { name: tc.name, arguments: tc.arguments },
      }))

      // ── Add assistant turn to history (preserving reasoning_details) ─────
      const assistantMsg: ConversationMessage = {
        role: 'assistant',
        content: assistantText || null,
        ...(toolCalls.length > 0 && { tool_calls: toolCalls }),
        ...(reasoningDetails !== undefined && { reasoning_details: reasoningDetails }),
      }
      session.messages.push(assistantMsg)

      // If assistant produced text and NO tool calls — send a 'done' marker
      if (assistantText && toolCalls.length === 0) {
        send(ws, { type: 'done', conversationId: session.id })
      }

      // ── No tool calls → conversation turn complete ───────────────────────
      if (toolCalls.length === 0 || finishReason === 'stop') {
        break
      }

      // ── Execute tool calls ───────────────────────────────────────────────
      for (const tc of toolCalls) {
        let input: Record<string, unknown> = {}
        try { input = JSON.parse(tc.function.arguments) } catch { /* leave empty */ }

        // Notify client about the tool call
        send(ws, {
          type: 'tool_call',
          conversationId: session.id,
          toolId: tc.id,
          toolName: tc.function.name,
          input,
        })

        // Execute
        const { output, isError } = await executeTool(tc.function.name, input, session.workDir)

        // Notify client about the result
        send(ws, {
          type: 'tool_result',
          conversationId: session.id,
          toolId: tc.id,
          toolName: tc.function.name,
          content: output.slice(0, CONFIG.bash.maxOutputBytes),
          isError,
        })

        // Add tool result to history
        session.messages.push({
          role: 'tool',
          tool_call_id: tc.id,
          content: output.slice(0, CONFIG.bash.maxOutputBytes),
        })
      }

      // Continue the loop — the model will see the tool results and respond
    }
  } finally {
    session.running = false
    session.abort = undefined
    session.lastActivityAt = Date.now()
    send(ws, { type: 'result', conversationId: session.id })
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// Session Registry
// ─────────────────────────────────────────────────────────────────────────────

class SessionRegistry {
  private sessions = new Map<string, Session>()
  private idleTimer: ReturnType<typeof setInterval>

  constructor() {
    this.idleTimer = setInterval(() => this.sweepIdle(), 60_000)
  }

  get(id: string): Session | undefined { return this.sessions.get(id) }

  add(session: Session): void { this.sessions.set(session.id, session) }

  remove(id: string): void { this.sessions.delete(id) }

  isRunning(id: string): boolean {
    const s = this.sessions.get(id)
    return !!s?.running
  }

  exists(id: string): boolean { return this.sessions.has(id) }

  touch(id: string): void {
    const s = this.sessions.get(id)
    if (s) s.lastActivityAt = Date.now()
  }

  allForClient(ws: WebSocket): Session[] {
    return [...this.sessions.values()].filter(s => s.clientWs === ws)
  }

  countForClient(ws: WebSocket): number {
    return this.allForClient(ws).length
  }

  summary() {
    return [...this.sessions.values()].map(s => ({
      id: s.id,
      workDir: s.workDir,
      startedAt: s.startedAt,
      lastActivityAt: s.lastActivityAt,
      turnCount: s.turnCount,
      running: s.running,
      messageCount: s.messages.length,
    }))
  }

  private sweepIdle(): void {
    const cutoff = Date.now() - CONFIG.sessionIdleTimeoutMs
    for (const [id, sess] of this.sessions) {
      if (!sess.running && sess.lastActivityAt < cutoff) {
        log('session', id, 'idle timeout — removed')
        this.sessions.delete(id)
      }
    }
  }

  destroy(): void {
    clearInterval(this.idleTimer)
    for (const [, sess] of this.sessions) {
      if (sess.running) sess.abort?.abort()
    }
    this.sessions.clear()
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// WebSocket Server
// ─────────────────────────────────────────────────────────────────────────────

function createWebSocketServer(httpServer: http.Server, registry: SessionRegistry): WebSocketServer {
  const wss = new WebSocketServer({ server: httpServer, path: '/ws' })
  const clients = new Map<WebSocket, ConnectedClient>()

  const heartbeat = setInterval(() => {
    for (const [ws, client] of clients) {
      if (!client.isAlive) { ws.terminate(); clients.delete(ws); continue }
      client.isAlive = false
      ws.ping()
    }
  }, CONFIG.wsHeartbeatIntervalMs)

  wss.on('close', () => clearInterval(heartbeat))

  wss.on('connection', (ws, req) => {
    const addr = req.socket.remoteAddress ?? '?'
    log('ws', '-', `connected from ${addr}`)

    const client: ConnectedClient = { ws, sessionIds: new Set(), isAlive: true, connectedAt: Date.now() }
    clients.set(ws, client)

    send(ws, {
      type: 'connected',
      serverTime: Date.now(),
      model: CONFIG.model,
      hasApiKey: !!process.env[CONFIG.openrouter.apiKeyEnv],
    })

    ws.on('pong', () => { client.isAlive = true })

    ws.on('message', (raw) => {
      let data: ClientMessage
      try { data = JSON.parse(raw.toString()) as ClientMessage } catch { return }

      switch (data.type) {
        case 'ping':
          send(ws, { type: 'pong' })
          break

        case 'message': {
          if (!data.content?.trim()) break
          const convId = data.conversationId ?? crypto.randomUUID()

          let session = registry.get(convId)

          if (!session) {
            // New conversation
            if (registry.countForClient(ws) >= CONFIG.maxSessionsPerClient) {
              send(ws, { type: 'error', conversationId: convId, content: `Max ${CONFIG.maxSessionsPerClient} simultaneous conversations reached.` })
              break
            }

            session = {
              id: convId,
              clientWs: ws,
              workDir: resolveWorkDir(data.cwd),
              messages: [
                { role: 'system', content: systemPrompt() },
                { role: 'user', content: data.content },
              ],
              startedAt: Date.now(),
              lastActivityAt: Date.now(),
              turnCount: 1,
              running: false,
            }
            registry.add(session)
            client.sessionIds.add(convId)
            log('session', convId, `new — "${data.content.slice(0, 60)}"`)
          } else {
            // Existing conversation — add next user turn
            if (session.running) {
              send(ws, { type: 'error', conversationId: convId, content: 'Session is still processing. Wait or interrupt first.' })
              break
            }
            session.messages.push({ role: 'user', content: data.content })
            session.turnCount++
            registry.touch(convId)
            log('session', convId, `turn ${session.turnCount} — "${data.content.slice(0, 60)}"`)
          }

          // Run the agent loop (non-blocking)
          runAgentLoop(session, ws).catch(err => {
            log('agent', convId, `unhandled error: ${err}`)
            send(ws, { type: 'error', conversationId: convId, content: String(err) })
          })
          break
        }

        case 'interrupt': {
          const sess = registry.get(data.conversationId ?? '')
          if (sess?.running) {
            sess.abort?.abort()
            log('session', sess.id, 'interrupted by client')
          }
          break
        }
      }
    })

    ws.on('close', (code) => {
      log('ws', '-', `disconnected (${code})`)
      clients.delete(ws)
      // Abort all running sessions for this client
      for (const sess of registry.allForClient(ws)) {
        if (sess.running) sess.abort?.abort()
        registry.remove(sess.id)
      }
    })

    ws.on('error', (err) => log('ws', '-', `error: ${err.message}`))
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

    if (pathname.startsWith('/api/')) return handleApi(req, res, pathname, registry)

    setSecurityHeaders(res)
    res.setHeader('Cache-Control', 'no-cache, no-store, must-revalidate')

    const safe = path.normalize(pathname).replace(/^(\.\.[/\\])+/, '')
    let filePath = path.join(CONFIG.publicDir, safe === '/' || safe === '' ? 'index.html' : safe)

    if (fs.existsSync(filePath) && fs.statSync(filePath).isDirectory()) filePath = path.join(filePath, 'index.html')
    if (!fs.existsSync(filePath)) filePath = path.join(CONFIG.publicDir, 'index.html')

    if (/\/assets\//.test(pathname)) res.setHeader('Cache-Control', 'public, max-age=31536000, immutable')

    const contentType = MIME_TYPES[path.extname(filePath)] ?? 'application/octet-stream'
    try {
      res.writeHead(200, { 'Content-Type': contentType })
      res.end(fs.readFileSync(filePath))
    } catch {
      res.writeHead(404, { 'Content-Type': 'text/plain' })
      res.end('Not Found')
    }
  })
}

function handleApi(
  _req: http.IncomingMessage,
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
      model: CONFIG.model,
      sessions: registry.summary().length,
      hasApiKey: !!process.env[CONFIG.openrouter.apiKeyEnv],
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

// ─────────────────────────────────────────────────────────────────────────────
// Utilities
// ─────────────────────────────────────────────────────────────────────────────

function send(ws: WebSocket, data: ServerMessage): void {
  if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(data))
}

function resolveWorkDir(cwd?: string): string {
  if (!cwd) return process.cwd()
  try {
    const r = path.resolve(cwd)
    if (fs.existsSync(r) && fs.statSync(r).isDirectory()) return r
  } catch { /* fall through */ }
  return process.cwd()
}

function resolvePath(filePath: string, workDir: string): string {
  return path.isAbsolute(filePath) ? filePath : path.resolve(workDir, filePath)
}

function runShell(command: string, cwd: string, timeoutMs: number): Promise<string> {
  return new Promise((resolve) => {
    const proc = child_process.spawn('sh', ['-c', command], {
      cwd,
      stdio: ['ignore', 'pipe', 'pipe'],
      env: { ...process.env, TERM: 'dumb', NO_COLOR: '1' },
    })

    let out = ''
    proc.stdout.on('data', (b: Buffer) => { out += b.toString('utf8') })
    proc.stderr.on('data', (b: Buffer) => { out += b.toString('utf8') })

    const timer = setTimeout(() => {
      proc.kill('SIGKILL')
      resolve(out + '\n[timed out]')
    }, timeoutMs)

    proc.on('exit', (code) => {
      clearTimeout(timer)
      resolve(out.length > CONFIG.bash.maxOutputBytes
        ? out.slice(0, CONFIG.bash.maxOutputBytes) + '\n[output truncated]'
        : out,
      )
    })
  })
}

function systemPrompt(): string {
  const cwd = process.cwd()
  return `You are an expert AI coding assistant. You have access to the following tools to help users with their code: bash (run shell commands), read_file, write_file, edit_file, glob (find files), grep (search in files).

Current working directory: ${cwd}

Guidelines:
- Always read files before editing them to understand the current state.
- Use bash for git operations, package installation, running tests, etc.
- When editing files, prefer edit_file for small targeted changes and write_file for complete rewrites.
- Be concise and explain what you're doing as you do it.
- If a tool call fails, adapt and try a different approach.`
}

function setSecurityHeaders(res: http.ServerResponse): void {
  res.setHeader('X-Content-Type-Options', 'nosniff')
  res.setHeader('X-Frame-Options', 'DENY')
  res.setHeader('Referrer-Policy', 'strict-origin-when-cross-origin')
}

function log(area: string, id: string, msg: string): void {
  const time = new Date().toISOString().slice(11, 23)
  console.log(`[${time}][${area}${id !== '-' ? ':' + id.slice(0, 8) : ''}] ${msg}`)
}

// ─────────────────────────────────────────────────────────────────────────────
// Graceful Shutdown
// ─────────────────────────────────────────────────────────────────────────────

function registerShutdown(server: http.Server, registry: SessionRegistry): void {
  const shutdown = (sig: string) => {
    log('server', '-', `${sig} — shutting down`)
    registry.destroy()
    server.close(() => process.exit(0))
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
    const key = process.env[CONFIG.openrouter.apiKeyEnv]
    console.log(`\n  Claude Code Web`)
    console.log(`  ──────────────────────────────────────`)
    console.log(`  🌐  http://${CONFIG.host}:${CONFIG.port}`)
    console.log(`  🔌  ws://${CONFIG.host}:${CONFIG.port}/ws`)
    console.log(`  📡  REST: /api/health  /api/sessions`)
    console.log(`  🤖  Model: ${CONFIG.model}`)
    console.log(`  🔑  API key: ${key ? '✓ set' : '✗ NOT SET — add ' + CONFIG.openrouter.apiKeyEnv}`)
    console.log(`  ──────────────────────────────────────\n`)
  })
}

start()
