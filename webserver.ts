import * as http from 'http'
import * as fs from 'fs'
import * as path from 'path'
import * as url from 'url'
import { spawn, type ChildProcessWithoutNullStreams } from 'child_process'
import { WebSocketServer, WebSocket } from 'ws'

const PORT = 5000
const __dirname = path.dirname(url.fileURLToPath(import.meta.url))
const PUBLIC = path.join(__dirname, 'public')

const MIME: Record<string, string> = {
  '.html': 'text/html',
  '.js': 'application/javascript',
  '.mjs': 'application/javascript',
  '.css': 'text/css',
  '.json': 'application/json',
  '.png': 'image/png',
  '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon',
  '.woff2': 'font/woff2',
  '.webmanifest': 'application/manifest+json',
}

// ─── HTTP server (serves built frontend) ────────────────────────────────────
const server = http.createServer((req, res) => {
  const parsed = url.parse(req.url ?? '/')
  let filePath = path.join(PUBLIC, parsed.pathname === '/' ? 'index.html' : parsed.pathname ?? '')

  res.setHeader('Access-Control-Allow-Origin', '*')
  res.setHeader('Cache-Control', 'no-cache')

  if (!fs.existsSync(filePath) || fs.statSync(filePath).isDirectory()) {
    filePath = path.join(PUBLIC, 'index.html')
  }

  const ext = path.extname(filePath)
  const contentType = MIME[ext] ?? 'application/octet-stream'

  try {
    const data = fs.readFileSync(filePath)
    res.writeHead(200, { 'Content-Type': contentType })
    res.end(data)
  } catch {
    res.writeHead(404)
    res.end('Not found')
  }
})

// ─── WebSocket server ────────────────────────────────────────────────────────
const wss = new WebSocketServer({ server, path: '/ws' })

interface Session {
  proc: ChildProcessWithoutNullStreams
  convId: string
  ws: WebSocket
  buf: string
}

const sessions = new Map<string, Session>()

wss.on('connection', (ws) => {
  console.log('[ws] Client connected')

  ws.on('message', async (raw) => {
    let data: { type: string; content?: string; conversationId?: string; cwd?: string }
    try { data = JSON.parse(raw.toString()) } catch { return }

    if (data.type === 'message' && data.content) {
      const convId = data.conversationId ?? crypto.randomUUID()
      const existing = sessions.get(convId)

      if (existing && existing.proc.exitCode === null) {
        // Send follow-up message to existing process stdin
        sendToProcess(existing, data.content)
      } else {
        // Spawn a new Claude Code process for this conversation
        spawnClaudeProcess(ws, convId, data.content, data.cwd)
      }
    }

    if (data.type === 'interrupt') {
      const sess = sessions.get(data.conversationId ?? '')
      if (sess) sess.proc.kill('SIGINT')
    }
  })

  ws.on('close', () => {
    console.log('[ws] Client disconnected')
    // Clean up processes belonging to this client
    for (const [convId, sess] of sessions.entries()) {
      if (sess.ws === ws && sess.proc.exitCode === null) {
        sess.proc.kill()
        sessions.delete(convId)
      }
    }
  })
})

function sendToProcess(sess: Session, message: string) {
  // stream-json input: write JSON-encoded user message
  const msg = JSON.stringify({ type: 'user', message: { role: 'user', content: message } }) + '\n'
  sess.proc.stdin.write(msg)
  console.log(`[proc:${sess.convId}] → stdin: ${message.slice(0, 80)}`)
}

function spawnClaudeProcess(ws: WebSocket, convId: string, initialPrompt: string, cwd?: string) {
  const workDir = cwd ?? process.cwd()

  const args = [
    'main.tsx',
    '--print',
    '--output-format', 'stream-json',
    '--verbose',
    '--input-format', 'stream-json',
    '--dangerously-skip-permissions',
    '--include-partial-messages',
    initialPrompt,
  ]

  console.log(`[proc:${convId}] Spawning: bun ${args.join(' ').slice(0, 120)}`)

  const proc = spawn('bun', args, {
    cwd: workDir,
    stdio: ['pipe', 'pipe', 'pipe'],
    env: {
      ...process.env,
      TERM: 'dumb',
      NO_COLOR: '1',
      FORCE_COLOR: '0',
    },
  })

  const sess: Session = { proc, convId, ws, buf: '' }
  sessions.set(convId, sess)

  send(ws, { type: 'session_start', conversationId: convId })

  // ─── stdout: JSON-line stream ───────────────────────────────────────────
  proc.stdout.on('data', (chunk: Buffer) => {
    sess.buf += chunk.toString()
    const lines = sess.buf.split('\n')
    sess.buf = lines.pop() ?? ''

    for (const line of lines) {
      const trimmed = line.trim()
      if (!trimmed) continue
      try {
        const msg = JSON.parse(trimmed)
        handleClaudeMessage(ws, convId, msg)
      } catch {
        // plain text fallback
        if (trimmed) send(ws, { type: 'text', content: trimmed, conversationId: convId })
      }
    }
  })

  // ─── stderr: forward as system messages ────────────────────────────────
  proc.stderr.on('data', (chunk: Buffer) => {
    const text = chunk.toString().trim()
    if (text) {
      console.error(`[proc:${convId}] stderr:`, text.slice(0, 200))
      send(ws, { type: 'stderr', content: text, conversationId: convId })
    }
  })

  proc.on('exit', (code) => {
    console.log(`[proc:${convId}] Exited with code ${code}`)
    sessions.delete(convId)
    send(ws, { type: 'done', conversationId: convId, exitCode: code })
  })

  proc.on('error', (err) => {
    console.error(`[proc:${convId}] Error:`, err.message)
    send(ws, { type: 'error', content: err.message, conversationId: convId })
  })
}

// ─── Parse and relay Claude stream-json messages ────────────────────────────
function handleClaudeMessage(ws: WebSocket, convId: string, msg: Record<string, unknown>) {
  const type = msg.type as string

  // Assistant text streaming
  if (type === 'assistant') {
    const message = msg.message as Record<string, unknown> | undefined
    if (message?.content && Array.isArray(message.content)) {
      for (const block of message.content) {
        const b = block as Record<string, unknown>
        if (b.type === 'text') {
          send(ws, { type: 'assistant_text', content: b.text, conversationId: convId })
        } else if (b.type === 'tool_use') {
          send(ws, {
            type: 'tool_call',
            toolId: b.id,
            toolName: b.name,
            input: b.input,
            conversationId: convId,
          })
        } else if (b.type === 'thinking') {
          send(ws, { type: 'thinking', content: b.thinking, conversationId: convId })
        }
      }
    }
  }

  // Tool result
  else if (type === 'tool_result' || type === 'user') {
    const message = msg.message as Record<string, unknown> | undefined
    if (message?.content && Array.isArray(message.content)) {
      for (const block of message.content) {
        const b = block as Record<string, unknown>
        if (b.type === 'tool_result') {
          send(ws, {
            type: 'tool_result',
            toolId: b.tool_use_id,
            content: Array.isArray(b.content)
              ? (b.content as Array<Record<string, unknown>>).map(c => c.text ?? '').join('\n')
              : String(b.content ?? ''),
            isError: b.is_error,
            conversationId: convId,
          })
        }
      }
    }
  }

  // Partial streaming events
  else if (type === 'stream_event') {
    const event = msg.event as Record<string, unknown> | undefined
    if (event?.type === 'content_block_delta') {
      const delta = event.delta as Record<string, unknown> | undefined
      if (delta?.type === 'text_delta') {
        send(ws, { type: 'delta', content: delta.text, conversationId: convId })
      }
    }
  }

  // System info
  else if (type === 'system') {
    send(ws, { type: 'system', content: msg.subtype ?? msg.message, conversationId: convId })
  }

  // Final result
  else if (type === 'result') {
    send(ws, {
      type: 'result',
      result: msg.result,
      is_error: msg.is_error,
      costUsd: msg.total_cost_usd,
      conversationId: convId,
    })
  }

  // Permission request
  else if (type === 'permission_request' || type === 'requires_action') {
    send(ws, { type: 'permission', data: msg, conversationId: convId })
  }

  // Pass everything else through too
  else {
    send(ws, { type: 'raw', data: msg, conversationId: convId })
  }
}

function send(ws: WebSocket, data: object) {
  if (ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify(data))
  }
}

server.listen(PORT, '0.0.0.0', () => {
  console.log(`🚀 Claude Code Web at http://0.0.0.0:${PORT}`)
  console.log(`   Bun: ${process.env.BUN_VERSION ?? 'via PATH'}`)
})
