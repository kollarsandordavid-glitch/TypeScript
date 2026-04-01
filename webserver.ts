import * as http from 'http'
import * as fs from 'fs'
import * as path from 'path'
import * as url from 'url'
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
  '.woff': 'font/woff',
  '.ttf': 'font/ttf',
  '.webmanifest': 'application/manifest+json',
}

const server = http.createServer((req, res) => {
  const parsed = url.parse(req.url ?? '/')
  let filePath = path.join(PUBLIC, parsed.pathname === '/' ? 'index.html' : parsed.pathname ?? '')

  res.setHeader('Access-Control-Allow-Origin', '*')
  res.setHeader('Cache-Control', 'no-cache')

  if (!fs.existsSync(filePath)) {
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

const wss = new WebSocketServer({ server, path: '/ws' })

interface ClientState {
  conversations: Map<string, Array<{ role: string; content: string }>>
}

const clients = new Map<WebSocket, ClientState>()

wss.on('connection', (ws) => {
  const state: ClientState = { conversations: new Map() }
  clients.set(ws, state)

  ws.on('message', async (raw) => {
    let data: { type: string; content?: string; conversationId?: string }
    try {
      data = JSON.parse(raw.toString())
    } catch {
      return
    }

    if (data.type === 'message' && data.content) {
      const convId = data.conversationId ?? 'default'
      const history = state.conversations.get(convId) ?? []
      history.push({ role: 'user', content: data.content })
      state.conversations.set(convId, history)

      try {
        await streamResponse(ws, data.content, convId, history)
      } catch (err) {
        send(ws, { type: 'error', content: String(err), conversationId: convId })
      }
    }
  })

  ws.on('close', () => clients.delete(ws))
})

async function streamResponse(
  ws: WebSocket,
  userMsg: string,
  convId: string,
  history: Array<{ role: string; content: string }>
) {
  const apiKey = process.env.ANTHROPIC_API_KEY

  if (!apiKey) {
    const reply = demoReply(userMsg)
    for (const chunk of reply) {
      if (ws.readyState !== WebSocket.OPEN) return
      send(ws, { type: 'delta', content: chunk, conversationId: convId })
      await sleep(30)
    }
    send(ws, { type: 'done', conversationId: convId })
    history.push({ role: 'assistant', content: reply.join('') })
    return
  }

  const messages = history.slice(-20).map(m => ({ role: m.role as 'user' | 'assistant', content: m.content }))

  const resp = await fetch('https://api.anthropic.com/v1/messages', {
    method: 'POST',
    headers: {
      'x-api-key': apiKey,
      'anthropic-version': '2023-06-01',
      'content-type': 'application/json',
    },
    body: JSON.stringify({
      model: 'claude-opus-4-5',
      max_tokens: 4096,
      stream: true,
      system: 'You are Claude Code, an expert AI coding assistant. Help the user with their coding tasks clearly and concisely.',
      messages,
    }),
  })

  if (!resp.ok || !resp.body) {
    throw new Error(`API error: ${resp.status} ${await resp.text()}`)
  }

  const reader = resp.body.getReader()
  const dec = new TextDecoder()
  let fullText = ''
  let buf = ''

  while (true) {
    const { done, value } = await reader.read()
    if (done) break
    buf += dec.decode(value, { stream: true })
    const lines = buf.split('\n')
    buf = lines.pop() ?? ''

    for (const line of lines) {
      if (!line.startsWith('data: ')) continue
      const payload = line.slice(6).trim()
      if (payload === '[DONE]') continue
      try {
        const ev = JSON.parse(payload)
        if (ev.type === 'content_block_delta' && ev.delta?.type === 'text_delta') {
          const chunk = ev.delta.text as string
          fullText += chunk
          if (ws.readyState === WebSocket.OPEN) {
            send(ws, { type: 'delta', content: chunk, conversationId: convId })
          }
        }
      } catch {}
    }
  }

  send(ws, { type: 'done', conversationId: convId })
  history.push({ role: 'assistant', content: fullText })
}

function demoReply(msg: string): string[] {
  const text = `I received your message: "${msg}"\n\nThis is a demo response since no **ANTHROPIC_API_KEY** is set. Add your API key to get real Claude responses!\n\nTo set it up:\n1. Get your API key from console.anthropic.com\n2. Set ANTHROPIC_API_KEY in your environment\n3. Restart the server`
  return text.match(/.{1,8}/g) ?? [text]
}

function send(ws: WebSocket, data: object) {
  if (ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify(data))
  }
}

function sleep(ms: number) {
  return new Promise(r => setTimeout(r, ms))
}

server.listen(PORT, '0.0.0.0', () => {
  console.log(`🚀 Claude Code Web running at http://0.0.0.0:${PORT}`)
})
