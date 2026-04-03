import { useEffect, useRef, useState, useCallback } from 'react'

export type MsgRole = 'user' | 'assistant' | 'tool_call' | 'tool_result' | 'thinking' | 'system' | 'error' | 'result'

export interface ChatMessage {
  id: string
  role: MsgRole
  content: string
  toolName?: string
  toolId?: string
  toolInput?: unknown
  isError?: boolean
  costUsd?: number
  timestamp: number
  streaming?: boolean
}

export interface Conversation {
  id: string
  title: string
  messages: ChatMessage[]
  createdAt: number
  thinking?: boolean
}

type WSStatus = 'connecting' | 'connected' | 'disconnected' | 'error'

export function useWebSocket() {
  const ws = useRef<WebSocket | null>(null)
  const [status, setStatus] = useState<WSStatus>('disconnected')
  const [conversations, setConversations] = useState<Conversation[]>([])
  const [activeId, setActiveId] = useState<string | null>(null)
  const reconnectTimer = useRef<ReturnType<typeof setTimeout> | null>(null)
  const pendingConvId = useRef<string | null>(null)

  const getActive = useCallback((): Conversation | null => {
    return conversations.find(c => c.id === activeId) ?? null
  }, [conversations, activeId])

  const newConversation = useCallback(() => {
    const id = crypto.randomUUID()
    const conv: Conversation = { id, title: 'New conversation', messages: [], createdAt: Date.now() }
    setConversations(prev => [conv, ...prev])
    setActiveId(id)
    return id
  }, [])

  const appendMsg = useCallback((convId: string, msg: ChatMessage) => {
    setConversations(prev => prev.map(c => c.id === convId ? {
      ...c,
      messages: [...c.messages, msg],
      title: c.messages.length === 0 && msg.role === 'user' ? msg.content.slice(0, 50) : c.title,
    } : c))
  }, [])

  const patchStream = useCallback((convId: string, delta: string, done: boolean) => {
    setConversations(prev => prev.map(c => {
      if (c.id !== convId) return c
      const msgs = [...c.messages]
      const last = msgs[msgs.length - 1]
      if (last?.role === 'assistant' && last.streaming) {
        msgs[msgs.length - 1] = { ...last, content: last.content + delta, streaming: !done }
      } else {
        msgs.push({ id: crypto.randomUUID(), role: 'assistant', content: delta, timestamp: Date.now(), streaming: !done })
      }
      return { ...c, messages: msgs }
    }))
  }, [])

  const patchThinking = useCallback((convId: string, delta: string) => {
    setConversations(prev => prev.map(c => {
      if (c.id !== convId) return c
      const msgs = [...c.messages]
      const last = msgs[msgs.length - 1]
      if (last?.role === 'thinking' && last.streaming) {
        msgs[msgs.length - 1] = { ...last, content: last.content + delta, streaming: true }
      } else {
        msgs.push({ id: crypto.randomUUID(), role: 'thinking', content: delta, timestamp: Date.now(), streaming: true })
      }
      return { ...c, messages: msgs }
    }))
  }, [])

  const stopStreaming = useCallback((convId: string) => {
    setConversations(prev => prev.map(c => {
      if (c.id !== convId) return c
      return { ...c, thinking: false, messages: c.messages.map(m => ({ ...m, streaming: false })) }
    }))
  }, [])

  const mapConvId = useCallback((serverConvId: string, localConvId: string | null) => {
    if (!localConvId || serverConvId === localConvId) return
    // Remap server-assigned conv ID to our local one
    setConversations(prev => prev.map(c => c.id === localConvId ? { ...c, id: serverConvId } : c))
    if (activeId === localConvId) setActiveId(serverConvId)
  }, [activeId])

  const connect = useCallback(() => {
    if (ws.current?.readyState === WebSocket.OPEN) return
    const proto = location.protocol === 'https:' ? 'wss' : 'ws'
    const socket = new WebSocket(`${proto}://${location.host}/ws`)
    ws.current = socket
    setStatus('connecting')

    socket.onopen = () => setStatus('connected')
    socket.onclose = () => {
      setStatus('disconnected')
      reconnectTimer.current = setTimeout(connect, 3000)
    }
    socket.onerror = () => setStatus('error')

    socket.onmessage = (e) => {
      try {
        const data = JSON.parse(e.data) as Record<string, unknown>
        const convId = data.conversationId as string | undefined
        if (!convId) return

        switch (data.type) {
          case 'session_start':
            // Server assigned a conv ID — map it to our local one
            if (pendingConvId.current && pendingConvId.current !== convId) {
              mapConvId(convId, pendingConvId.current)
              pendingConvId.current = null
            }
            break

          case 'delta':
            patchStream(convId, data.content as string, false)
            break

          case 'assistant_text':
            appendMsg(convId, {
              id: crypto.randomUUID(), role: 'assistant',
              content: data.content as string, timestamp: Date.now(),
            })
            break

          case 'thinking':
            patchThinking(convId, data.content as string)
            break

          case 'tool_call':
            appendMsg(convId, {
              id: crypto.randomUUID(), role: 'tool_call',
              toolName: data.toolName as string,
              toolId: data.toolId as string,
              toolInput: data.input,
              content: JSON.stringify(data.input, null, 2),
              timestamp: Date.now(),
            })
            break

          case 'tool_result':
            appendMsg(convId, {
              id: crypto.randomUUID(), role: 'tool_result',
              toolId: data.toolId as string,
              content: data.content as string,
              isError: data.isError as boolean,
              timestamp: Date.now(),
            })
            break

          case 'system':
            appendMsg(convId, {
              id: crypto.randomUUID(), role: 'system',
              content: String(data.content ?? ''), timestamp: Date.now(),
            })
            break

          case 'result':
            stopStreaming(convId)
            if (data.costUsd) {
              appendMsg(convId, {
                id: crypto.randomUUID(), role: 'result',
                content: `Cost: $${(data.costUsd as number).toFixed(4)}`,
                costUsd: data.costUsd as number,
                timestamp: Date.now(),
              })
            }
            break

          case 'done':
            stopStreaming(convId)
            break

          case 'error':
            stopStreaming(convId)
            appendMsg(convId, {
              id: crypto.randomUUID(), role: 'error',
              content: data.content as string, timestamp: Date.now(),
            })
            break
        }
      } catch {}
    }
  }, [mapConvId, appendMsg, patchStream, patchThinking, stopStreaming])

  useEffect(() => {
    connect()
    return () => {
      reconnectTimer.current && clearTimeout(reconnectTimer.current)
      ws.current?.close()
    }
  }, [])

  const sendMessage = useCallback((text: string) => {
    let convId = activeId
    if (!convId) {
      convId = newConversation()
    }
    pendingConvId.current = convId

    appendMsg(convId, { id: crypto.randomUUID(), role: 'user', content: text, timestamp: Date.now() })

    if (ws.current?.readyState === WebSocket.OPEN) {
      ws.current.send(JSON.stringify({ type: 'message', content: text, conversationId: convId }))
    } else {
      appendMsg(convId, { id: crypto.randomUUID(), role: 'error', content: 'Not connected to server.', timestamp: Date.now() })
    }
  }, [activeId, newConversation, appendMsg])

  return { status, conversations, activeId, setActiveId, getActive, newConversation, sendMessage }
}
