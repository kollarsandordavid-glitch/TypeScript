import { useEffect, useRef, useState, useCallback } from 'react'

export type MsgRole = 'user' | 'assistant' | 'tool' | 'error' | 'system'

export interface ChatMessage {
  id: string
  role: MsgRole
  content: string
  toolName?: string
  timestamp: number
  streaming?: boolean
}

export interface Conversation {
  id: string
  title: string
  messages: ChatMessage[]
  createdAt: number
}

type WSStatus = 'connecting' | 'connected' | 'disconnected' | 'error'

export function useWebSocket() {
  const ws = useRef<WebSocket | null>(null)
  const [status, setStatus] = useState<WSStatus>('disconnected')
  const [conversations, setConversations] = useState<Conversation[]>([])
  const [activeId, setActiveId] = useState<string | null>(null)
  const reconnectTimer = useRef<ReturnType<typeof setTimeout> | null>(null)

  const getActive = useCallback((): Conversation | null => {
    return conversations.find(c => c.id === activeId) ?? null
  }, [conversations, activeId])

  const newConversation = useCallback(() => {
    const id = crypto.randomUUID()
    const conv: Conversation = {
      id,
      title: 'New conversation',
      messages: [],
      createdAt: Date.now(),
    }
    setConversations(prev => [conv, ...prev])
    setActiveId(id)
    return id
  }, [])

  const appendMessage = useCallback((convId: string, msg: ChatMessage) => {
    setConversations(prev =>
      prev.map(c =>
        c.id === convId
          ? {
              ...c,
              messages: [...c.messages, msg],
              title:
                c.messages.length === 0 && msg.role === 'user'
                  ? msg.content.slice(0, 48)
                  : c.title,
            }
          : c
      )
    )
  }, [])

  const patchLastAssistant = useCallback((convId: string, delta: string, done: boolean) => {
    setConversations(prev =>
      prev.map(c => {
        if (c.id !== convId) return c
        const msgs = [...c.messages]
        const last = msgs[msgs.length - 1]
        if (last && last.role === 'assistant' && last.streaming) {
          msgs[msgs.length - 1] = {
            ...last,
            content: last.content + delta,
            streaming: !done,
          }
        } else {
          msgs.push({
            id: crypto.randomUUID(),
            role: 'assistant',
            content: delta,
            timestamp: Date.now(),
            streaming: !done,
          })
        }
        return { ...c, messages: msgs }
      })
    )
  }, [])

  const connect = useCallback(() => {
    if (ws.current?.readyState === WebSocket.OPEN) return

    const proto = location.protocol === 'https:' ? 'wss' : 'ws'
    const socket = new WebSocket(`${proto}://${location.host}/ws`)
    ws.current = socket
    setStatus('connecting')

    socket.onopen = () => setStatus('connected')

    socket.onmessage = (e) => {
      try {
        const data = JSON.parse(e.data)
        const convId = data.conversationId ?? activeId
        if (!convId) return

        if (data.type === 'delta') {
          patchLastAssistant(convId, data.content, false)
        } else if (data.type === 'done') {
          patchLastAssistant(convId, '', true)
        } else if (data.type === 'tool') {
          appendMessage(convId, {
            id: crypto.randomUUID(),
            role: 'tool',
            toolName: data.toolName,
            content: data.content,
            timestamp: Date.now(),
          })
        } else if (data.type === 'error') {
          appendMessage(convId, {
            id: crypto.randomUUID(),
            role: 'error',
            content: data.content,
            timestamp: Date.now(),
          })
        }
      } catch {}
    }

    socket.onclose = () => {
      setStatus('disconnected')
      reconnectTimer.current = setTimeout(connect, 3000)
    }

    socket.onerror = () => setStatus('error')
  }, [activeId, appendMessage, patchLastAssistant])

  useEffect(() => {
    connect()
    return () => {
      reconnectTimer.current && clearTimeout(reconnectTimer.current)
      ws.current?.close()
    }
  }, [])

  const sendMessage = useCallback((text: string) => {
    let convId = activeId
    if (!convId) convId = newConversation()

    const msg: ChatMessage = {
      id: crypto.randomUUID(),
      role: 'user',
      content: text,
      timestamp: Date.now(),
    }
    appendMessage(convId, msg)

    if (ws.current?.readyState === WebSocket.OPEN) {
      ws.current.send(JSON.stringify({ type: 'message', content: text, conversationId: convId }))
    } else {
      setTimeout(() => {
        appendMessage(convId!, {
          id: crypto.randomUUID(),
          role: 'error',
          content: 'Not connected to server.',
          timestamp: Date.now(),
        })
      }, 100)
    }
  }, [activeId, newConversation, appendMessage])

  return {
    status,
    conversations,
    activeId,
    setActiveId,
    getActive,
    newConversation,
    sendMessage,
  }
}
