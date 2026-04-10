import { useEffect, useRef, useState, useCallback } from 'react'

export type MsgRole = 'user' | 'assistant' | 'tool_call' | 'tool_result' | 'thinking' | 'system' | 'error' | 'result' | 'stderr'

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
  loading: boolean
}

type WSStatus = 'connecting' | 'connected' | 'disconnected'

interface ServerInfo {
  model?: string
  hasApiKey?: boolean
}

export function useWebSocket() {
  const wsRef = useRef<WebSocket | null>(null)
  const [status, setStatus] = useState<WSStatus>('disconnected')
  const [serverInfo, setServerInfo] = useState<ServerInfo>({})

  const convsRef = useRef<Conversation[]>([])
  const [conversations, setConversations] = useState<Conversation[]>([])
  const activeRef = useRef<string | null>(null)
  const [activeId, setActiveIdState] = useState<string | null>(null)

  const updateConvs = useCallback((fn: (prev: Conversation[]) => Conversation[]) => {
    convsRef.current = fn(convsRef.current)
    setConversations([...convsRef.current])
  }, [])

  const setActiveId = useCallback((id: string | null) => {
    activeRef.current = id
    setActiveIdState(id)
  }, [])

  const getActive = useCallback((): Conversation | null => {
    return convsRef.current.find(c => c.id === activeRef.current) ?? null
  }, [])

  const uid = () => crypto.randomUUID()

  const newConversation = useCallback(() => {
    const id = uid()
    const conv: Conversation = { id, title: 'New chat', messages: [], createdAt: Date.now(), loading: false }
    updateConvs(prev => [conv, ...prev])
    setActiveId(id)
    return id
  }, [updateConvs, setActiveId])

  const appendMsg = useCallback((convId: string, msg: ChatMessage) => {
    updateConvs(prev => prev.map(c => {
      if (c.id !== convId) return c
      const title = c.messages.length === 0 && msg.role === 'user' ? msg.content.slice(0, 50) : c.title
      return { ...c, messages: [...c.messages, msg], title }
    }))
  }, [updateConvs])

  const setLoading = useCallback((convId: string, loading: boolean) => {
    updateConvs(prev => prev.map(c => c.id === convId ? { ...c, loading } : c))
  }, [updateConvs])

  const patchDelta = useCallback((convId: string, delta: string) => {
    updateConvs(prev => prev.map(c => {
      if (c.id !== convId) return c
      const msgs = [...c.messages]
      const last = msgs[msgs.length - 1]
      if (last?.role === 'assistant' && last.streaming) {
        msgs[msgs.length - 1] = { ...last, content: last.content + delta }
      } else {
        msgs.push({ id: uid(), role: 'assistant', content: delta, timestamp: Date.now(), streaming: true })
      }
      return { ...c, messages: msgs, loading: true }
    }))
  }, [updateConvs])

  const patchThinking = useCallback((convId: string, delta: string) => {
    updateConvs(prev => prev.map(c => {
      if (c.id !== convId) return c
      const msgs = [...c.messages]
      const last = msgs[msgs.length - 1]
      if (last?.role === 'thinking' && last.streaming) {
        msgs[msgs.length - 1] = { ...last, content: last.content + delta }
      } else {
        msgs.push({ id: uid(), role: 'thinking', content: delta, timestamp: Date.now(), streaming: true })
      }
      return { ...c, messages: msgs, loading: true }
    }))
  }, [updateConvs])

  const stopAllStreaming = useCallback((convId: string) => {
    updateConvs(prev => prev.map(c => {
      if (c.id !== convId) return c
      return { ...c, loading: false, messages: c.messages.map(m => ({ ...m, streaming: false })) }
    }))
  }, [updateConvs])

  const handleMessage = useCallback((e: MessageEvent) => {
    let data: Record<string, unknown>
    try { data = JSON.parse(e.data) } catch { return }
    const convId = data.conversationId as string | undefined

    switch (data.type) {
      case 'connected':
        setServerInfo({ model: data.model as string, hasApiKey: data.hasApiKey as boolean })
        break
      case 'pong':
        break
      case 'session_start':
        if (convId) setLoading(convId, true)
        break
      case 'delta':
        if (convId) patchDelta(convId, data.content as string)
        break
      case 'thinking_delta':
        if (convId) patchThinking(convId, data.content as string)
        break
      case 'assistant_text':
        if (convId) appendMsg(convId, { id: uid(), role: 'assistant', content: data.content as string, timestamp: Date.now() })
        break
      case 'thinking':
        if (convId) appendMsg(convId, { id: uid(), role: 'thinking', content: data.content as string, timestamp: Date.now() })
        break
      case 'tool_call':
        if (convId) appendMsg(convId, {
          id: uid(), role: 'tool_call', content: JSON.stringify(data.input, null, 2),
          toolName: data.toolName as string, toolId: data.toolId as string, toolInput: data.input,
          timestamp: Date.now(),
        })
        break
      case 'tool_result':
        if (convId) appendMsg(convId, {
          id: uid(), role: 'tool_result', content: data.content as string,
          toolId: data.toolId as string, toolName: data.toolName as string,
          isError: data.isError as boolean, timestamp: Date.now(),
        })
        break
      case 'stderr':
        if (convId) appendMsg(convId, { id: uid(), role: 'stderr', content: data.content as string, timestamp: Date.now() })
        break
      case 'result':
      case 'done':
      case 'session_end':
        if (convId) stopAllStreaming(convId)
        break
      case 'interrupted':
        if (convId) stopAllStreaming(convId)
        break
      case 'error':
        if (convId) {
          stopAllStreaming(convId)
          appendMsg(convId, { id: uid(), role: 'error', content: data.content as string, timestamp: Date.now() })
        }
        break
    }
  }, [appendMsg, patchDelta, patchThinking, setLoading, stopAllStreaming, setServerInfo])

  const handleMessageRef = useRef(handleMessage)
  handleMessageRef.current = handleMessage

  useEffect(() => {
    let disposed = false
    let timer: ReturnType<typeof setTimeout> | null = null
    let socket: WebSocket | null = null

    const connect = () => {
      if (disposed) return
      if (socket?.readyState === WebSocket.OPEN || socket?.readyState === WebSocket.CONNECTING) return
      const proto = location.protocol === 'https:' ? 'wss' : 'ws'
      socket = new WebSocket(`${proto}://${location.host}/ws`)
      wsRef.current = socket
      setStatus('connecting')

      socket.onopen = () => { if (!disposed) setStatus('connected') }
      socket.onclose = () => {
        if (disposed) return
        setStatus('disconnected')
        timer = setTimeout(connect, 2000)
      }
      socket.onerror = () => { /* onclose will fire */ }
      socket.onmessage = (e) => handleMessageRef.current(e)
    }

    connect()

    const ping = setInterval(() => {
      if (wsRef.current?.readyState === WebSocket.OPEN) {
        wsRef.current.send(JSON.stringify({ type: 'ping' }))
      }
    }, 20_000)

    return () => {
      disposed = true
      clearInterval(ping)
      timer && clearTimeout(timer)
      if (socket) {
        socket.onclose = null
        socket.onmessage = null
        socket.onerror = null
        socket.close()
      }
    }
  }, [])

  const sendMessage = useCallback((text: string) => {
    let convId = activeRef.current
    if (!convId) convId = newConversation()
    appendMsg(convId, { id: uid(), role: 'user', content: text, timestamp: Date.now() })
    if (wsRef.current?.readyState === WebSocket.OPEN) {
      setLoading(convId, true)
      wsRef.current.send(JSON.stringify({ type: 'message', content: text, conversationId: convId }))
    } else {
      appendMsg(convId, { id: uid(), role: 'error', content: 'Not connected. Try again in a moment.', timestamp: Date.now() })
    }
  }, [newConversation, appendMsg, setLoading])

  const interrupt = useCallback((convId: string) => {
    wsRef.current?.readyState === WebSocket.OPEN &&
      wsRef.current.send(JSON.stringify({ type: 'interrupt', conversationId: convId }))
  }, [])

  return { status, serverInfo, conversations, activeId, setActiveId, getActive, newConversation, sendMessage, interrupt }
}
