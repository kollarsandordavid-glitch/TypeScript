import React, { useEffect, useRef, useState } from 'react'
import { Conversation } from '../hooks/useWebSocket'
import { Message } from './Message'

interface Props {
  conversation: Conversation | null
  onSend: (text: string) => void
  onInterrupt: (convId: string) => void
  status: string
  serverInfo: { model?: string; hasApiKey?: boolean }
  onMenuToggle: () => void
}

export function ChatWindow({ conversation, onSend, onInterrupt, status, serverInfo, onMenuToggle }: Props) {
  const [input, setInput] = useState('')
  const [rows, setRows] = useState(1)
  const bottomRef = useRef<HTMLDivElement>(null)
  const textareaRef = useRef<HTMLTextAreaElement>(null)

  const msgs = conversation?.messages ?? []
  const lastContent = msgs.length > 0 ? msgs[msgs.length - 1]?.content : undefined

  useEffect(() => {
    bottomRef.current?.scrollIntoView({ behavior: 'smooth' })
  }, [msgs.length, lastContent])

  const handleInput = (e: React.ChangeEvent<HTMLTextAreaElement>) => {
    setInput(e.target.value)
    setRows(Math.min((e.target.value.match(/\n/g) || []).length + 1, 8))
  }

  const submit = () => {
    const t = input.trim()
    if (!t) return
    onSend(t)
    setInput('')
    setRows(1)
  }

  const onKeyDown = (e: React.KeyboardEvent) => {
    if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); submit() }
  }

  const isLoading = conversation?.loading ?? false
  const connected = status === 'connected'
  const noKey = connected && serverInfo.hasApiKey === false

  return (
    <div style={{ flex: 1, display: 'flex', flexDirection: 'column', overflow: 'hidden', background: 'var(--bg)' }}>
      {/* Header */}
      <header style={{
        height: 48, borderBottom: '1px solid var(--border)', display: 'flex', alignItems: 'center',
        padding: '0 12px', gap: 10, flexShrink: 0, background: 'var(--bg)',
      }}>
        <button onClick={onMenuToggle} style={{ width: 32, height: 32, borderRadius: 8, display: 'flex', alignItems: 'center', justifyContent: 'center', color: 'var(--text2)', fontSize: 16 }}>☰</button>
        <span style={{ fontWeight: 600, fontSize: 13, flex: 1, overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' }}>
          {conversation?.title || 'Claude Code Web'}
        </span>
        {serverInfo.model && (
          <span style={{ fontSize: 10, color: 'var(--text3)', fontFamily: 'var(--mono)', padding: '3px 6px', background: 'var(--bg3)', borderRadius: 4 }}>
            {serverInfo.model.split('/').pop()}
          </span>
        )}
        <div style={{
          display: 'flex', alignItems: 'center', gap: 4, padding: '3px 7px', borderRadius: 12,
          background: connected ? 'rgba(74,222,128,0.08)' : 'rgba(248,113,113,0.08)',
          fontSize: 10, color: connected ? '#4ade80' : '#f87171', fontWeight: 500,
        }}>
          <span style={{ width: 5, height: 5, borderRadius: '50%', background: connected ? '#4ade80' : '#f87171', animation: connected ? 'pulse 2s infinite' : 'none' }} />
          {connected ? 'Live' : status}
        </div>
      </header>

      {/* No API key warning */}
      {noKey && (
        <div style={{ padding: '8px 16px', background: 'rgba(251,191,36,0.08)', borderBottom: '1px solid rgba(251,191,36,0.15)', color: '#fbbf24', fontSize: 12, display: 'flex', alignItems: 'center', gap: 6 }}>
          <span>⚠</span> OPENROUTER_API_KEY is not set. Add it to your environment variables.
        </div>
      )}

      {/* Messages */}
      <div style={{ flex: 1, overflowY: 'auto', padding: '16px 16px 8px' }}>
        {!conversation || conversation.messages.length === 0 ? (
          <div style={{ height: '100%', display: 'flex', flexDirection: 'column', alignItems: 'center', justifyContent: 'center', gap: 14, color: 'var(--text3)', userSelect: 'none' }}>
            <div style={{
              width: 50, height: 50, borderRadius: 14, background: '#cc785c',
              display: 'flex', alignItems: 'center', justifyContent: 'center',
              fontSize: 20, fontWeight: 700, color: '#fff', boxShadow: '0 0 28px rgba(204,120,92,0.2)',
            }}>AI</div>
            <div style={{ fontSize: 16, fontWeight: 600, color: 'var(--text2)' }}>Claude Code Web</div>
            <div style={{ fontSize: 12, color: 'var(--text3)', textAlign: 'center', maxWidth: 350 }}>
              Full agentic AI assistant with bash, file read/write/edit, search tools.
              {serverInfo.model && <><br />Model: {serverInfo.model}</>}
            </div>
            <div style={{ display: 'flex', gap: 6, flexWrap: 'wrap', justifyContent: 'center', maxWidth: 420, marginTop: 4 }}>
              {['List all files', 'Read package.json', 'Run ls -la', 'Explain this project'].map(s => (
                <button key={s} onClick={() => { setInput(s); textareaRef.current?.focus() }}
                  style={{
                    padding: '6px 12px', borderRadius: 16, background: 'var(--bg3)',
                    border: '1px solid var(--border2)', color: 'var(--text2)', fontSize: 12,
                    transition: 'all 0.15s',
                  }}
                  onMouseEnter={e => { e.currentTarget.style.borderColor = '#cc785c'; e.currentTarget.style.color = '#f2f2f2' }}
                  onMouseLeave={e => { e.currentTarget.style.borderColor = 'var(--border2)'; e.currentTarget.style.color = 'var(--text2)' }}
                >{s}</button>
              ))}
            </div>
          </div>
        ) : (
          <>
            {conversation.messages.map(m => <Message key={m.id} msg={m} />)}
            {isLoading && conversation.messages[conversation.messages.length - 1]?.role !== 'assistant' && (
              <div style={{ display: 'flex', gap: 10, margin: '8px 0', alignItems: 'center' }}>
                <div style={{ width: 26, height: 26, borderRadius: 7, background: '#cc785c', display: 'flex', alignItems: 'center', justifyContent: 'center', fontSize: 12, fontWeight: 700, color: '#fff' }}>AI</div>
                <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
                  <span style={{ width: 4, height: 4, borderRadius: '50%', background: '#cc785c', animation: 'pulse 1s infinite' }} />
                  <span style={{ width: 4, height: 4, borderRadius: '50%', background: '#cc785c', animation: 'pulse 1s 0.2s infinite' }} />
                  <span style={{ width: 4, height: 4, borderRadius: '50%', background: '#cc785c', animation: 'pulse 1s 0.4s infinite' }} />
                </div>
              </div>
            )}
            <div ref={bottomRef} />
          </>
        )}
      </div>

      {/* Input */}
      <div style={{ padding: '10px 14px 14px', borderTop: '1px solid var(--border)', background: 'var(--bg)', flexShrink: 0 }}>
        <div style={{
          display: 'flex', alignItems: 'flex-end', gap: 8,
          background: 'var(--bg2)', border: '1px solid var(--border2)',
          borderRadius: 14, padding: '8px 10px 8px 14px', transition: 'border-color 0.15s',
        }}
          onFocusCapture={e => e.currentTarget.style.borderColor = '#cc785c'}
          onBlurCapture={e => e.currentTarget.style.borderColor = 'var(--border2)'}
        >
          <textarea ref={textareaRef} value={input} onChange={handleInput} onKeyDown={onKeyDown} rows={rows}
            placeholder={isLoading ? 'Waiting for response...' : 'Message... (Enter to send)'}
            disabled={isLoading}
            style={{ flex: 1, resize: 'none', background: 'transparent', color: 'var(--text)', fontSize: 14, lineHeight: 1.6, maxHeight: 200, overflowY: 'auto', opacity: isLoading ? 0.5 : 1 }}
          />
          {isLoading && conversation ? (
            <button onClick={() => onInterrupt(conversation.id)}
              style={{
                width: 32, height: 32, borderRadius: 8, background: '#7d3a3a', color: '#fff',
                display: 'flex', alignItems: 'center', justifyContent: 'center', fontSize: 14, flexShrink: 0,
              }}
              title="Stop"
            >■</button>
          ) : (
            <button onClick={submit} disabled={!input.trim()}
              style={{
                width: 32, height: 32, borderRadius: 8,
                background: input.trim() ? '#cc785c' : 'var(--bg4)', color: input.trim() ? '#fff' : 'var(--text3)',
                display: 'flex', alignItems: 'center', justifyContent: 'center', fontSize: 14, flexShrink: 0,
                transition: 'all 0.15s',
              }}
            >↑</button>
          )}
        </div>
      </div>
    </div>
  )
}
