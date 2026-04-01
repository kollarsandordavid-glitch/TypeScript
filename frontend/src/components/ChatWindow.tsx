import React, { useEffect, useRef, useState } from 'react'
import { Conversation } from '../hooks/useWebSocket'
import { Message } from './Message'

interface Props {
  conversation: Conversation | null
  onSend: (text: string) => void
  status: string
  onMenuOpen: () => void
}

export function ChatWindow({ conversation, onSend, status, onMenuOpen }: Props) {
  const [input, setInput] = useState('')
  const [rows, setRows] = useState(1)
  const bottomRef = useRef<HTMLDivElement>(null)
  const textareaRef = useRef<HTMLTextAreaElement>(null)

  useEffect(() => {
    bottomRef.current?.scrollIntoView({ behavior: 'smooth' })
  }, [conversation?.messages])

  const handleInput = (e: React.ChangeEvent<HTMLTextAreaElement>) => {
    const val = e.target.value
    setInput(val)
    const lineCount = (val.match(/\n/g) || []).length + 1
    setRows(Math.min(lineCount, 8))
  }

  const submit = () => {
    const text = input.trim()
    if (!text) return
    onSend(text)
    setInput('')
    setRows(1)
    textareaRef.current?.focus()
  }

  const onKeyDown = (e: React.KeyboardEvent<HTMLTextAreaElement>) => {
    if (e.key === 'Enter' && !e.shiftKey) {
      e.preventDefault()
      submit()
    }
  }

  const connected = status === 'connected'

  return (
    <div style={{ flex: 1, display: 'flex', flexDirection: 'column', overflow: 'hidden', background: 'var(--bg)' }}>
      <header style={{
        height: 52,
        borderBottom: '1px solid var(--border)',
        display: 'flex',
        alignItems: 'center',
        padding: '0 16px',
        gap: 12,
        flexShrink: 0,
        background: 'var(--bg)',
      }}>
        <button
          onClick={onMenuOpen}
          style={{
            width: 32, height: 32, borderRadius: 8,
            display: 'flex', alignItems: 'center', justifyContent: 'center',
            color: 'var(--text2)', fontSize: 18,
            transition: 'background 0.15s',
          }}
          className="menu-btn"
        >☰</button>
        <span style={{ fontWeight: 600, fontSize: 14, flex: 1, overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' }}>
          {conversation?.title || 'Claude Code Web'}
        </span>
        <div style={{
          display: 'flex', alignItems: 'center', gap: 5,
          padding: '4px 8px',
          borderRadius: 20,
          background: connected ? 'rgba(74,222,128,0.1)' : 'rgba(248,113,113,0.1)',
          fontSize: 11,
          color: connected ? 'var(--green)' : 'var(--red)',
          fontWeight: 500,
        }}>
          <span style={{
            width: 6, height: 6, borderRadius: '50%',
            background: connected ? 'var(--green)' : 'var(--red)',
            animation: connected ? 'pulse 2s infinite' : 'none',
          }} />
          {connected ? 'Live' : status}
        </div>
      </header>

      <div style={{ flex: 1, overflowY: 'auto', padding: '20px 16px 8px' }}>
        {!conversation || conversation.messages.length === 0 ? (
          <div style={{
            height: '100%', display: 'flex', flexDirection: 'column',
            alignItems: 'center', justifyContent: 'center', gap: 16,
            color: 'var(--text3)', userSelect: 'none',
          }}>
            <div style={{
              width: 56, height: 56, borderRadius: 16,
              background: 'var(--accent)',
              display: 'flex', alignItems: 'center', justifyContent: 'center',
              fontSize: 26, fontWeight: 700, color: '#fff',
              boxShadow: '0 0 32px var(--accent-glow)',
            }}>C</div>
            <div style={{ textAlign: 'center' }}>
              <div style={{ fontSize: 18, fontWeight: 600, color: 'var(--text2)', marginBottom: 6 }}>Claude Code Web</div>
              <div style={{ fontSize: 13 }}>Start a conversation below</div>
            </div>
            <div style={{ display: 'flex', gap: 8, flexWrap: 'wrap', justifyContent: 'center', maxWidth: 400 }}>
              {['Explain this codebase', 'Write a function', 'Fix a bug', 'Review my code'].map(s => (
                <button
                  key={s}
                  onClick={() => { setInput(s); textareaRef.current?.focus() }}
                  style={{
                    padding: '7px 14px',
                    borderRadius: 20,
                    background: 'var(--bg3)',
                    border: '1px solid var(--border2)',
                    color: 'var(--text2)',
                    fontSize: 12,
                    transition: 'all 0.15s',
                  }}
                  onMouseEnter={e => { e.currentTarget.style.borderColor = 'var(--accent)'; e.currentTarget.style.color = 'var(--text)' }}
                  onMouseLeave={e => { e.currentTarget.style.borderColor = 'var(--border2)'; e.currentTarget.style.color = 'var(--text2)' }}
                >
                  {s}
                </button>
              ))}
            </div>
          </div>
        ) : (
          <>
            {conversation.messages.map(msg => <Message key={msg.id} msg={msg} />)}
            <div ref={bottomRef} />
          </>
        )}
      </div>

      <div style={{
        padding: '12px 16px 16px',
        borderTop: '1px solid var(--border)',
        background: 'var(--bg)',
        flexShrink: 0,
      }}>
        <div style={{
          display: 'flex',
          alignItems: 'flex-end',
          gap: 10,
          background: 'var(--bg2)',
          border: '1px solid var(--border2)',
          borderRadius: 16,
          padding: '10px 12px 10px 16px',
          transition: 'border-color 0.15s',
        }}
          onFocusCapture={e => (e.currentTarget.style.borderColor = 'var(--accent)')}
          onBlurCapture={e => (e.currentTarget.style.borderColor = 'var(--border2)')}
        >
          <textarea
            ref={textareaRef}
            value={input}
            onChange={handleInput}
            onKeyDown={onKeyDown}
            rows={rows}
            placeholder="Message Claude... (Enter to send, Shift+Enter for new line)"
            style={{
              flex: 1,
              resize: 'none',
              background: 'transparent',
              color: 'var(--text)',
              fontSize: 14,
              lineHeight: 1.6,
              maxHeight: 200,
              overflowY: 'auto',
            }}
          />
          <button
            onClick={submit}
            disabled={!input.trim()}
            style={{
              width: 34, height: 34,
              borderRadius: 10,
              background: input.trim() ? 'var(--accent)' : 'var(--bg4)',
              color: input.trim() ? '#fff' : 'var(--text3)',
              display: 'flex', alignItems: 'center', justifyContent: 'center',
              fontSize: 16, flexShrink: 0,
              transition: 'all 0.15s',
              transform: input.trim() ? 'scale(1)' : 'scale(0.95)',
            }}
          >↑</button>
        </div>
        <div style={{ marginTop: 6, textAlign: 'center', fontSize: 11, color: 'var(--text3)' }}>
          Claude Code Web · Local AI Agent
        </div>
      </div>
    </div>
  )
}
