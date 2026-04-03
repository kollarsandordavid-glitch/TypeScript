import React, { useState } from 'react'
import { ChatMessage } from '../hooks/useWebSocket'

interface Props { msg: ChatMessage }

function ToolCallBlock({ msg }: Props) {
  const [open, setOpen] = useState(false)
  let inputStr = ''
  try { inputStr = JSON.stringify(msg.toolInput, null, 2) } catch { inputStr = String(msg.toolInput) }

  return (
    <div style={{ margin: '4px 0', background: '#0d1117', border: '1px solid #1e2d3d', borderRadius: 8, overflow: 'hidden', fontSize: 12 }}>
      <button
        onClick={() => setOpen(v => !v)}
        style={{
          width: '100%', padding: '7px 12px', display: 'flex', alignItems: 'center', gap: 8,
          background: 'transparent', color: '#58a6ff', fontFamily: 'var(--mono)', fontWeight: 600, fontSize: 11,
          textAlign: 'left', cursor: 'pointer',
        }}
      >
        <span style={{ fontSize: 9, opacity: 0.7 }}>▶</span>
        <span style={{ flex: 1 }}>{msg.toolName}</span>
        <span style={{ opacity: 0.4, fontSize: 10, fontFamily: 'inherit' }}>{open ? '▲' : '▼'}</span>
      </button>
      {open && inputStr && (
        <pre style={{ padding: '8px 14px', color: '#8b949e', fontSize: 11, overflowX: 'auto', borderTop: '1px solid #1e2d3d', margin: 0, lineHeight: 1.5 }}>
          {inputStr}
        </pre>
      )}
    </div>
  )
}

function ToolResultBlock({ msg }: Props) {
  const [open, setOpen] = useState(false)
  const lines = msg.content.split('\n')
  const preview = lines.slice(0, 3).join('\n')
  const hasMore = lines.length > 3

  return (
    <div style={{ margin: '2px 0 6px 0', background: '#0a0f0a', border: `1px solid ${msg.isError ? '#3d1e1e' : '#1a2d1a'}`, borderRadius: 8, overflow: 'hidden', fontSize: 12 }}>
      <button
        onClick={() => setOpen(v => !v)}
        style={{
          width: '100%', padding: '6px 12px', display: 'flex', alignItems: 'center', gap: 8,
          background: 'transparent', color: msg.isError ? '#f87171' : '#4ade80',
          fontFamily: 'var(--mono)', fontWeight: 500, fontSize: 10, textAlign: 'left', cursor: 'pointer',
        }}
      >
        <span>{msg.isError ? '✗' : '✓'}</span>
        <span style={{ flex: 1 }}>output</span>
        {hasMore && <span style={{ opacity: 0.4, fontSize: 10 }}>{open ? 'collapse' : `${lines.length} lines`}</span>}
      </button>
      {msg.content && (
        <pre style={{
          padding: '6px 14px 10px', color: '#6e7681', fontSize: 11, overflowX: 'auto',
          borderTop: `1px solid ${msg.isError ? '#2d1a1a' : '#1a2d1a'}`, margin: 0, lineHeight: 1.5,
          maxHeight: open ? 400 : 80, overflow: open ? 'auto' : 'hidden',
          transition: 'max-height 0.2s',
        }}>
          {open ? msg.content : preview}
          {!open && hasMore && <span style={{ color: '#58a6ff' }}> ...show more</span>}
        </pre>
      )}
    </div>
  )
}

function ThinkingBlock({ msg }: Props) {
  const [open, setOpen] = useState(false)
  return (
    <div style={{ margin: '4px 0', background: '#0d0d14', border: '1px solid #1e1e35', borderRadius: 8, overflow: 'hidden', fontSize: 12 }}>
      <button
        onClick={() => setOpen(v => !v)}
        style={{
          width: '100%', padding: '7px 12px', display: 'flex', alignItems: 'center', gap: 8,
          background: 'transparent', color: '#a78bfa', fontFamily: 'inherit', fontWeight: 500, fontSize: 11,
          textAlign: 'left', cursor: 'pointer',
        }}
      >
        <span style={{ animation: msg.streaming ? 'pulse 1.5s infinite' : 'none' }}>💭</span>
        <span style={{ flex: 1 }}>Thinking{msg.streaming ? '...' : ''}</span>
        <span style={{ opacity: 0.4, fontSize: 10 }}>{open ? '▲' : '▼'}</span>
      </button>
      {open && (
        <pre style={{ padding: '8px 14px', color: '#7c6dab', fontSize: 11, overflowX: 'auto', borderTop: '1px solid #1e1e35', margin: 0, lineHeight: 1.6, whiteSpace: 'pre-wrap', wordBreak: 'break-word' }}>
          {msg.content}
        </pre>
      )}
    </div>
  )
}

export function Message({ msg }: Props) {
  if (msg.role === 'thinking') return <ThinkingBlock msg={msg} />
  if (msg.role === 'tool_call') return <ToolCallBlock msg={msg} />
  if (msg.role === 'tool_result') return <ToolResultBlock msg={msg} />

  if (msg.role === 'error') {
    return (
      <div style={{ margin: '4px 0', padding: '9px 14px', background: 'rgba(248,113,113,0.07)', border: '1px solid rgba(248,113,113,0.2)', borderRadius: 8, color: '#f87171', fontSize: 13, display: 'flex', gap: 8 }}>
        <span>⚠</span><span>{msg.content}</span>
      </div>
    )
  }

  if (msg.role === 'system') {
    return (
      <div style={{ margin: '4px 0', padding: '5px 12px', color: 'var(--text3)', fontSize: 11, fontFamily: 'var(--mono)', display: 'flex', gap: 6, alignItems: 'center' }}>
        <span>ℹ</span><span>{msg.content}</span>
      </div>
    )
  }

  if (msg.role === 'result') {
    return (
      <div style={{ margin: '6px 0', padding: '5px 12px', color: 'var(--text3)', fontSize: 11, display: 'flex', gap: 6, alignItems: 'center', borderTop: '1px solid var(--border)' }}>
        <span>💰</span><span>{msg.content}</span>
      </div>
    )
  }

  if (msg.role === 'user') {
    return (
      <div style={{ display: 'flex', justifyContent: 'flex-end', margin: '8px 0' }}>
        <div style={{
          maxWidth: '75%', padding: '10px 16px',
          background: 'var(--bg3)', border: '1px solid var(--border2)',
          borderRadius: '18px 18px 4px 18px',
          fontSize: 14, lineHeight: 1.6, whiteSpace: 'pre-wrap', wordBreak: 'break-word',
        }}>{msg.content}</div>
      </div>
    )
  }

  // assistant
  return (
    <div style={{ display: 'flex', gap: 12, margin: '8px 0', alignItems: 'flex-start' }}>
      <div style={{
        width: 28, height: 28, borderRadius: 8, background: 'var(--accent)',
        display: 'flex', alignItems: 'center', justifyContent: 'center',
        fontSize: 13, fontWeight: 700, color: '#fff', flexShrink: 0, marginTop: 2,
      }}>C</div>
      <div style={{ flex: 1, fontSize: 14, lineHeight: 1.7, whiteSpace: 'pre-wrap', wordBreak: 'break-word', paddingTop: 4 }}>
        {msg.content}
        {msg.streaming && (
          <span style={{ display: 'inline-block', width: 2, height: 16, background: 'var(--accent)', marginLeft: 2, verticalAlign: 'text-bottom', animation: 'blink 1s step-end infinite' }} />
        )}
      </div>
    </div>
  )
}
