import React, { useState } from 'react'
import { ChatMessage } from '../hooks/useWebSocket'

interface Props { msg: ChatMessage }

function ToolCall({ msg }: Props) {
  const [open, setOpen] = useState(true)
  return (
    <div style={{ margin: '4px 0', background: '#0d1117', border: '1px solid #1e2d3d', borderRadius: 8, overflow: 'hidden', fontSize: 12, animation: 'fadeIn 0.2s ease' }}>
      <button onClick={() => setOpen(v => !v)} style={{
        width: '100%', padding: '8px 12px', display: 'flex', alignItems: 'center', gap: 8,
        background: '#161b22', color: '#58a6ff', fontFamily: 'var(--mono)', fontWeight: 600, fontSize: 12,
        textAlign: 'left', cursor: 'pointer', borderBottom: open ? '1px solid #1e2d3d' : 'none',
      }}>
        <span style={{ color: '#f0883e' }}>⚡</span>
        <span style={{ flex: 1 }}>{msg.toolName || 'tool'}</span>
        <span style={{ opacity: 0.4, fontSize: 10 }}>{open ? '▲' : '▼'}</span>
      </button>
      {open && msg.content && (
        <pre style={{ padding: '8px 14px', color: '#8b949e', fontSize: 11, overflowX: 'auto', margin: 0, lineHeight: 1.5, maxHeight: 200, overflow: 'auto' }}>
          {msg.content}
        </pre>
      )}
    </div>
  )
}

function ToolResult({ msg }: Props) {
  const [open, setOpen] = useState(false)
  const lines = msg.content.split('\n')
  const preview = lines.slice(0, 4).join('\n')
  const hasMore = lines.length > 4

  return (
    <div style={{ margin: '2px 0 6px 0', background: msg.isError ? '#1a0f0f' : '#0a0f0a', border: `1px solid ${msg.isError ? '#3d1e1e' : '#1a2d1a'}`, borderRadius: 8, overflow: 'hidden', fontSize: 12, animation: 'fadeIn 0.2s ease' }}>
      <button onClick={() => setOpen(v => !v)} style={{
        width: '100%', padding: '6px 12px', display: 'flex', alignItems: 'center', gap: 6,
        background: 'transparent', color: msg.isError ? '#f87171' : '#4ade80',
        fontFamily: 'var(--mono)', fontWeight: 500, fontSize: 11, textAlign: 'left', cursor: 'pointer',
      }}>
        <span>{msg.isError ? '✗' : '✓'}</span>
        <span style={{ flex: 1 }}>{msg.toolName ? `${msg.toolName} output` : 'output'}</span>
        {hasMore && <span style={{ opacity: 0.4, fontSize: 10 }}>{open ? 'collapse' : `${lines.length} lines`}</span>}
      </button>
      {msg.content && (
        <pre style={{
          padding: '6px 14px 10px', color: msg.isError ? '#fca5a5' : '#6e7681', fontSize: 11, overflowX: 'auto',
          borderTop: `1px solid ${msg.isError ? '#2d1a1a' : '#1a2d1a'}`, margin: 0, lineHeight: 1.5,
          maxHeight: open ? 400 : 80, overflow: open ? 'auto' : 'hidden', transition: 'max-height 0.2s',
        }}>
          {open ? msg.content : preview}
          {!open && hasMore && <span style={{ color: '#58a6ff', cursor: 'pointer' }}> ...show all</span>}
        </pre>
      )}
    </div>
  )
}

function Thinking({ msg }: Props) {
  const [open, setOpen] = useState(false)
  return (
    <div style={{ margin: '4px 0', background: '#0d0d14', border: '1px solid #1e1e35', borderRadius: 8, overflow: 'hidden', fontSize: 12, animation: 'fadeIn 0.2s ease' }}>
      <button onClick={() => setOpen(v => !v)} style={{
        width: '100%', padding: '7px 12px', display: 'flex', alignItems: 'center', gap: 8,
        background: 'transparent', color: '#a78bfa', fontWeight: 500, fontSize: 11,
        textAlign: 'left', cursor: 'pointer',
      }}>
        <span style={{ animation: msg.streaming ? 'pulse 1.5s infinite' : 'none' }}>💭</span>
        <span style={{ flex: 1 }}>Thinking{msg.streaming ? '...' : ''}</span>
        <span style={{ opacity: 0.4, fontSize: 10 }}>{open ? '▲' : '▼'}</span>
      </button>
      {open && (
        <pre style={{ padding: '8px 14px', color: '#7c6dab', fontSize: 11, borderTop: '1px solid #1e1e35', margin: 0, lineHeight: 1.6, whiteSpace: 'pre-wrap', wordBreak: 'break-word', maxHeight: 300, overflow: 'auto' }}>
          {msg.content}
        </pre>
      )}
    </div>
  )
}

export function Message({ msg }: Props) {
  if (msg.role === 'thinking') return <Thinking msg={msg} />
  if (msg.role === 'tool_call') return <ToolCall msg={msg} />
  if (msg.role === 'tool_result') return <ToolResult msg={msg} />

  if (msg.role === 'error') return (
    <div style={{ margin: '4px 0', padding: '9px 14px', background: 'rgba(248,113,113,0.08)', border: '1px solid rgba(248,113,113,0.2)', borderRadius: 8, color: '#f87171', fontSize: 13, display: 'flex', gap: 8, animation: 'fadeIn 0.2s ease' }}>
      <span>⚠</span><span style={{ flex: 1 }}>{msg.content}</span>
    </div>
  )

  if (msg.role === 'system' || msg.role === 'stderr' || msg.role === 'result') return (
    <div style={{ margin: '3px 0', padding: '4px 12px', color: '#555', fontSize: 11, fontFamily: 'var(--mono)', display: 'flex', gap: 6, opacity: 0.7 }}>
      <span>{msg.role === 'stderr' ? '⚙' : 'ℹ'}</span><span>{msg.content}</span>
    </div>
  )

  if (msg.role === 'user') return (
    <div style={{ display: 'flex', justifyContent: 'flex-end', margin: '8px 0', animation: 'fadeIn 0.15s ease' }}>
      <div style={{
        maxWidth: '80%', padding: '10px 16px', background: '#1a1a2e', border: '1px solid #2a2a4a',
        borderRadius: '18px 18px 4px 18px', fontSize: 14, lineHeight: 1.6, whiteSpace: 'pre-wrap', wordBreak: 'break-word',
      }}>{msg.content}</div>
    </div>
  )

  return (
    <div style={{ display: 'flex', gap: 10, margin: '8px 0', alignItems: 'flex-start', animation: 'fadeIn 0.15s ease' }}>
      <div style={{
        width: 26, height: 26, borderRadius: 7, background: '#cc785c',
        display: 'flex', alignItems: 'center', justifyContent: 'center',
        fontSize: 12, fontWeight: 700, color: '#fff', flexShrink: 0, marginTop: 3,
      }}>AI</div>
      <div style={{ flex: 1, fontSize: 14, lineHeight: 1.7, whiteSpace: 'pre-wrap', wordBreak: 'break-word', paddingTop: 2 }}>
        {msg.content}
        {msg.streaming && <span style={{ display: 'inline-block', width: 2, height: 16, background: '#cc785c', marginLeft: 2, verticalAlign: 'text-bottom', animation: 'blink 1s step-end infinite' }} />}
      </div>
    </div>
  )
}
