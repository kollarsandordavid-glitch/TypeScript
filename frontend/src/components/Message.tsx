import React from 'react'
import { ChatMessage } from '../hooks/useWebSocket'

interface Props {
  msg: ChatMessage
}

export function Message({ msg }: Props) {
  if (msg.role === 'tool') {
    return (
      <div style={{
        margin: '4px 0',
        background: 'var(--tool-bg)',
        border: '1px solid var(--tool-border)',
        borderRadius: 'var(--radius-sm)',
        overflow: 'hidden',
        fontSize: 12,
      }}>
        <div style={{
          padding: '6px 12px',
          borderBottom: '1px solid var(--tool-border)',
          display: 'flex',
          alignItems: 'center',
          gap: 6,
          color: 'var(--blue)',
          fontFamily: 'var(--mono)',
          fontWeight: 600,
          fontSize: 11,
        }}>
          <span style={{ opacity: 0.6 }}>▶</span>
          {msg.toolName ?? 'tool'}
        </div>
        <pre style={{
          padding: '10px 14px',
          overflowX: 'auto',
          color: 'var(--text2)',
          lineHeight: 1.5,
          fontSize: 12,
          margin: 0,
        }}>{msg.content}</pre>
      </div>
    )
  }

  if (msg.role === 'error') {
    return (
      <div style={{
        margin: '4px 0',
        padding: '10px 14px',
        background: 'rgba(248,113,113,0.08)',
        border: '1px solid rgba(248,113,113,0.2)',
        borderRadius: 'var(--radius-sm)',
        color: 'var(--red)',
        fontSize: 13,
        display: 'flex',
        alignItems: 'center',
        gap: 8,
      }}>
        <span>⚠</span>
        {msg.content}
      </div>
    )
  }

  if (msg.role === 'user') {
    return (
      <div style={{ display: 'flex', justifyContent: 'flex-end', margin: '6px 0' }}>
        <div style={{
          maxWidth: '75%',
          padding: '10px 16px',
          background: 'var(--bg3)',
          border: '1px solid var(--border2)',
          borderRadius: '18px 18px 4px 18px',
          color: 'var(--text)',
          fontSize: 14,
          lineHeight: 1.6,
          whiteSpace: 'pre-wrap',
          wordBreak: 'break-word',
        }}>
          {msg.content}
        </div>
      </div>
    )
  }

  return (
    <div style={{ display: 'flex', gap: 12, margin: '6px 0', alignItems: 'flex-start' }}>
      <div style={{
        width: 28, height: 28, borderRadius: 8,
        background: 'var(--accent)',
        display: 'flex', alignItems: 'center', justifyContent: 'center',
        fontSize: 13, fontWeight: 700, color: '#fff',
        flexShrink: 0, marginTop: 2,
      }}>C</div>
      <div style={{
        flex: 1,
        color: 'var(--text)',
        fontSize: 14,
        lineHeight: 1.7,
        whiteSpace: 'pre-wrap',
        wordBreak: 'break-word',
        paddingTop: 4,
      }}>
        {msg.content}
        {msg.streaming && (
          <span style={{
            display: 'inline-block',
            width: 2, height: 16,
            background: 'var(--accent)',
            marginLeft: 2,
            verticalAlign: 'text-bottom',
            animation: 'blink 1s step-end infinite',
          }} />
        )}
      </div>
    </div>
  )
}
