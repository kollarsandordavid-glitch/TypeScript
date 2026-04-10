import React from 'react'
import { Conversation } from '../hooks/useWebSocket'

interface Props {
  conversations: Conversation[]
  activeId: string | null
  onSelect: (id: string) => void
  onNew: () => void
  open: boolean
  onClose: () => void
  serverInfo: { model?: string; hasApiKey?: boolean }
}

export function Sidebar({ conversations, activeId, onSelect, onNew, open, onClose, serverInfo }: Props) {
  return (
    <aside style={{
      width: 240, minWidth: 240, height: '100%', background: 'var(--bg2)',
      borderRight: '1px solid var(--border)', display: 'flex', flexDirection: 'column', flexShrink: 0,
    }}>
      <div style={{ padding: '14px 10px 10px', borderBottom: '1px solid var(--border)', display: 'flex', alignItems: 'center', gap: 8 }}>
        <div style={{ width: 26, height: 26, borderRadius: 7, background: '#cc785c', display: 'flex', alignItems: 'center', justifyContent: 'center', fontSize: 11, fontWeight: 700, color: '#fff', flexShrink: 0 }}>AI</div>
        <span style={{ fontWeight: 600, fontSize: 13, color: 'var(--text)' }}>Code Agent</span>
      </div>

      <button onClick={onNew} style={{
        margin: '8px 8px 4px', padding: '8px 12px', background: 'var(--bg3)',
        border: '1px solid var(--border2)', borderRadius: 8, color: 'var(--text)',
        fontSize: 12, fontWeight: 500, display: 'flex', alignItems: 'center', gap: 6,
        transition: 'background 0.15s',
      }}
        onMouseEnter={e => e.currentTarget.style.background = 'var(--bg4)'}
        onMouseLeave={e => e.currentTarget.style.background = 'var(--bg3)'}
      >
        <span style={{ fontSize: 14, opacity: 0.6 }}>＋</span> New chat
      </button>

      <div style={{ flex: 1, overflowY: 'auto', padding: '4px 6px' }}>
        {conversations.length === 0 && (
          <div style={{ padding: '16px 10px', color: 'var(--text3)', fontSize: 11, textAlign: 'center' }}>No conversations</div>
        )}
        {conversations.map(c => (
          <button key={c.id} onClick={() => onSelect(c.id)} style={{
            width: '100%', padding: '7px 10px', borderRadius: 6,
            background: c.id === activeId ? 'var(--bg4)' : 'transparent',
            color: c.id === activeId ? 'var(--text)' : 'var(--text2)',
            fontSize: 12, textAlign: 'left', overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap',
            display: 'flex', alignItems: 'center', gap: 6, marginBottom: 1,
            borderLeft: c.id === activeId ? '2px solid #cc785c' : '2px solid transparent',
            transition: 'all 0.1s',
          }}
            onMouseEnter={e => { if (c.id !== activeId) e.currentTarget.style.background = 'var(--bg3)' }}
            onMouseLeave={e => { if (c.id !== activeId) e.currentTarget.style.background = 'transparent' }}
          >
            {c.loading && <span style={{ width: 4, height: 4, borderRadius: '50%', background: '#cc785c', animation: 'pulse 1s infinite', flexShrink: 0 }} />}
            <span style={{ overflow: 'hidden', textOverflow: 'ellipsis' }}>{c.title}</span>
          </button>
        ))}
      </div>

      <div style={{ padding: '8px 10px', borderTop: '1px solid var(--border)', fontSize: 10, color: 'var(--text3)', fontFamily: 'var(--mono)' }}>
        {serverInfo.model?.split('/').pop() ?? 'no model'}
        <br />
        {serverInfo.hasApiKey ? '🟢 API ready' : '🔴 No API key'}
      </div>
    </aside>
  )
}
