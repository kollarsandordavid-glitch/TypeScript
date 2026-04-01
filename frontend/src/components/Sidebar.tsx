import React from 'react'
import { Conversation } from '../hooks/useWebSocket'

interface Props {
  conversations: Conversation[]
  activeId: string | null
  onSelect: (id: string) => void
  onNew: () => void
  open: boolean
  onClose: () => void
}

export function Sidebar({ conversations, activeId, onSelect, onNew, open, onClose }: Props) {
  return (
    <>
      {open && (
        <div
          style={{
            position: 'fixed', inset: 0, background: 'rgba(0,0,0,0.5)',
            zIndex: 40, display: 'none',
          }}
          className="sidebar-overlay"
          onClick={onClose}
        />
      )}
      <aside
        style={{
          width: 260,
          minWidth: 260,
          height: '100%',
          background: 'var(--bg2)',
          borderRight: '1px solid var(--border)',
          display: 'flex',
          flexDirection: 'column',
          flexShrink: 0,
          transition: 'transform 0.25s cubic-bezier(.4,0,.2,1)',
        }}
      >
        <div style={{
          padding: '16px 12px 12px',
          borderBottom: '1px solid var(--border)',
          display: 'flex',
          alignItems: 'center',
          gap: 8,
        }}>
          <div style={{
            width: 28, height: 28, borderRadius: 8,
            background: 'var(--accent)',
            display: 'flex', alignItems: 'center', justifyContent: 'center',
            fontSize: 14, fontWeight: 700, color: '#fff', flexShrink: 0,
          }}>C</div>
          <span style={{ fontWeight: 600, fontSize: 14, color: 'var(--text)' }}>Claude Code</span>
        </div>

        <button
          onClick={onNew}
          style={{
            margin: '10px 10px 6px',
            padding: '9px 14px',
            background: 'var(--bg3)',
            border: '1px solid var(--border2)',
            borderRadius: 'var(--radius-sm)',
            color: 'var(--text)',
            fontSize: 13,
            fontWeight: 500,
            display: 'flex',
            alignItems: 'center',
            gap: 8,
            transition: 'background 0.15s',
          }}
          onMouseEnter={e => (e.currentTarget.style.background = 'var(--bg4)')}
          onMouseLeave={e => (e.currentTarget.style.background = 'var(--bg3)')}
        >
          <span style={{ fontSize: 16, opacity: 0.7 }}>＋</span>
          New conversation
        </button>

        <div style={{ flex: 1, overflowY: 'auto', padding: '4px 6px' }}>
          {conversations.length === 0 && (
            <div style={{ padding: '20px 12px', color: 'var(--text3)', fontSize: 12, textAlign: 'center' }}>
              No conversations yet
            </div>
          )}
          {conversations.map(c => (
            <button
              key={c.id}
              onClick={() => onSelect(c.id)}
              style={{
                width: '100%',
                padding: '9px 12px',
                borderRadius: 'var(--radius-sm)',
                background: c.id === activeId ? 'var(--bg4)' : 'transparent',
                color: c.id === activeId ? 'var(--text)' : 'var(--text2)',
                fontSize: 13,
                textAlign: 'left',
                overflow: 'hidden',
                textOverflow: 'ellipsis',
                whiteSpace: 'nowrap',
                display: 'block',
                marginBottom: 2,
                borderLeft: c.id === activeId ? '2px solid var(--accent)' : '2px solid transparent',
                transition: 'all 0.12s',
              }}
              onMouseEnter={e => { if (c.id !== activeId) e.currentTarget.style.background = 'var(--bg3)' }}
              onMouseLeave={e => { if (c.id !== activeId) e.currentTarget.style.background = 'transparent' }}
            >
              {c.title || 'Untitled'}
            </button>
          ))}
        </div>

        <div style={{
          padding: '10px 12px',
          borderTop: '1px solid var(--border)',
          display: 'flex',
          alignItems: 'center',
          gap: 8,
        }}>
          <div style={{
            width: 28, height: 28, borderRadius: '50%',
            background: 'var(--bg4)',
            display: 'flex', alignItems: 'center', justifyContent: 'center',
            fontSize: 13, color: 'var(--text2)',
          }}>U</div>
          <div>
            <div style={{ fontSize: 12, fontWeight: 500 }}>User</div>
            <div style={{ fontSize: 11, color: 'var(--text3)' }}>Local session</div>
          </div>
        </div>
      </aside>
    </>
  )
}
