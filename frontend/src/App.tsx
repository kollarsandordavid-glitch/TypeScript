import React, { useState } from 'react'
import { Sidebar } from './components/Sidebar'
import { ChatWindow } from './components/ChatWindow'
import { useWebSocket } from './hooks/useWebSocket'

export default function App() {
  const { status, conversations, activeId, setActiveId, getActive, newConversation, sendMessage } = useWebSocket()
  const [sidebarOpen, setSidebarOpen] = useState(true)

  const active = getActive()

  return (
    <div style={{
      display: 'flex',
      height: '100%',
      width: '100%',
      overflow: 'hidden',
      background: 'var(--bg)',
    }}>
      <style>{`
        @keyframes blink {
          0%, 100% { opacity: 1; }
          50% { opacity: 0; }
        }
        @keyframes pulse {
          0%, 100% { opacity: 1; }
          50% { opacity: 0.4; }
        }
        @keyframes fadeIn {
          from { opacity: 0; transform: translateY(6px); }
          to { opacity: 1; transform: translateY(0); }
        }
        .menu-btn:hover { background: var(--bg3) !important; }
        @media (max-width: 600px) {
          aside { position: fixed; left: 0; top: 0; bottom: 0; z-index: 50; transform: translateX(${sidebarOpen ? '0' : '-100%'}); }
        }
      `}</style>

      {sidebarOpen && (
        <Sidebar
          conversations={conversations}
          activeId={activeId}
          onSelect={(id) => { setActiveId(id); if (window.innerWidth < 600) setSidebarOpen(false) }}
          onNew={() => { newConversation(); if (window.innerWidth < 600) setSidebarOpen(false) }}
          open={sidebarOpen}
          onClose={() => setSidebarOpen(false)}
        />
      )}

      <ChatWindow
        conversation={active}
        onSend={sendMessage}
        status={status}
        onMenuOpen={() => setSidebarOpen(v => !v)}
      />
    </div>
  )
}
