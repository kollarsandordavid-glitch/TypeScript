import React, { useState } from 'react'
import { Sidebar } from './components/Sidebar'
import { ChatWindow } from './components/ChatWindow'
import { useWebSocket } from './hooks/useWebSocket'

export default function App() {
  const { status, serverInfo, conversations, activeId, setActiveId, getActive, newConversation, sendMessage, interrupt } = useWebSocket()
  const [sidebar, setSidebar] = useState(true)

  return (
    <div style={{ display: 'flex', height: '100%', width: '100%', overflow: 'hidden', background: 'var(--bg)' }}>
      <style>{`
        @keyframes blink { 0%,100%{opacity:1} 50%{opacity:0} }
        @keyframes pulse { 0%,100%{opacity:1} 50%{opacity:0.3} }
        @keyframes fadeIn { from{opacity:0;transform:translateY(4px)} to{opacity:1;transform:translateY(0)} }
      `}</style>

      {sidebar && (
        <Sidebar
          conversations={conversations}
          activeId={activeId}
          onSelect={setActiveId}
          onNew={newConversation}
          open={sidebar}
          onClose={() => setSidebar(false)}
          serverInfo={serverInfo}
        />
      )}

      <ChatWindow
        conversation={getActive()}
        onSend={sendMessage}
        onInterrupt={interrupt}
        status={status}
        serverInfo={serverInfo}
        onMenuToggle={() => setSidebar(v => !v)}
      />
    </div>
  )
}
