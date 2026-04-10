# Claude Code — Replit Project Guide

## Overview

This is **Claude Code**, an AI-powered coding assistant CLI application built by Anthropic. It functions as an interactive terminal-based REPL that integrates with Claude (Anthropic's AI model) to help users write, edit, debug, and manage code projects. The system supports both interactive use (via a terminal UI) and programmatic use through an Agent SDK.

Key capabilities:
- AI-powered code generation, editing, and review through Claude models
- A rich set of built-in tools (Bash, file read/write/edit, glob search, web fetch, notebook editing)
- Remote Control ("bridge") mode — connects the local CLI session to the claude.ai web app for remote pair-programming
- Multi-agent and swarm execution with task scheduling
- MCP (Model Context Protocol) server integration for third-party tool extensions
- Session history, memory (CLAUDE.md), and cost tracking
- Feature-flagged experimental capabilities via GrowthBook

## User Preferences

Preferred communication style: Simple, everyday language.

## System Architecture

### Web Frontend (PWA)
- **React + Vite PWA** in `frontend/` — dark-themed, native-feeling chat interface
- **Build output**: `public/` directory, served by `webserver.ts`
- **Components**: `App.tsx`, `ChatWindow.tsx`, `Message.tsx`, `Sidebar.tsx`
- **State management**: `useWebSocket.ts` hook with refs for stable WebSocket callbacks, React state for UI updates
- **Message types displayed**: user, assistant (streaming), thinking (collapsible), tool_call (expandable with input), tool_result (with error styling), error, system
- **Connection**: WebSocket to `/ws` with auto-reconnect (2s), heartbeat ping every 20s
- **Build command**: `cd frontend && npm run build`

### Original Terminal UI
- **Terminal UI**: Built with [Ink](https://github.com/vadimdemedes/ink) (React for CLIs), wrapped in a custom `ThemeProvider` so all components share a consistent design system (ThemedBox, ThemedText).
- **React 19**: The entire interactive REPL is a React component tree rendered inside an Ink root. Dialog screens (onboarding, settings, resume) are dynamically imported to reduce startup cost.
- **Entry point**: `main.tsx` — bootstraps the CLI, parses arguments via Commander.js, and delegates to `launchRepl()` / dialog launchers. Side-effects (keychain prefetch, MDM read, startup profiling) are fired as early as possible for parallel execution.
- **Startup optimization**: `startupProfiler`, `keychainPrefetch`, and `startMdmRawRead` run before the module graph is fully evaluated to minimize time-to-interactive.
- **Dialog launchers** (`dialogLaunchers.tsx`): Thin async wrappers that dynamically import heavy dialog components only when needed.

### Backend / Core Architecture
- **Runtime**: Bun (primary) with Node.js compatibility. ESM modules throughout (`"type": "module"`).
- **TypeScript**: Strict mode, ESNext target, no emitted output (type-checking only; Bun handles execution).
- **Query engine** (`query.ts`, `QueryEngine.ts`): Drives the agentic loop — sends messages to Claude, handles tool use responses, manages context compaction, and streams results back.
- **Tool system** (`Tool.ts`, `tools.ts`): Extensible tool registry. Core tools: Bash, FileRead, FileWrite, FileEdit, Glob, WebFetch, NotebookEdit, AgentTool, SkillTool. Ant-internal and feature-flagged tools loaded conditionally via `process.env.USER_TYPE` and `feature()` (Bun bundle flags).
- **Task system** (`Task.ts`, `tasks.ts`): Async task execution for local shell commands, local/remote agent spawning, workflow scripts, and monitoring. Tasks have lifecycle states (`pending → running → completed/failed/killed`).
- **Command system** (`commands.ts`): Slash commands (e.g., `/commit`, `/review`, `/mcp`, `/session`) registered and dispatched from the REPL.
- **Context** (`context.ts`): Assembles the system prompt — git status, CLAUDE.md memory files, user context — with memoization to avoid re-computation.
- **State** (`bootstrap/state.ts`): Centralized global state singleton (session ID, project root, cost counters, model usage, OpenTelemetry references). Kept deliberately minimal.

### Remote Control / Bridge Architecture
The `bridge/` directory is a substantial subsystem for the Remote Control feature:
- **Purpose**: Connects the local Claude Code CLI to the claude.ai web app so users can interact remotely.
- **Two bridge modes**:
  - *Env-based (v1)* (`replBridge.ts`): Uses the Environments API (poll → dispatch → work loop) with a HybridTransport (WebSocket reads + HTTP POST writes).
  - *Env-less (v2)* (`remoteBridgeCore.ts`): Bypasses the Environments API; connects directly to a Session-Ingress JWT via CCRClient (SSE reads + CCR v2 writes). Gated by `tengu_bridge_repl_v2` GrowthBook flag.
- **Multi-session bridge** (`bridgeMain.ts`): Manages multiple concurrent remote sessions (one per spawned CLI child process).
- **Transport layer** (`replBridgeTransport.ts`): Abstraction over v1 (HybridTransport) and v2 (SSETransport + CCRClient) so `replBridge.ts` is transport-agnostic.
- **Reliability features**: Poll interval tuning via GrowthBook (`pollConfig.ts`), JWT refresh scheduling (`jwtUtils.ts`), crash-recovery pointer (`bridgePointer.ts`), capacity-wake primitive (`capacityWake.ts`), flush gate for message ordering during session init (`flushGate.ts`), and fault injection for testing (`bridgeDebug.ts`).
- **Security**: Bridge IDs validated against a safe-character allowlist before URL interpolation; secrets redacted from debug logs (`debugUtils.ts`).

### Data Storage
- **No database**: All persistence is file-based.
- **Session history**: Stored as JSONL files on disk, keyed by session/project ID. Large paste content is stored in a paste store with hash references.
- **Configuration**: Global config (`~/.claude/`) and per-project config files, read/written via `utils/config.ts`. Settings can come from files, environment variables, or remote managed settings (MDM/GrowthBook).
- **Memory (CLAUDE.md)**: Markdown files at project root and in `~/.claude/` that inject persistent instructions into the system prompt.
- **Session storage**: Session metadata, bridge pointers, and worktree state stored in `~/.claude/projects/`.

### Authentication & Authorization
- **Primary auth**: OAuth 2.0 via claude.ai (tokens stored in OS keychain on macOS, file on Linux). `utils/auth.ts` handles token retrieval, refresh, and 401 recovery.
- **API key fallback**: Direct Anthropic API key (env var or keychain) for non-OAuth use cases.
- **Bridge auth**: OAuth token used to authenticate bridge sessions with CCR. Trusted device tokens add an elevated security tier.
- **Permission system**: Tools request permission via a `CanUseToolFn` hook. Permission modes (auto-approve, require confirmation, deny) are configurable per tool and per project. Remote Control sessions can forward permission requests to the web UI for user approval.

### Feature Flagging
- **GrowthBook** (`services/analytics/growthbook.ts`): Runtime A/B testing and feature flags. Cached disk values for startup speed; async refresh in background.
- **Build-time flags**: `feature('FLAG_NAME')` from `bun:bundle` — dead-code-eliminates entire code paths at build time for external (non-Anthropic) releases.

### Analytics & Observability
- **Analytics**: Custom event logging (`services/analytics/index.ts`), Datadog integration, first-party event logger.
- **OpenTelemetry**: Tracing, metrics, and logs wiring in `bootstrap/state.ts` for the ant-internal build.
- **Cost tracking** (`cost-tracker.ts`): Tracks token usage and USD cost per session, per model, and accumulates totals.

## External Dependencies

### AI / LLM
- **`@anthropic-ai/sdk`** (v0.81): Primary SDK for calling Claude models. Used for message streaming, tool use, and usage tracking.
- **`openai`** (v6.34): Used in `webserver.ts` with OpenRouter as the base URL — provides an alternative LLM backend (model: `minimax/minimax-m2.5:free` via OpenRouter).
- **OpenRouter** (`https://openrouter.ai/api/v1`): LLM proxy used by the web backend. Requires `OPENROUTER_API_KEY` env var.

### Protocol / Integration
- **`@modelcontextprotocol/sdk`** (v1.29): MCP client for connecting to external tool servers. Enables third-party tool extensions.
- **`ws`** (v8.20): WebSocket library for bridge transport (server-side WebSocketServer in `webserver.ts` and client-side in bridge transports).
- **`axios`**: HTTP client used throughout the bridge subsystem for API calls to CCR and the Anthropic backend.
- **GrowthBook**: Feature flag and A/B testing service (SDK integrated, remote config fetched at startup).

### CLI & UI
- **`@commander-js/extra-typings`** (v14): CLI argument parsing with full TypeScript types.
- **`react`** (v19) + **Ink**: React-based terminal UI framework.
- **`chalk`** (v5): Terminal color output.
- **`strip-ansi`** (v7): Strips ANSI escape codes for log sanitization.
- **`qrcode`**: QR code generation for bridge connect URLs displayed in the terminal.

### Utilities
- **`lodash-es`** (v4): Utility functions (memoize, last, mapValues, etc.) — ES module build.
- **`zod`** (v4): Schema validation and type inference used extensively for config, bridge messages, and API responses.
- **`node-fetch`** (v3): Fetch polyfill for Node.js environments.

### Build & Dev
- **Bun**: Primary runtime and bundler. `bun:bundle` feature flags control dead-code elimination for external builds.
- **`tsx`** (v4): TypeScript execution for development.
- **`vite`** (v8) + **`@vitejs/plugin-react`**: Bundler for the React PWA frontend (`public/` directory served by `webserver.ts`).
- **`@types/node`**, **`@types/ws`**: TypeScript type definitions.

### Anthropic Backend Services
- **CCR (Claude Code Remote)**: Anthropic's backend for Remote Control sessions — session ingress, SSE transport, worker JWT issuance.
- **Anthropic API** (`BASE_API_URL` from OAuth config): Session management, file uploads, policy limits, managed settings, and referral prefetch.
- **Keychain / MDM**: macOS Keychain and Windows/MDM registry for secure credential and policy storage.