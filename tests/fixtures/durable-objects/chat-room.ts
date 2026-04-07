interface ChatMessage { id: string; userId: string; content: string; timestamp: number }

export class ChatRoomDO {
  private state: DurableObjectState;
  private sessions: Map<string, { userId: string; socket: WebSocket }> = new Map();
  private messages: ChatMessage[] = [];
  private nextId = 0;
  constructor(state: DurableObjectState, env: Env) {
    this.state = state;
    this.state.blockConcurrencyWhile(async () => {
      this.messages = await this.state.storage.get<ChatMessage[]>("messages") ?? [];
      this.nextId   = await this.state.storage.get<number>("nextId") ?? 0;
    });
  }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/history" && request.method === "GET") {
      return new Response(JSON.stringify({ messages: this.messages }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
  async webSocketMessage(ws: WebSocket, message: string): Promise<void> {
    const tags = this.state.getTags(ws);
    const sessionId = tags[0];
    const session = this.sessions.get(sessionId);
    if (!session) return;
    let data: { type: string; content?: string };
    try { data = JSON.parse(message); } catch { ws.send(JSON.stringify({ error: "invalid" })); return; }
    if (data.type === "message" && data.content) {
      const msg: ChatMessage = { id: `msg_${this.nextId++}`, userId: session.userId, content: data.content, timestamp: Date.now() };
      this.messages.push(msg);
      if (this.messages.length > 1000) this.messages = this.messages.slice(-1000);
      await this.state.storage.put("messages", this.messages);
      await this.state.storage.put("nextId", this.nextId);
      this.broadcast(JSON.stringify({ type: "message", message: msg }), sessionId);
    }
  }
  private broadcast(message: string, excludeId?: string): void {
    for (const [id, session] of this.sessions) {
      if (id !== excludeId) { try { session.socket.send(message); } catch { this.sessions.delete(id); } }
    }
  }
}
