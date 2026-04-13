// Chat room with WebSocket Hibernation API
export class ChatRoom extends DurableObject {
  async fetch(request: Request): Promise<Response> {
    const pair = new WebSocketPair();
    const url = new URL(request.url);
    const room = url.pathname.slice(1) || "default";
    this.ctx.acceptWebSocket(pair[1], [room]);
    return new Response(null, { status: 101, webSocket: pair[0] });
  }

  async webSocketMessage(ws: WebSocket, message: string): Promise<void> {
    const tags = this.ctx.getTags(ws);
    if (tags.length > 0) {
      const peers = this.ctx.getWebSockets(tags[0]);
      for (const peer of peers) {
        peer.send(message);
      }
    }
  }

  async webSocketClose(ws: WebSocket, code: number, reason: string, wasClean: boolean): Promise<void> {
    ws.close(code, reason);
  }
}
