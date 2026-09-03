// ============================================================================
// Durable Object — Chat Room with WebSocket Hibernation
// ============================================================================
//
// Demonstrates the full WebSocket Hibernation API:
//   - WebSocketPair creation
//   - acceptWebSocket with tags for room-based routing
//   - getWebSockets / getTags for peer discovery
//   - webSocketMessage / webSocketClose event handlers
//
// TSLean maps these to the DurableObjects.WebSocket Lean module:
//   - new WebSocketPair()             → WebSocketPair.new
//   - this.ctx.acceptWebSocket(ws, tags) → openConnWithTags state ws tags
//   - this.ctx.getWebSockets(tag)     → getByTag state tag
//   - this.ctx.getTags(ws)            → getTags state ws
//   - ws.send(message)                → WsMessage.text message (in broadcast)
//   - ws.close(code, reason)          → closeConn state ws
//
// The Lean WebSocket model uses session types (send/recv/choice/offer) for
// protocol-level verification, but the transpiler maps to the operational
// WsDoState model (connection tracking + message broadcast). Session type
// verification is a manual Veil exercise.
//
// Lean output structure:
//   namespace ChatRoom
//     def fetch (self : ChatRoomState) (request : Request) : IO Response := ...
//     def webSocketMessage (self : ChatRoomState) (ws : WebSocket) (message : String) : IO Unit := ...
//     def webSocketClose   (self : ChatRoomState) (ws : WebSocket) ... : IO Unit := ...
//   end ChatRoom

export class ChatRoom extends DurableObject {
  // -- fetch: upgrade HTTP to WebSocket, accept with room tag.
  // -- The 101 status + webSocket field in ResponseInit signals a WS upgrade.
  async fetch(request: Request): Promise<Response> {
    const pair = new WebSocketPair();
    const url = new URL(request.url);
    const room = url.pathname.slice(1) || "default";

    // acceptWebSocket registers the server-side socket with the DO runtime.
    // Tags enable efficient broadcast to subsets of connections.
    this.ctx.acceptWebSocket(pair[1], [room]);

    return new Response(null, { status: 101, webSocket: pair[0] });
  }

  // -- webSocketMessage: called for each message received on any accepted socket.
  // -- Hibernation: the DO may have been evicted and reconstructed since accept.
  async webSocketMessage(ws: WebSocket, message: string): Promise<void> {
    // Get the tags for this connection (set during acceptWebSocket)
    const tags = this.ctx.getTags(ws);
    if (tags.length > 0) {
      // Broadcast to all peers in the same room
      const peers = this.ctx.getWebSockets(tags[0]);
      for (const peer of peers) {
        peer.send(message);
      }
    }
  }

  // -- webSocketClose: clean up when a client disconnects.
  async webSocketClose(ws: WebSocket, code: number, reason: string, wasClean: boolean): Promise<void> {
    ws.close(code, reason);
  }
}
