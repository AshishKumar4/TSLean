interface Session { userId: string; data: Record<string, unknown>; createdAt: number; expiresAt: number }

export class SessionStoreDO {
  private state: DurableObjectState;
  private TTL_MS = 24 * 60 * 60 * 1000;
  constructor(state: DurableObjectState, env: Env) { this.state = state; }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    const sessionId = url.searchParams.get("sessionId");
    if (request.method === "POST" && url.pathname === "/create") {
      const body = await request.json() as { userId: string; data?: Record<string, unknown> };
      const id = await this.createSession(body.userId, body.data ?? {});
      return new Response(JSON.stringify({ sessionId: id }), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "GET" && url.pathname === "/get" && sessionId) {
      const session = await this.getSession(sessionId);
      if (!session) return new Response(JSON.stringify({ error: "not found" }), { status: 404, headers: { "Content-Type": "application/json" } });
      return new Response(JSON.stringify({ session }), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "DELETE" && url.pathname === "/destroy" && sessionId) {
      await this.destroySession(sessionId);
      return new Response(JSON.stringify({ success: true }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
  private async createSession(userId: string, data: Record<string, unknown>): Promise<string> {
    const id = crypto.randomUUID();
    const now = Date.now();
    const session: Session = { userId, data, createdAt: now, expiresAt: now + this.TTL_MS };
    await this.state.storage.put(`session:${id}`, session);
    return id;
  }
  private async getSession(id: string): Promise<Session | null> {
    const session = await this.state.storage.get<Session>(`session:${id}`);
    if (!session) return null;
    if (Date.now() > session.expiresAt) { await this.state.storage.delete(`session:${id}`); return null; }
    return session;
  }
  private async destroySession(id: string): Promise<void> { await this.state.storage.delete(`session:${id}`); }
}
