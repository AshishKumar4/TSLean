interface AuthSession { userId: string; token: string; createdAt: number; expiresAt: number; roles: string[] }

export class AuthDO {
  private state: DurableObjectState;
  private TOKEN_TTL = 3600_000;
  constructor(state: DurableObjectState, env: Env) { this.state = state; }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (request.method === "POST" && url.pathname === "/login") {
      const creds = await request.json() as { username: string; password: string };
      return this.handleLogin(creds);
    }
    if (request.method === "POST" && url.pathname === "/logout") {
      const token = request.headers.get("Authorization")?.replace("Bearer ", "");
      if (!token) return new Response(JSON.stringify({ error: "No token" }), { status: 401 });
      await this.logout(token);
      return new Response(JSON.stringify({ success: true }), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "GET" && url.pathname === "/verify") {
      const token = request.headers.get("Authorization")?.replace("Bearer ", "");
      if (!token) return new Response(JSON.stringify({ valid: false }), { status: 401 });
      const session = await this.authenticate(token);
      if (!session) return new Response(JSON.stringify({ valid: false }), { status: 401 });
      return new Response(JSON.stringify({ valid: true, userId: session.userId, roles: session.roles }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
  private async handleLogin(creds: { username: string; password: string }): Promise<Response> {
    if (!creds.username || !creds.password)
      return new Response(JSON.stringify({ error: "Invalid credentials" }), { status: 401 });
    const token = crypto.randomUUID();
    const session: AuthSession = { userId: creds.username, token, createdAt: Date.now(), expiresAt: Date.now() + this.TOKEN_TTL, roles: ["user"] };
    await this.state.storage.put(`token:${token}`, session);
    return new Response(JSON.stringify({ token }), { headers: { "Content-Type": "application/json" } });
  }
  private async logout(token: string): Promise<void> { await this.state.storage.delete(`token:${token}`); }
  private async authenticate(token: string): Promise<AuthSession | null> {
    const session = await this.state.storage.get<AuthSession>(`token:${token}`);
    if (!session) return null;
    if (Date.now() > session.expiresAt) { await this.state.storage.delete(`token:${token}`); return null; }
    return session;
  }
}
