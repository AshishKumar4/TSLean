import { User, UserId, ApiResponse, makeApiSuccess, makeApiError } from '../shared/types.js';
import { validateEmail, validateDisplayName } from '../shared/validators.js';

interface StoredUser extends User { passwordHash: string }
interface AuthToken { userId: UserId; token: string; expiresAt: number }

export class AuthDO {
  private state: DurableObjectState;
  constructor(state: DurableObjectState, env: Env) { this.state = state; }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    const body = request.method !== "GET" ? await request.json() as Record<string, unknown> : null;
    if (url.pathname === "/register") {
      const result = await this.register(body as { email: string; displayName: string; password: string });
      return new Response(JSON.stringify(result), { headers: { "Content-Type": "application/json" } });
    }
    if (url.pathname === "/login") {
      const result = await this.login(body as { email: string; password: string });
      return new Response(JSON.stringify(result), { headers: { "Content-Type": "application/json" } });
    }
    if (url.pathname === "/verify") {
      const token = request.headers.get("Authorization")?.replace("Bearer ", "");
      const result = await this.verify(token ?? "");
      return new Response(JSON.stringify(result), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
  private async register(data: { email: string; displayName: string; password: string }): Promise<ApiResponse<{ userId: UserId }>> {
    const emailCheck = validateEmail(data.email);
    if (!emailCheck.valid) return makeApiError(emailCheck.errors.join(", "), 400);
    const nameCheck = validateDisplayName(data.displayName);
    if (!nameCheck.valid) return makeApiError(nameCheck.errors.join(", "), 400);
    const userId = crypto.randomUUID() as UserId;
    const user: StoredUser = { id: userId, email: data.email, displayName: data.displayName, createdAt: Date.now(), roles: ["user"], passwordHash: `hash:${data.password}` };
    await this.state.storage.put(`user:${userId}`, user);
    await this.state.storage.put(`email:${data.email}`, userId);
    return makeApiSuccess({ userId });
  }
  private async login(data: { email: string; password: string }): Promise<ApiResponse<{ token: string }>> {
    const userId = await this.state.storage.get<string>(`email:${data.email}`);
    if (!userId) return makeApiError("Invalid credentials", 401);
    const token = crypto.randomUUID();
    const authToken: AuthToken = { userId: userId as UserId, token, expiresAt: Date.now() + 3600_000 };
    await this.state.storage.put(`token:${token}`, authToken);
    return makeApiSuccess({ token });
  }
  private async verify(token: string): Promise<ApiResponse<{ userId: UserId }>> {
    const authToken = await this.state.storage.get<AuthToken>(`token:${token}`);
    if (!authToken) return makeApiError("Invalid token", 401);
    if (Date.now() > authToken.expiresAt) { await this.state.storage.delete(`token:${token}`); return makeApiError("Token expired", 401); }
    return makeApiSuccess({ userId: authToken.userId });
  }
}
