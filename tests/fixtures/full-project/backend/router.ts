import { ApiResponse, makeApiError } from '../shared/types.js';

interface RouterEnv extends Env {
  AUTH_DO: DurableObjectNamespace;
}

function jsonResponse(data: unknown, status = 200): Response {
  return new Response(JSON.stringify(data), { status, headers: { "Content-Type": "application/json" } });
}

export default {
  async fetch(request: Request, env: RouterEnv, ctx: ExecutionContext): Promise<Response> {
    const url = new URL(request.url);
    const path = url.pathname;

    if (path.startsWith("/auth/")) {
      const authId = env.AUTH_DO.idFromName("global");
      const auth   = env.AUTH_DO.get(authId);
      return auth.fetch(new Request(request.url.replace("/auth", ""), {
        method: request.method, headers: request.headers, body: request.body,
      }));
    }

    return jsonResponse({ error: "Not Found" }, 404);
  },
};
