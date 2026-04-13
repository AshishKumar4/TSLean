// Basic Workers entry point — no DO, just fetch handler
export default {
  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/hello") {
      return new Response("Hello Workers!");
    }
    return new Response("Not Found", { status: 404 });
  }
};
