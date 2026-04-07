interface RPCEnvelope { id: string; method: string; params: unknown; timestamp: number }
interface RPCResponse  { id: string; result?: unknown; error?: string }

export class CoordinatorDO {
  private state: DurableObjectState;
  private nodes: Map<string, { id: string; lastSeen: number }> = new Map();
  constructor(state: DurableObjectState, env: Env) { this.state = state; }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (request.method === "POST" && url.pathname === "/rpc") {
      const envelope = await request.json() as RPCEnvelope;
      const response = await this.handleRPC(envelope);
      return new Response(JSON.stringify(response), { headers: { "Content-Type": "application/json" } });
    }
    if (request.method === "GET" && url.pathname === "/topology") {
      const topology = Array.from(this.nodes.entries()).map(([id, node]) => ({ id, lastSeen: node.lastSeen }));
      return new Response(JSON.stringify({ nodes: topology }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
  private async handleRPC(envelope: RPCEnvelope): Promise<RPCResponse> {
    const { id, method, params } = envelope;
    switch (method) {
      case "ping":      return { id, result: { pong: true, timestamp: Date.now() } };
      case "broadcast": return { id, result: { sent: true } };
      default:          return { id, error: `Unknown method: ${method}` };
    }
  }
}
