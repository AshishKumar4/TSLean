import { RoomId, UserId } from '../shared/types.js';

interface Message { id: string; userId: UserId; content: string; timestamp: number }

export class ChatRoomDO {
  private state: DurableObjectState;
  private messages: Message[] = [];
  private nextId = 0;
  constructor(state: DurableObjectState, env: Env) {
    this.state = state;
    this.state.blockConcurrencyWhile(async () => {
      this.messages = await this.state.storage.get<Message[]>("messages") ?? [];
      this.nextId   = await this.state.storage.get<number>("nextId") ?? 0;
    });
  }
  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    if (url.pathname === "/history" && request.method === "GET") {
      return new Response(JSON.stringify({ messages: this.messages }), { headers: { "Content-Type": "application/json" } });
    }
    if (url.pathname === "/post" && request.method === "POST") {
      const body = await request.json() as { userId: UserId; content: string };
      const msg: Message = { id: `msg_${this.nextId++}`, userId: body.userId, content: body.content, timestamp: Date.now() };
      this.messages.push(msg);
      await this.state.storage.put("messages", this.messages);
      await this.state.storage.put("nextId", this.nextId);
      return new Response(JSON.stringify({ msg }), { headers: { "Content-Type": "application/json" } });
    }
    return new Response("Not Found", { status: 404 });
  }
}
