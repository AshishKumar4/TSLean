export interface Todo {
  id: string;
  title: string;
  completed: boolean;
  createdAt: number;
}

export interface TodoList {
  name: string;
  items: Todo[];
}

export type Filter = 'all' | 'active' | 'completed';

export function createTodo(id: string, title: string): Todo {
  return { id, title, completed: false, createdAt: Date.now() };
}
