import { TodoStore } from './store.js';
import { createTodo } from './models.js';

export function addTodo(store: TodoStore, title: string): void {
  const id = String(Math.random());
  const todo = createTodo(id, title);
  store.add(todo);
}

export function clearCompleted(store: TodoStore): number {
  const completed = store.getFiltered('completed');
  let count = 0;
  for (const todo of completed) {
    if (store.remove(todo.id)) count++;
  }
  return count;
}

export function toggleAll(store: TodoStore): void {
  const all = store.getFiltered('all');
  const allCompleted = all.every(t => t.completed);
  for (const todo of all) {
    if (allCompleted || !todo.completed) {
      store.toggle(todo.id);
    }
  }
}
