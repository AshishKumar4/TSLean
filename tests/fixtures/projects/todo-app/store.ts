import { Todo, Filter } from './models.js';

export class TodoStore {
  private todos: Todo[] = [];

  add(todo: Todo): void {
    this.todos.push(todo);
  }

  remove(id: string): boolean {
    const idx = this.todos.findIndex(t => t.id === id);
    if (idx === -1) return false;
    this.todos.splice(idx, 1);
    return true;
  }

  toggle(id: string): boolean {
    const todo = this.todos.find(t => t.id === id);
    if (!todo) return false;
    todo.completed = !todo.completed;
    return true;
  }

  getFiltered(filter: Filter): Todo[] {
    switch (filter) {
      case 'all': return this.todos;
      case 'active': return this.todos.filter(t => !t.completed);
      case 'completed': return this.todos.filter(t => t.completed);
    }
  }

  count(): number {
    return this.todos.length;
  }

  activeCount(): number {
    return this.todos.filter(t => !t.completed).length;
  }
}
