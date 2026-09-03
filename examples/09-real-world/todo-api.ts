// 09-real-world/todo-api.ts
// A realistic Todo API showing multiple features combined.
//
// Run: npx tsx src/cli.ts examples/09-real-world/todo-api.ts -o output.lean

interface Todo {
  id: string;
  title: string;
  completed: boolean;
}

type Filter = 'all' | 'active' | 'completed';

function createTodo(id: string, title: string): Todo {
  return { id, title, completed: false };
}

function toggleTodo(todo: Todo): Todo {
  return { ...todo, completed: !todo.completed };
}

function filterTodos(todos: Todo[], filter: Filter): Todo[] {
  switch (filter) {
    case 'all': return todos;
    case 'active': return todos.filter(t => !t.completed);
    case 'completed': return todos.filter(t => t.completed);
  }
}

function countActive(todos: Todo[]): number {
  return todos.filter(t => !t.completed).length;
}

function removeTodo(todos: Todo[], id: string): Todo[] {
  return todos.filter(t => t.id !== id);
}
