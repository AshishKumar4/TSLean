// Template literals → s!"..." interpolation

function greeting(name: string, age: number): string {
  return `Hello, ${name}! You are ${age} years old.`;
}

function url(base: string, path: string, id: string): string {
  return `${base}/${path}/${id}`;
}

function jsonLike(key: string, value: string): string {
  return `{"${key}": "${value}"}`;
}

function multipart(a: string, b: string, c: number): string {
  return `${a}-${b}=${c}`;
}

const endpoint = 'https://api.example.com';

function userUrl(userId: string): string {
  return `${endpoint}/users/${userId}`;
}

function logMessage(level: string, msg: string): string {
  const ts = Date.now();
  return `[${level}] ${msg} at ${ts}`;
}

interface User { id: string; name: string }

function userTag(u: User): string {
  return `<user id="${u.id}">${u.name}</user>`;
}
