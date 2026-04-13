// Async/await → IO monad

async function fetchUser(id: string): Promise<{ name: string; email: string }> {
  const response = await fetch(`https://api.example.com/users/${id}`);
  const data = await response.json();
  return data as { name: string; email: string };
}

async function fetchAndProcess(ids: string[]): Promise<string[]> {
  const results: string[] = [];
  for (const id of ids) {
    const user = await fetchUser(id);
    results.push(user.name);
  }
  return results;
}

async function delay(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function withRetry<T>(op: () => Promise<T>, maxRetries: number): Promise<T> {
  let lastError: Error | undefined;
  for (let i = 0; i < maxRetries; i++) {
    try {
      return await op();
    } catch (e) {
      lastError = e as Error;
      await delay(100 * (i + 1));
    }
  }
  throw lastError ?? new Error("Max retries exceeded");
}
