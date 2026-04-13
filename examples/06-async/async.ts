// 06-async/async.ts
// async/await → IO monad. Promises unwrap to IO return types.
//
// Run: npx tsx src/cli.ts examples/06-async/async.ts -o output.lean

// async function → def fetchData : IO String
async function fetchData(url: string): Promise<string> {
  return `data from ${url}`;
}

// await → monadic bind (← in do notation)
async function processData(url: string): Promise<string> {
  const raw = await fetchData(url);
  return raw.toUpperCase();
}

// Promise<void> → IO Unit
async function logMessage(msg: string): Promise<void> {
  console.log(msg);
}

// Multiple awaits in sequence
async function pipeline(url: string): Promise<number> {
  const data = await fetchData(url);
  const processed = await processData(url);
  return processed.length;
}
