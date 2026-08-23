-- TSLean.Stubs.NodePath
-- Lean stubs for Node.js `node:path` module.
-- Pure string operations — no IO needed.

namespace TSLean.Stubs.NodePath

/-- Join path segments with the platform separator. -/
def join (segments : Array String) : String :=
  String.intercalate "/" (segments.toList.filter (· ≠ ""))

/-- Resolve a relative path against a base directory. -/
def resolve (base relative : String) : String :=
  if relative.startsWith "/" then relative
  else base ++ "/" ++ relative

/-- Get the directory name of a path. -/
def dirname (p : String) : String :=
  match p.splitOn "/" |>.dropLast with
  | [] => "."
  | parts => String.intercalate "/" parts

/-- Get the last component of a path. -/
def basename (p : String) (ext : String := "") : String :=
  let b := (p.splitOn "/").getLast?.getD p
  if ext.length > 0 && b.endsWith ext then
    String.ofList (b.toList.take (b.length - ext.length))
  else b

/-- Get the file extension (including the dot). -/
def extname (p : String) : String :=
  let b := basename p
  let parts := b.splitOn "."
  if parts.length > 1 then "." ++ parts.getLast!
  else ""

/-- Compute relative path from `from` to `to`. -/
def relative (from_ to_ : String) : String :=
  -- Simplified: strip common prefix
  let fromParts := from_.splitOn "/"
  let toParts := to_.splitOn "/"
  let rec countCommon : List String → List String → Nat
    | a :: as_, b :: bs => if a == b then 1 + countCommon as_ bs else 0
    | _, _ => 0
  let common := countCommon fromParts toParts
  let ups := List.replicate (fromParts.length - common) ".."
  let rest := toParts.drop common
  String.intercalate "/" (ups ++ rest)

/-- Normalize a path (remove . and .., collapse separators). -/
def normalize (p : String) : String :=
  let parts := p.splitOn "/" |>.filter (fun s => s ≠ "." && s ≠ "")
  let folded := parts.foldl (fun acc seg =>
    if seg == ".." then acc.dropLast else acc ++ [seg]) ([] : List String)
  let result := String.intercalate "/" folded
  if p.startsWith "/" then "/" ++ result else result

/-- Check if a path is absolute. -/
def isAbsolute (p : String) : Bool := p.startsWith "/"

/-- Path separator (Unix). -/
def sep : String := "/"

/-- Path delimiter (Unix). -/
def delimiter : String := ":"

end TSLean.Stubs.NodePath
