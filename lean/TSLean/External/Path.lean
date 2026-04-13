-- TSLean.External.Path
-- Stubs for Node.js path module operations.

namespace TSLean.External.Path

def join (segments : List String) : String :=
  String.intercalate "/" segments

def resolve (base relative : String) : String :=
  if relative.startsWith "/" then relative
  else base ++ "/" ++ relative

def dirname (p : String) : String :=
  match p.splitOn "/" |>.dropLast with
  | [] => "."
  | parts => String.intercalate "/" parts

def basename (p : String) : String :=
  (p.splitOn "/").getLast?.getD p

def extname (p : String) : String :=
  let b := basename p
  match b.splitOn "." |>.getLast? with
  | some ext => "." ++ ext
  | none => ""

def isAbsolute (p : String) : Bool := p.startsWith "/"

def normalize (p : String) : String := p  -- simplified

end TSLean.External.Path
