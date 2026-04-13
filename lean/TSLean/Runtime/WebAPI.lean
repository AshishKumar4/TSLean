-- TSLean.Runtime.WebAPI
-- Web platform type stubs for transpiled Durable Object code.
-- Simplified models of Request, Response, URL, Headers from the Fetch API.

namespace TSLean.WebAPI

/-! ## Headers -/

abbrev Headers := List (String × String)

namespace Headers

def empty : Headers := []

def get (h : Headers) (key : String) : Option String :=
  (h.find? (fun (k, _) => k.toLower == key.toLower)).map Prod.snd

def set (h : Headers) (key value : String) : Headers :=
  let filtered := h.filter (fun (k, _) => k.toLower != key.toLower)
  filtered ++ [(key, value)]

def has (h : Headers) (key : String) : Bool :=
  h.any (fun (k, _) => k.toLower == key.toLower)

def append (h : Headers) (key value : String) : Headers :=
  h ++ [(key, value)]

def delete (h : Headers) (key : String) : Headers :=
  h.filter (fun (k, _) => k.toLower != key.toLower)

def keys (h : Headers) : List String := h.map Prod.fst

def values (h : Headers) : List String := h.map Prod.snd

def entries (h : Headers) : Headers := h

instance : Inhabited Headers := ⟨empty⟩

-- Theorems
theorem get_empty (k : String) : Headers.empty.get k = none := by
  simp [empty, get]

theorem has_empty (k : String) : Headers.empty.has k = false := by
  simp [empty, has]

end Headers

/-! ## SearchParams -/

abbrev SearchParams := List (String × String)

namespace SearchParams

def empty : SearchParams := []

def get (sp : SearchParams) (key : String) : Option String :=
  (sp.find? (fun (k, _) => k == key)).map Prod.snd

def set (sp : SearchParams) (key value : String) : SearchParams :=
  (sp.filter (fun (k, _) => k != key)) ++ [(key, value)]

def has (sp : SearchParams) (key : String) : Bool :=
  sp.any (fun (k, _) => k == key)

def delete (sp : SearchParams) (key : String) : SearchParams :=
  sp.filter (fun (k, _) => k != key)

def entries (sp : SearchParams) : SearchParams := sp

instance : Inhabited SearchParams := ⟨empty⟩

end SearchParams

/-! ## URL -/

structure URL where
  pathname     : String
  searchParams : SearchParams
  origin       : String
  href         : String
  protocol     : String := "https:"
  host         : String := ""
  deriving Repr

namespace URL

def parse (s : String) : URL :=
  -- Simplified parser: splits on "?" for search params, extracts pathname
  let parts := s.splitOn "?"
  let pathPart := parts.head?.getD s
  let queryPart := if parts.length > 1 then (parts.drop 1).head?.getD "" else ""
  let params : SearchParams := if queryPart.isEmpty then []
    else queryPart.splitOn "&" |>.filterMap fun kv =>
      match kv.splitOn "=" with
      | [k, v] => some (k, v)
      | _ => none
  let protoParts := pathPart.splitOn "//"
  let afterProto := (protoParts.drop 1).head?.getD pathPart
  let hostAndPath := afterProto.splitOn "/"
  let hostStr := hostAndPath.head?.getD ""
  let pathSegments := hostAndPath.drop 1
  let pathname := if protoParts.length > 1
    then "/" ++ String.intercalate "/" pathSegments
    else pathPart
  let protoPrefix := protoParts.head?.getD ""
  let origin := if protoParts.length > 1 then protoPrefix ++ "//" ++ hostStr else ""
  { pathname, searchParams := params, origin, href := s,
    protocol := if s.startsWith "https" then "https:" else "http:",
    host := hostStr }

instance : Inhabited URL := ⟨{ pathname := "/", searchParams := [], origin := "", href := "" }⟩

end URL

/-! ## ResponseInit -/

structure ResponseInit where
  status  : Nat := 200
  headers : Headers := Headers.empty
  deriving Repr

instance : Inhabited ResponseInit := ⟨{}⟩

/-! ## Request -/

structure Request where
  method  : String
  url     : String
  headers : Headers
  body    : Option String := none
  deriving Repr

namespace Request

def empty : Request := { method := "GET", url := "/", headers := [] }

def parsedUrl (r : Request) : URL := URL.parse r.url

/-- Parse request body as JSON (stub — returns body as-is). -/
def toJson (r : Request) : IO String := pure (r.body.getD "")

/-- Get request body as text. -/
def text (r : Request) : IO String := pure (r.body.getD "")

instance : Inhabited Request := ⟨empty⟩

end Request

/-! ## Response -/

structure Response where
  status  : Nat
  body    : String
  headers : Headers
  deriving Repr

namespace Response

def ok (body : String) (headers : Headers := []) : Response :=
  { status := 200, body, headers }

def notFound (body : String := "Not Found") : Response :=
  { status := 404, body, headers := [] }

def badRequest (body : String := "Bad Request") : Response :=
  { status := 400, body, headers := [] }

def serverError (body : String := "Internal Server Error") : Response :=
  { status := 500, body, headers := [] }

def redirect (url : String) (status : Nat := 302) : Response :=
  { status, body := "", headers := [("Location", url)] }

def json (body : String) (status : Nat := 200) : Response :=
  { status, body, headers := [("Content-Type", "application/json")] }

/-- Parse response body as JSON (stub — returns body as-is).
    Deliberately shadows the static `json` constructor in instance method position. -/
-- Use fully-qualified `Response.json body status` for the constructor.
-- Dot notation `r.toJson` for the instance method.
def toJson (r : Response) : IO String := pure r.body

/-- Get response body as text. -/
def text (r : Response) : IO String := pure r.body

instance : Inhabited Response := ⟨ok ""⟩

end Response

def mkResponse (body : String) (opts : ResponseInit := {}) : Response :=
  { status := opts.status, body, headers := opts.headers }

/-! ## Fetch stub -/

/-- Placeholder for the fetch API. In verification mode this is opaque. -/
opaque fetch (url : String) (opts : Request := Request.empty) : IO Response

/-! ## Theorems -/

theorem mkResponse_status (body : String) (opts : ResponseInit) :
    (mkResponse body opts).status = opts.status := rfl

theorem mkResponse_body (body : String) (opts : ResponseInit) :
    (mkResponse body opts).body = body := rfl

theorem Response.ok_status (body : String) :
    (Response.ok body).status = 200 := rfl

theorem Response.notFound_status :
    Response.notFound.status = 404 := rfl

theorem Response.json_has_content_type (body : String) :
    (Response.json body).headers.has "Content-Type" = true := by
  simp [Response.json, Headers.has, List.any]

theorem Response.redirect_has_location (url : String) :
    (Response.redirect url).headers.has "Location" = true := by
  simp [Response.redirect, Headers.has, List.any]

/-! ## Request/Response composition -/

theorem Response.ok_body (body : String) :
    (Response.ok body).body = body := rfl

theorem Response.badRequest_status :
    Response.badRequest.status = 400 := rfl

theorem Response.serverError_status :
    Response.serverError.status = 500 := rfl

theorem Response.json_status (body : String) :
    (Response.json body).status = 200 := rfl

theorem Response.json_custom_status (body : String) (s : Nat) :
    (Response.json body s).status = s := rfl

theorem Response.redirect_status (url : String) :
    (Response.redirect url).status = 302 := rfl

theorem Response.redirect_body_empty (url : String) :
    (Response.redirect url).body = "" := rfl

theorem mkResponse_default_status (body : String) :
    (mkResponse body).status = 200 := rfl

-- Request
theorem Request.empty_method : Request.empty.method = "GET" := rfl
theorem Request.empty_url : Request.empty.url = "/" := rfl

-- Headers append then has is true
theorem Headers.has_append_self (h : Headers) (k v : String) :
    (h.append k v).has k = true := by
  simp [Headers.append, Headers.has, List.any_append, String.toLower]

-- URL parse preserves href
theorem URL.parse_href (s : String) : (URL.parse s).href = s := rfl

-- SearchParams
theorem SearchParams.get_empty (k : String) : SearchParams.empty.get k = none := by
  simp [SearchParams.empty, SearchParams.get]

theorem SearchParams.has_empty (k : String) : SearchParams.empty.has k = false := by
  simp [SearchParams.empty, SearchParams.has]

end TSLean.WebAPI
