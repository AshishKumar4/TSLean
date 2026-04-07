-- TSLean.DurableObjects.Http
import TSLean.Runtime.Basic
import TSLean.Stdlib.HashMap

namespace TSLean.DO.Http
open TSLean TSLean.Stdlib.HashMap

inductive HttpMethod where
  | GET | POST | PUT | PATCH | DELETE | HEAD | OPTIONS
  deriving Repr, BEq, DecidableEq

abbrev HttpStatus := Nat
abbrev HttpHeaders := AssocMap String String
def HttpHeaders.empty : HttpHeaders := AssocMap.empty

structure HttpRequest where
  method  : HttpMethod
  url     : String
  headers : HttpHeaders
  body    : Option String

structure HttpResponse where
  status  : HttpStatus
  headers : HttpHeaders
  body    : String

def HttpResponse.mk' (s : HttpStatus) (b : String) : HttpResponse :=
  { status := s, headers := AssocMap.empty, body := b }

def HttpResponse.ok          (b : String) := HttpResponse.mk' 200 b
def HttpResponse.created     (b : String) := HttpResponse.mk' 201 b
def HttpResponse.noContent               := HttpResponse.mk' 204 ""
def HttpResponse.badRequest  (b : String) := HttpResponse.mk' 400 b
def HttpResponse.unauthorized (b : String) := HttpResponse.mk' 401 b
def HttpResponse.forbidden   (b : String) := HttpResponse.mk' 403 b
def HttpResponse.notFound    (b : String) := HttpResponse.mk' 404 b
def HttpResponse.internalError (b : String) := HttpResponse.mk' 500 b
def HttpResponse.json (body : String) : HttpResponse :=
  { status := 200, headers := AssocMap.empty.insert "Content-Type" "application/json", body }
def HttpResponse.withHeader (r : HttpResponse) (k v : String) : HttpResponse :=
  { r with headers := r.headers.insert k v }

def HttpResponse.isSuccess     (r : HttpResponse) : Bool := 200 ≤ r.status && r.status < 300
def HttpResponse.isRedirect    (r : HttpResponse) : Bool := 300 ≤ r.status && r.status < 400
def HttpResponse.isClientError (r : HttpResponse) : Bool := 400 ≤ r.status && r.status < 500
def HttpResponse.isServerError (r : HttpResponse) : Bool := 500 ≤ r.status && r.status < 600
def HttpResponse.isError       (r : HttpResponse) : Bool := r.isClientError || r.isServerError
def HttpResponse.isOk          (r : HttpResponse) : Bool := r.status == 200

theorem ok_is_success (body : String) : (HttpResponse.ok body).isSuccess = true := by
  simp [HttpResponse.ok, HttpResponse.mk', HttpResponse.isSuccess]
theorem created_is_success (body : String) : (HttpResponse.created body).isSuccess = true := by
  simp [HttpResponse.created, HttpResponse.mk', HttpResponse.isSuccess]
theorem noContent_is_success : HttpResponse.noContent.isSuccess = true := by
  simp [HttpResponse.noContent, HttpResponse.mk', HttpResponse.isSuccess]
theorem badRequest_is_client_error (msg : String) : (HttpResponse.badRequest msg).isClientError = true := by
  simp [HttpResponse.badRequest, HttpResponse.mk', HttpResponse.isClientError]
theorem unauthorized_is_client_error (msg : String) : (HttpResponse.unauthorized msg).isClientError = true := by
  simp [HttpResponse.unauthorized, HttpResponse.mk', HttpResponse.isClientError]
theorem notFound_is_client_error (msg : String) : (HttpResponse.notFound msg).isClientError = true := by
  simp [HttpResponse.notFound, HttpResponse.mk', HttpResponse.isClientError]
theorem internalError_is_server_error (msg : String) : (HttpResponse.internalError msg).isServerError = true := by
  simp [HttpResponse.internalError, HttpResponse.mk', HttpResponse.isServerError]

theorem isError_iff (r : HttpResponse) :
    r.isError = true ↔ r.isClientError = true ∨ r.isServerError = true := by
  simp [HttpResponse.isError, Bool.or_eq_true]

theorem success_not_error (r : HttpResponse) (h : r.isSuccess = true) : r.isError = false := by
  simp only [HttpResponse.isSuccess, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [HttpResponse.isError, HttpResponse.isClientError, HttpResponse.isServerError]
  have h3 : decide (400 ≤ r.status) = false :=
    decide_eq_false_iff_not.mpr (Nat.not_le.mpr (Nat.lt_of_lt_of_le h2 (by decide)))
  have h4 : decide (500 ≤ r.status) = false :=
    decide_eq_false_iff_not.mpr (Nat.not_le.mpr (Nat.lt_of_lt_of_le h2 (by decide)))
  rw [h3, h4]; rfl

theorem success_and_redirect_exclusive (r : HttpResponse) :
    r.isSuccess = true → r.isRedirect = false := by
  simp only [HttpResponse.isSuccess, Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨h1, h2⟩
  simp only [HttpResponse.isRedirect]
  have h3 : decide (300 ≤ r.status) = false :=
    decide_eq_false_iff_not.mpr (Nat.not_le.mpr (Nat.lt_of_lt_of_le h2 (by decide)))
  rw [h3]; rfl

theorem client_not_server_error' (r : HttpResponse) :
    r.isClientError = true → r.isServerError = false := by
  simp only [HttpResponse.isClientError, Bool.and_eq_true, decide_eq_true_eq]
  intro ⟨h1, h2⟩
  simp only [HttpResponse.isServerError]
  have h3 : decide (500 ≤ r.status) = false :=
    decide_eq_false_iff_not.mpr (Nat.not_le.mpr (Nat.lt_of_lt_of_le h2 (by decide)))
  rw [h3]; rfl

theorem client_not_server_error (r : HttpResponse) :
    r.isClientError = true → r.isServerError = false :=
  client_not_server_error' r

theorem json_response_is_ok : (HttpResponse.json "{}").isSuccess = true := by
  simp [HttpResponse.json, HttpResponse.isSuccess]

theorem withHeader_get_same (r : HttpResponse) (k v : String) :
    (r.withHeader k v).headers.get? k = some v := by
  simp [HttpResponse.withHeader, AssocMap.get?_insert_same]

theorem mk'_body (s : HttpStatus) (b : String) : (HttpResponse.mk' s b).body = b := rfl



-- Additional Http deep theorems

theorem status_determines_success (r : HttpResponse) :
    r.isSuccess = true ↔ 200 ≤ r.status ∧ r.status < 300 := by
  simp [HttpResponse.isSuccess, Bool.and_eq_true, decide_eq_true_eq]

theorem ok_body (body : String) : (HttpResponse.ok body).body = body := rfl
theorem badRequest_body (body : String) : (HttpResponse.badRequest body).body = body := rfl
theorem notFound_body (body : String) : (HttpResponse.notFound body).body = body := rfl

theorem withHeader_headers (r : HttpResponse) (k v : String) :
    (r.withHeader k v).headers.get? k = some v :=
  withHeader_get_same r k v

theorem status_200_is_success : (HttpResponse.ok "").isSuccess = true := by
  simp [HttpResponse.ok, HttpResponse.mk', HttpResponse.isSuccess]

theorem status_404_is_client_error (msg : String) :
    (HttpResponse.notFound msg).isClientError = true :=
  notFound_is_client_error msg

theorem status_500_is_server_error (msg : String) :
    (HttpResponse.internalError msg).isServerError = true :=
  internalError_is_server_error msg

-- Success and error are exclusive (see success_not_error)
theorem isSuccess_isError_exclusive (r : HttpResponse) (h : r.isSuccess = true) :
    r.isError = false := success_not_error r h

theorem withHeader_status_unchanged (r : HttpResponse) (k v : String) :
    (r.withHeader k v).status = r.status := rfl

theorem json_is_success : (HttpResponse.json "{}").isSuccess = true := by
  simp [HttpResponse.json, HttpResponse.isSuccess]

theorem forbidden_is_client_error (msg : String) :
    (HttpResponse.forbidden msg).isClientError = true := by
  simp [HttpResponse.forbidden, HttpResponse.mk', HttpResponse.isClientError]

end TSLean.DO.Http
