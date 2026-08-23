import TSLean.JS.AbstractEquality
import TSLean.JS.HasInstance

/-! Proof-support-only free coercion specification and scripted semantics.
It is intentionally audited and tested without being imported by the production `TSLean.JS` barrel. -/

namespace TSLean.JS

/-- One typed observable operation in an effectful coercion. -/
inductive CoercionOp : Type 0 → Type 0 where
  | get (ref : RefId) (key : PropertyKey) (receiver : Value) : CoercionOp Value
  | call (callee : RefId) (receiver : Value) (arguments : Array Value) : CoercionOp Value
  | isCallable (ref : RefId) : CoercionOp Bool
  | ordinaryHasInstance (constructor : RefId) (value : Value) : CoercionOp Bool
  | typeError (message : String) : CoercionOp Empty
  | throw (value : Value) : CoercionOp Empty

/-- Total free syntax for effectful coercion algorithms. -/
inductive CoercionProgram (α : Type 0) : Type 0 where
  | pure (value : α)
  | get (ref : RefId) (key : PropertyKey) (receiver : Value)
      (next : Value → CoercionProgram α)
  | call (callee : RefId) (receiver : Value) (arguments : Array Value)
      (next : Value → CoercionProgram α)
  | isCallable (ref : RefId) (next : Bool → CoercionProgram α)
  | ordinaryHasInstance (constructor : RefId) (value : Value)
      (next : Bool → CoercionProgram α)
  | typeError (message : String)
  | throw (value : Value)

namespace CoercionProgram

/-- Substitutes the result of a free coercion program. -/
def bind : CoercionProgram α → (α → CoercionProgram β) → CoercionProgram β
  | .pure value, next => next value
  | .get ref key receiver next, last =>
      .get ref key receiver fun value => bind (next value) last
  | .call callee receiver arguments next, last =>
      .call callee receiver arguments fun value => bind (next value) last
  | .isCallable ref next, last => .isCallable ref fun value => bind (next value) last
  | .ordinaryHasInstance constructor value next, last =>
      .ordinaryHasInstance constructor value fun result => bind (next result) last
  | .typeError message, _ => .typeError message
  | .throw value, _ => .throw value

instance : Monad CoercionProgram where
  pure := .pure
  bind := bind

@[simp] theorem pure_bind (value : α) (next : α → CoercionProgram β) :
    (pure value >>= next) = next value := rfl

@[simp] theorem bind_pure (program : CoercionProgram α) :
    program >>= pure = program := by
  induction program with
  | pure value => rfl
  | get ref key receiver next induction | call ref receiver key next induction =>
      simp only [Bind.bind, bind]
      congr
      funext value
      exact induction value
  | isCallable ref next induction | ordinaryHasInstance ref value next induction =>
      simp only [Bind.bind, bind]
      congr
      funext value
      exact induction value
  | typeError message | throw message => rfl

theorem bind_assoc (program : CoercionProgram α) (next : α → CoercionProgram β)
    (last : β → CoercionProgram γ) :
    (program >>= next) >>= last = program >>= fun value => next value >>= last := by
  induction program with
  | pure value => rfl
  | get ref key receiver continuation induction | call ref receiver key continuation induction =>
      simp only [Bind.bind, bind]
      congr
      funext value
      exact induction value
  | isCallable ref continuation induction | ordinaryHasInstance ref value continuation induction =>
      simp only [Bind.bind, bind]
      congr
      funext value
      exact induction value
  | typeError message | throw message => rfl

instance : LawfulMonad CoercionProgram := LawfulMonad.mk' CoercionProgram
  (by
    intro α program
    change program >>= pure = program
    exact bind_pure program)
  pure_bind bind_assoc

/-- Raises one typed operation into the free program. -/
def perform (operation : CoercionOp α) : CoercionProgram α :=
  match operation with
  | .get ref key receiver => .get ref key receiver .pure
  | .call callee receiver arguments => .call callee receiver arguments .pure
  | .isCallable ref => .isCallable ref .pure
  | .ordinaryHasInstance constructor value => .ordinaryHasInstance constructor value .pure
  | .typeError message => .typeError message
  | .throw value => .throw value

/-- The explicit ordinary `instanceof` fallback operation. -/
def ordinaryHasInstanceEffect (constructor : RefId) (value : Value) : CoercionProgram Bool :=
  perform (.ordinaryHasInstance constructor value)

/-- Free coercion effects used directly by the production `*With` definitions. -/
def effects : CoercionEffects CoercionProgram where
  get ref key receiver := perform (.get ref key receiver)
  call callee receiver arguments := perform (.call callee receiver arguments)
  isCallable ref := perform (.isCallable ref)
  typeError message := perform (.typeError message)
  throw value := perform (.throw value)

/-- Interprets one operation at a lawful effect boundary. -/
def interpretOp [Monad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) : CoercionOp α → m α
  | .get ref key receiver => target.get ref key receiver
  | .call callee receiver arguments => target.call callee receiver arguments
  | .isCallable ref => target.isCallable ref
  | .ordinaryHasInstance constructor value => ordinary constructor value
  | .typeError message => target.typeError message
  | .throw value => target.throw value

/-- Folds a free coercion program into any lawful monad and coercion effects. -/
def interpret [Monad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) : CoercionProgram α → m α
  | .pure value => Pure.pure value
  | .get ref key receiver next => do
      let value ← target.get ref key receiver
      interpret target ordinary (next value)
  | .call callee receiver arguments next => do
      let value ← target.call callee receiver arguments
      interpret target ordinary (next value)
  | .isCallable ref next => do
      let value ← target.isCallable ref
      interpret target ordinary (next value)
  | .ordinaryHasInstance constructor value next => do
      let result ← ordinary constructor value
      interpret target ordinary (next result)
  | .typeError message => CoercionEffects.terminal (target.typeError message)
  | .throw value => CoercionEffects.terminal (target.throw value)

@[simp] theorem interpret_pure [Monad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (value : α) :
    interpret target ordinary (Pure.pure value) = Pure.pure value := rfl

private theorem terminal_empty [Monad m] [LawfulMonad m] (action : m Empty) :
    (CoercionEffects.terminal action : m Empty) = action := by
  unfold CoercionEffects.terminal
  rw [show Empty.elim = (Pure.pure : Empty → m Empty) from by
    funext impossible
    exact impossible.elim]
  exact _root_.bind_pure action

private theorem terminal_bind [Monad m] [LawfulMonad m] (action : m Empty)
    (next : α → m β) :
    (CoercionEffects.terminal action : m α) >>= next =
      (CoercionEffects.terminal action : m β) := by
  unfold CoercionEffects.terminal
  rw [LawfulMonad.bind_assoc]
  congr
  funext impossible
  exact impossible.elim

theorem interpret_bind [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (program : CoercionProgram α)
    (next : α → CoercionProgram β) :
    interpret target ordinary (program >>= next) =
      (interpret target ordinary program >>= fun value => interpret target ordinary (next value)) := by
  induction program with
  | pure value => simp [interpret]
  | get ref key receiver continuation induction | call ref receiver key continuation induction =>
      simp only [Bind.bind, bind, interpret]
      rw [LawfulMonad.bind_assoc]
      congr
      funext value
      exact induction value
  | isCallable ref continuation induction | ordinaryHasInstance ref value continuation induction =>
      simp only [Bind.bind, bind, interpret]
      rw [LawfulMonad.bind_assoc]
      congr
      funext value
      exact induction value
  | typeError message => exact (terminal_bind (target.typeError message) _).symm
  | throw value => exact (terminal_bind (target.throw value) _).symm

@[simp] theorem interpret_perform [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (operation : CoercionOp α) :
    interpret target ordinary (perform operation) = interpretOp target ordinary operation := by
  cases operation <;> simp [perform, interpret, interpretOp, terminal_empty]

theorem interpret_map [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (function : α → β)
    (program : CoercionProgram α) :
    interpret target ordinary (function <$> program) =
      function <$> interpret target ordinary program := by
  change interpret target ordinary (program >>= fun value => Pure.pure (function value)) = _
  rw [interpret_bind]
  simp only [interpret_pure]
  exact LawfulMonad.bind_pure_comp function (interpret target ordinary program)

@[simp] theorem interpret_terminal [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (program : CoercionProgram Empty) (α : Type) :
    interpret target ordinary (CoercionEffects.terminal program : CoercionProgram α) =
      (CoercionEffects.terminal (interpret target ordinary program) : m α) := by
  unfold CoercionEffects.terminal
  rw [interpret_bind]
  congr
  funext impossible
  exact impossible.elim

@[simp] theorem interpret_effect_get [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (ref : RefId) (key : PropertyKey) (receiver : Value) :
    interpret target ordinary (effects.get ref key receiver) = target.get ref key receiver := by
  simp [effects, interpretOp]

@[simp] theorem interpret_effect_call [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (callee : RefId) (receiver : Value)
    (arguments : Array Value) :
    interpret target ordinary (effects.call callee receiver arguments) =
      target.call callee receiver arguments := by
  simp [effects, interpretOp]

@[simp] theorem interpret_effect_isCallable [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool) (ref : RefId) :
    interpret target ordinary (effects.isCallable ref) = target.isCallable ref := by
  simp [effects, interpretOp]

@[simp] theorem interpret_effect_typeError [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool) (message : String) :
    interpret target ordinary (effects.typeError message) = target.typeError message := by
  change interpret target ordinary (perform (.typeError message)) = _
  simp [interpretOp]

@[simp] theorem interpret_effect_throw [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool) (value : Value) :
    interpret target ordinary (effects.throw value) = target.throw value := by
  change interpret target ordinary (perform (.throw value)) = _
  simp [interpretOp]

@[simp] theorem interpret_raiseTypeError [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (message : String) {α : Type} :
    interpret target ordinary
        (CoercionEffects.raiseTypeError effects message : CoercionProgram α) =
      (CoercionEffects.raiseTypeError target message : m α) := by
  unfold CoercionEffects.raiseTypeError
  rw [interpret_terminal, interpret_effect_typeError]

@[simp] theorem interpret_ordinaryHasInstance [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (constructor : RefId) (value : Value) :
    interpret target ordinary (ordinaryHasInstanceEffect constructor value) = ordinary constructor value := by
  simp [ordinaryHasInstanceEffect, interpretOp]

private theorem interpret_fromCoercion [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (result : Except CoercionFault α) :
    interpret target ordinary (CoercionEffects.fromCoercion effects result) =
      CoercionEffects.fromCoercion target result := by
  cases result <;> simp [CoercionEffects.fromCoercion]

theorem interpret_getMethodWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (ref : RefId) (key : PropertyKey) :
    interpret target ordinary (AbstractOperations.getMethodWith effects ref key) =
      AbstractOperations.getMethodWith target ref key := by
  simp only [AbstractOperations.getMethodWith, interpret_bind, interpret_effect_get]
  congr
  funext value
  cases value with
  | primitive primitive => cases primitive <;> simp
  | object method =>
      simp only [interpret_bind, interpret_effect_isCallable]
      congr
      funext callable
      cases callable <;> simp

theorem interpret_tryOrdinaryMethodWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (receiver : RefId) (name : String) :
    interpret target ordinary (AbstractOperations.tryOrdinaryMethodWith effects receiver name) =
      AbstractOperations.tryOrdinaryMethodWith target receiver name := by
  simp only [AbstractOperations.tryOrdinaryMethodWith, interpret_bind, interpret_effect_get]
  congr
  funext methodValue
  cases methodValue with
  | primitive primitive => simp
  | object method =>
      simp only [interpret_bind, interpret_effect_isCallable]
      congr
      funext callable
      cases callable
      · simp
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, interpret_bind,
          interpret_effect_call]
        congr
        funext result
        cases result <;> simp

theorem interpret_tryOrdinaryMethodsWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (receiver : RefId) (names : List String) :
    interpret target ordinary (AbstractOperations.tryOrdinaryMethodsWith effects receiver names) =
      AbstractOperations.tryOrdinaryMethodsWith target receiver names := by
  induction names with
  | nil => simp [AbstractOperations.tryOrdinaryMethodsWith]
  | cons name rest induction =>
      simp only [AbstractOperations.tryOrdinaryMethodsWith, interpret_bind,
        interpret_tryOrdinaryMethodWith]
      congr
      funext result
      cases result <;> simp [induction]

theorem interpret_ordinaryToPrimitiveWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (receiver : RefId) (hint : PreferredType) :
    interpret target ordinary (AbstractOperations.ordinaryToPrimitiveWith effects receiver hint) =
      AbstractOperations.ordinaryToPrimitiveWith target receiver hint := by
  cases hint <;> simp [AbstractOperations.ordinaryToPrimitiveWith,
    interpret_tryOrdinaryMethodsWith]

theorem interpret_toPrimitiveWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (value : Value) (hint : PreferredType) :
    interpret target ordinary (AbstractOperations.toPrimitiveWith effects value hint) =
      AbstractOperations.toPrimitiveWith target value hint := by
  cases value with
  | primitive primitive => simp [AbstractOperations.toPrimitiveWith]
  | object receiver =>
      simp only [AbstractOperations.toPrimitiveWith, interpret_bind, interpret_getMethodWith]
      congr
      funext method
      cases method with
      | none => exact interpret_ordinaryToPrimitiveWith target ordinary receiver hint
      | some method =>
          simp only [interpret_bind, interpret_effect_call]
          congr
          funext result
          cases result <;> simp

theorem interpret_toNumberWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (value : Value) :
    interpret target ordinary (AbstractOperations.toNumberWith effects value) =
      AbstractOperations.toNumberWith target value := by
  simp only [AbstractOperations.toNumberWith, interpret_bind, interpret_toPrimitiveWith]
  congr
  funext primitive
  exact interpret_fromCoercion target ordinary primitive.toNumber

theorem interpret_toStringWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (value : Value) :
    interpret target ordinary (AbstractOperations.toStringWith effects value) =
      AbstractOperations.toStringWith target value := by
  simp only [AbstractOperations.toStringWith, interpret_bind, interpret_toPrimitiveWith]
  congr
  funext primitive
  exact interpret_fromCoercion target ordinary primitive.toString

theorem interpret_toNumericWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (value : Value) :
    interpret target ordinary (AbstractOperations.toNumericWith effects value) =
      AbstractOperations.toNumericWith target value := by
  simp only [AbstractOperations.toNumericWith, interpret_bind, interpret_toPrimitiveWith]
  congr
  funext primitive
  exact interpret_fromCoercion target ordinary primitive.toNumeric

theorem interpret_toPropertyKeyWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (value : Value) :
    interpret target ordinary (AbstractOperations.toPropertyKeyWith effects value) =
      AbstractOperations.toPropertyKeyWith target value := by
  simp only [AbstractOperations.toPropertyKeyWith, interpret_bind, interpret_toPrimitiveWith]
  congr
  funext primitive
  exact interpret_fromCoercion target ordinary primitive.toPropertyKey

theorem interpret_looseEqualWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (left right : Value) :
    interpret target ordinary (AbstractEquality.looseEqualWith effects left right) =
      AbstractEquality.looseEqualWith target left right := by
  cases left with
  | primitive leftPrimitive =>
      cases right with
      | primitive rightPrimitive => simp [AbstractEquality.looseEqualWith]
      | object rightRef =>
          cases leftPrimitive <;>
            simp [AbstractEquality.looseEqualWith, AbstractEquality.primitiveAgainstObjectWith,
              AbstractEquality.nullish, interpret_map, interpret_toPrimitiveWith]
  | object leftRef =>
      cases right with
      | primitive rightPrimitive =>
          cases rightPrimitive <;>
            simp [AbstractEquality.looseEqualWith, AbstractEquality.primitiveAgainstObjectWith,
              AbstractEquality.nullish, interpret_map, interpret_toPrimitiveWith]
      | object rightRef => simp [AbstractEquality.looseEqualWith]

private theorem interpret_addPrimitivesWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (left right : Primitive) :
    interpret target ordinary (AbstractEquality.addPrimitivesWith effects left right) =
      AbstractEquality.addPrimitivesWith target left right := by
  cases left <;> cases right <;>
    simp [AbstractEquality.addPrimitivesWith, interpret_bind, interpret_map,
      interpret_fromCoercion]

theorem interpret_addWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (left right : Value) :
    interpret target ordinary (AbstractEquality.addWith effects left right) =
      AbstractEquality.addWith target left right := by
  simp only [AbstractEquality.addWith, interpret_bind, interpret_toPrimitiveWith]
  congr
  funext leftPrimitive
  congr
  funext rightPrimitive
  exact interpret_addPrimitivesWith target ordinary leftPrimitive rightPrimitive

private theorem interpret_orderedPrimitivesWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (left right : Value) (leftFirst : Bool) :
    interpret target ordinary
        (AbstractEquality.orderedPrimitivesWith effects left right leftFirst) =
      AbstractEquality.orderedPrimitivesWith target left right leftFirst := by
  cases leftFirst <;>
    simp [AbstractEquality.orderedPrimitivesWith, interpret_bind, interpret_map,
      interpret_toPrimitiveWith]

theorem interpret_relationalComparisonWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (left right : Value) (leftFirst : Bool) :
    interpret target ordinary
        (AbstractEquality.relationalComparisonWith effects left right leftFirst) =
      AbstractEquality.relationalComparisonWith target left right leftFirst := by
  simp only [AbstractEquality.relationalComparisonWith, interpret_bind,
    interpret_orderedPrimitivesWith]
  congr
  funext primitives
  exact interpret_fromCoercion target ordinary
    (Primitive.abstractRelationalComparison primitives.1 primitives.2 leftFirst)

theorem interpret_lessThanWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (left right : Value) :
    interpret target ordinary (AbstractEquality.lessThanWith effects left right) =
      AbstractEquality.lessThanWith target left right := by
  change interpret target ordinary
      ((fun result => result.getD false) <$>
        AbstractEquality.relationalComparisonWith effects left right) = _
  rw [interpret_map, interpret_relationalComparisonWith]
  unfold AbstractEquality.lessThanWith
  exact (LawfulMonad.bind_pure_comp (fun result => result.getD false)
    (AbstractEquality.relationalComparisonWith target left right)).symm

theorem interpret_greaterThanWith [Monad m] [LawfulMonad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (left right : Value) :
    interpret target ordinary (AbstractEquality.greaterThanWith effects left right) =
      AbstractEquality.greaterThanWith target left right := by
  change interpret target ordinary
      ((fun result => result.getD false) <$>
        AbstractEquality.relationalComparisonWith effects right left false) = _
  rw [interpret_map, interpret_relationalComparisonWith]
  unfold AbstractEquality.greaterThanWith
  exact (LawfulMonad.bind_pure_comp (fun result => result.getD false)
    (AbstractEquality.relationalComparisonWith target right left false)).symm

theorem interpret_lessThanOrEqualWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool) (left right : Value) :
    interpret target ordinary (AbstractEquality.lessThanOrEqualWith effects left right) =
      AbstractEquality.lessThanOrEqualWith target left right := by
  simp only [AbstractEquality.lessThanOrEqualWith, interpret_bind,
    interpret_relationalComparisonWith]
  congr
  funext result
  cases result with
  | none => rfl
  | some value => cases value <;> rfl

theorem interpret_greaterThanOrEqualWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool) (left right : Value) :
    interpret target ordinary (AbstractEquality.greaterThanOrEqualWith effects left right) =
      AbstractEquality.greaterThanOrEqualWith target left right := by
  simp only [AbstractEquality.greaterThanOrEqualWith, interpret_bind,
    interpret_relationalComparisonWith]
  congr
  funext result
  cases result with
  | none => rfl
  | some value => cases value <;> rfl

theorem interpret_instanceofOperatorWith [Monad m] [LawfulMonad m]
    (target : CoercionEffects m) (ordinary : RefId → Value → m Bool)
    (value constructor : Value) :
    interpret target ordinary
        (Instanceof.instanceofOperatorWith effects ordinaryHasInstanceEffect value constructor) =
      Instanceof.instanceofOperatorWith target ordinary value constructor := by
  cases constructor with
  | primitive primitive => simp [Instanceof.instanceofOperatorWith]
  | object constructorRef =>
      simp only [Instanceof.instanceofOperatorWith, interpret_bind, interpret_getMethodWith]
      congr
      funext method
      cases method with
      | some method => simp [interpret_map]
      | none =>
          simp only [interpret_bind, interpret_effect_isCallable]
          congr
          funext callable
          cases callable <;> simp

/-- A fully parameterized operation recorded by the scripted interpreter. -/
inductive TraceEvent where
  | get (ref : RefId) (key : PropertyKey) (receiver : Value)
  | call (callee : RefId) (receiver : Value) (arguments : Array Value)
  | isCallable (ref : RefId)
  | ordinaryHasInstance (constructor : RefId) (value : Value)
  | typeError (message : String)
  | throw (value : Value)
  deriving DecidableEq

/-- Typed responses consumed by nonterminal scripted operations. -/
inductive ScriptResponse where
  | get (value : Value)
  | call (value : Value)
  | isCallable (value : Bool)
  | ordinaryHasInstance (value : Bool)
  deriving DecidableEq

/-- Total failures for missing, mistyped, or terminal scripted interactions. -/
inductive ScriptFault where
  | missing (operation : TraceEvent)
  | unexpected (operation : TraceEvent) (response : ScriptResponse)
  | typeError (message : String)
  | thrown (value : Value)
  deriving DecidableEq

/-- Script queue, ordered trace, and a state-changing allocation counter. -/
structure ScriptState where
  responses : List ScriptResponse
  trace : List TraceEvent := []
  allocations : Nat := 0
  typeErrorPrefix : String := "TypeError: "
  deriving DecidableEq

/-- A script always retains the final state, including on faults. -/
inductive ScriptResult (α : Type) where
  | ok (value : α) (state : ScriptState)
  | fault (fault : ScriptFault) (state : ScriptState)
  deriving DecidableEq

/-- Extracts the committed final script state. -/
@[simp] def ScriptResult.state : ScriptResult α → ScriptState
  | .ok _ state | .fault _ state => state

/-- Total state-and-fault monad used only for coercion proofs and tests. -/
abbrev ScriptM (α : Type) := ScriptState → ScriptResult α

private def scriptBind (action : ScriptM α) (next : α → ScriptM β) : ScriptM β :=
  fun state =>
    match action state with
    | .ok value nextState => next value nextState
    | .fault fault nextState => .fault fault nextState

instance : Monad ScriptM where
  pure value state := .ok value state
  bind := scriptBind

/-- The total scripted state/fault interpreter satisfies the monad laws. -/
instance : LawfulMonad ScriptM := LawfulMonad.mk' ScriptM
  (by
    intro α action
    funext state
    change scriptBind action (fun value => (Pure.pure : α → ScriptM α) (id value)) state = action state
    unfold scriptBind
    change (match action state with
      | .ok value nextState => .ok (id value) nextState
      | .fault fault nextState => .fault fault nextState) = action state
    cases action state <;> rfl)
  (by intros; rfl)
  (by
    intro α β γ action next last
    funext state
    change scriptBind (scriptBind action next) last state =
      scriptBind action (fun value => scriptBind (next value) last) state
    unfold scriptBind
    cases action state with
    | fault fault nextState => rfl
    | ok value nextState => cases next value nextState <;> rfl)

@[simp] private theorem script_bind_apply (action : ScriptM α) (next : α → ScriptM β)
    (state : ScriptState) :
    (action >>= next) state = scriptBind action next state := rfl

@[simp] private theorem script_pure_apply (value : α) (state : ScriptState) :
    (Pure.pure value : ScriptM α) state = .ok value state := rfl

private def record (state : ScriptState) (event : TraceEvent) : ScriptState :=
  { state with trace := state.trace ++ [event] }

private def consume (state : ScriptState) (event : TraceEvent)
    (accept : ScriptResponse → Option α) : ScriptResult α :=
  let recorded := record state event
  match state.responses with
  | [] => .fault (.missing event) recorded
  | response :: rest =>
      match accept response with
      | none => .fault (.unexpected event response) recorded
      | some value => .ok value {
          recorded with responses := rest, allocations := state.allocations + 1 }

/-- Concrete scripted coercion effects. No response is synthesized. -/
def scriptedEffects : CoercionEffects ScriptM where
  get ref key receiver state :=
    consume state (.get ref key receiver) fun
      | .get value => some value
      | _ => none
  call callee receiver arguments state :=
    consume state (.call callee receiver arguments) fun
      | .call value => some value
      | _ => none
  isCallable ref state :=
    consume state (.isCallable ref) fun
      | .isCallable value => some value
      | _ => none
  typeError message state :=
    let state := record state (.typeError message)
    .fault (.typeError (state.typeErrorPrefix ++ message)) state
  throw value state :=
    let state := record state (.throw value)
    .fault (.thrown value) state

/-- Scripted interpretation of the explicit ordinary `instanceof` fallback. -/
def scriptedOrdinaryHasInstance (constructor : RefId) (value : Value) : ScriptM Bool :=
  fun state => consume state (.ordinaryHasInstance constructor value) fun
    | .ordinaryHasInstance result => some result
    | _ => none

/-- Executes a free coercion program against a typed response script. -/
def execute (program : CoercionProgram α) : ScriptM α :=
  interpret scriptedEffects scriptedOrdinaryHasInstance program

private def ScriptResponse.get? : ScriptResponse → Option Value
  | .get value => some value
  | _ => none

private def ScriptResponse.call? : ScriptResponse → Option Value
  | .call value => some value
  | _ => none

private def ScriptResponse.callable? : ScriptResponse → Option Bool
  | .isCallable value => some value
  | _ => none

private def ScriptResponse.ordinary? : ScriptResponse → Option Bool
  | .ordinaryHasInstance value => some value
  | _ => none

/-- Exact big-step semantics for a free coercion program and response script. -/
inductive Executes : CoercionProgram α → ScriptState → ScriptResult α → Prop where
  | pure (value : α) (state : ScriptState) : Executes (.pure value) state (.ok value state)
  | getSuccess (ref : RefId) (key : PropertyKey) (receiver value : Value)
      (next : Value → CoercionProgram α) (rest : List ScriptResponse)
      (trace : List TraceEvent) (allocations : Nat) (errorPrefix : String) (result : ScriptResult α)
      (continued : Executes (next value) {
        responses := rest, trace := trace ++ [.get ref key receiver],
        allocations := allocations + 1, typeErrorPrefix := errorPrefix } result) :
      Executes (.get ref key receiver next) {
        responses := .get value :: rest, trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix } result
  | getMissing (ref : RefId) (key : PropertyKey) (receiver : Value)
      (next : Value → CoercionProgram α) (trace : List TraceEvent) (allocations : Nat)
      (errorPrefix : String) :
      Executes (.get ref key receiver next) {
        responses := [], trace := trace, allocations := allocations, typeErrorPrefix := errorPrefix }
        (.fault (.missing (.get ref key receiver)) {
          responses := [], trace := trace ++ [.get ref key receiver], allocations,
          typeErrorPrefix := errorPrefix })
  | getMistyped (ref : RefId) (key : PropertyKey) (receiver : Value)
      (next : Value → CoercionProgram α) (response : ScriptResponse)
      (rest : List ScriptResponse) (trace : List TraceEvent) (allocations : Nat)
      (errorPrefix : String) (wrong : response.get? = none) :
      Executes (.get ref key receiver next) {
        responses := response :: rest, trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix }
        (.fault (.unexpected (.get ref key receiver) response) {
          responses := response :: rest, trace := trace ++ [.get ref key receiver], allocations,
          typeErrorPrefix := errorPrefix })
  | callSuccess (callee : RefId) (receiver value : Value) (arguments : Array Value)
      (next : Value → CoercionProgram α) (rest : List ScriptResponse)
      (trace : List TraceEvent) (allocations : Nat) (errorPrefix : String) (result : ScriptResult α)
      (continued : Executes (next value) {
        responses := rest, trace := trace ++ [.call callee receiver arguments],
        allocations := allocations + 1, typeErrorPrefix := errorPrefix } result) :
      Executes (.call callee receiver arguments next) {
        responses := .call value :: rest, trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix } result
  | callMissing (callee : RefId) (receiver : Value) (arguments : Array Value)
      (next : Value → CoercionProgram α) (trace : List TraceEvent) (allocations : Nat)
      (errorPrefix : String) :
      Executes (.call callee receiver arguments next) {
        responses := [], trace := trace, allocations := allocations, typeErrorPrefix := errorPrefix }
        (.fault (.missing (.call callee receiver arguments)) {
          responses := [], trace := trace ++ [.call callee receiver arguments], allocations,
          typeErrorPrefix := errorPrefix })
  | callMistyped (callee : RefId) (receiver : Value) (arguments : Array Value)
      (next : Value → CoercionProgram α) (response : ScriptResponse)
      (rest : List ScriptResponse) (trace : List TraceEvent) (allocations : Nat)
      (errorPrefix : String) (wrong : response.call? = none) :
      Executes (.call callee receiver arguments next) {
        responses := response :: rest, trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix }
        (.fault (.unexpected (.call callee receiver arguments) response) {
          responses := response :: rest, trace := trace ++ [.call callee receiver arguments], allocations,
          typeErrorPrefix := errorPrefix })
  | callableSuccess (ref : RefId) (value : Bool) (next : Bool → CoercionProgram α)
      (rest : List ScriptResponse) (trace : List TraceEvent) (allocations : Nat)
      (errorPrefix : String) (result : ScriptResult α)
      (continued : Executes (next value) {
        responses := rest, trace := trace ++ [.isCallable ref], allocations := allocations + 1,
        typeErrorPrefix := errorPrefix } result) :
      Executes (.isCallable ref next) {
        responses := .isCallable value :: rest, trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix } result
  | callableMissing (ref : RefId) (next : Bool → CoercionProgram α)
      (trace : List TraceEvent) (allocations : Nat) (errorPrefix : String) :
      Executes (.isCallable ref next) ({
        responses := ([] : List ScriptResponse), trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix } : ScriptState)
        (.fault (.missing (.isCallable ref)) {
          responses := [], trace := trace ++ [.isCallable ref], allocations := allocations,
          typeErrorPrefix := errorPrefix })
  | callableMistyped (ref : RefId) (next : Bool → CoercionProgram α)
      (response : ScriptResponse) (rest : List ScriptResponse) (trace : List TraceEvent)
      (allocations : Nat) (errorPrefix : String) (wrong : response.callable? = none) :
      Executes (.isCallable ref next) ({
        responses := response :: rest
        trace := trace
        allocations := allocations
        typeErrorPrefix := errorPrefix
      } : ScriptState) (.fault (.unexpected (.isCallable ref) response) {
        responses := response :: rest
        trace := trace ++ [.isCallable ref]
        allocations := allocations
        typeErrorPrefix := errorPrefix
      })
  | ordinarySuccess (constructor : RefId) (value : Value) (answer : Bool)
      (next : Bool → CoercionProgram α) (rest : List ScriptResponse)
      (trace : List TraceEvent) (allocations : Nat) (errorPrefix : String) (result : ScriptResult α)
      (continued : Executes (next answer) {
        responses := rest, trace := trace ++ [.ordinaryHasInstance constructor value],
        allocations := allocations + 1, typeErrorPrefix := errorPrefix } result) :
      Executes (.ordinaryHasInstance constructor value next) {
        responses := .ordinaryHasInstance answer :: rest, trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix } result
  | ordinaryMissing (constructor : RefId) (value : Value)
      (next : Bool → CoercionProgram α) (trace : List TraceEvent) (allocations : Nat)
      (errorPrefix : String) :
      Executes (.ordinaryHasInstance constructor value next) {
        responses := [], trace := trace, allocations := allocations, typeErrorPrefix := errorPrefix }
        (.fault (.missing (.ordinaryHasInstance constructor value)) {
          responses := [], trace := trace ++ [.ordinaryHasInstance constructor value], allocations,
          typeErrorPrefix := errorPrefix })
  | ordinaryMistyped (constructor : RefId) (value : Value)
      (next : Bool → CoercionProgram α) (response : ScriptResponse)
      (rest : List ScriptResponse) (trace : List TraceEvent) (allocations : Nat)
      (errorPrefix : String) (wrong : response.ordinary? = none) :
      Executes (.ordinaryHasInstance constructor value next) {
        responses := response :: rest, trace := trace, allocations := allocations,
        typeErrorPrefix := errorPrefix }
        (.fault (.unexpected (.ordinaryHasInstance constructor value) response) {
          responses := response :: rest, trace := trace ++ [.ordinaryHasInstance constructor value],
          allocations := allocations, typeErrorPrefix := errorPrefix })
  | typeError (message : String) (responses : List ScriptResponse) (trace : List TraceEvent)
      (allocations : Nat) (errorPrefix : String) :
      Executes (.typeError message) ({
        responses := responses
        trace := trace
        allocations := allocations
        typeErrorPrefix := errorPrefix
      } : ScriptState)
        (.fault (.typeError (errorPrefix ++ message)) {
          responses := responses, trace := trace ++ [.typeError message],
          allocations := allocations, typeErrorPrefix := errorPrefix })
  | throw (value : Value) (responses : List ScriptResponse) (trace : List TraceEvent)
      (allocations : Nat) (errorPrefix : String) :
      Executes (.throw value) ({
        responses := responses
        trace := trace
        allocations := allocations
        typeErrorPrefix := errorPrefix
      } : ScriptState)
        (.fault (.thrown value) {
          responses := responses, trace := trace ++ [.throw value],
          allocations := allocations, typeErrorPrefix := errorPrefix })

/-- Exact big-step derivations are sound for the scripted interpreter. -/
theorem Executes.sound (execution : Executes program initial result) :
    execute program initial = result := by
  induction execution <;>
    simp_all [execute, interpret, scriptedEffects, scriptedOrdinaryHasInstance,
      consume, record, scriptBind, script_bind_apply, ScriptResponse.get?, ScriptResponse.call?,
      ScriptResponse.callable?, ScriptResponse.ordinary?, CoercionEffects.terminal]

/-- Every scripted interpreter run has an exact big-step derivation. -/
theorem Executes.complete (program : CoercionProgram α) (state : ScriptState) :
    Executes program state (execute program state) := by
  induction program generalizing state with
  | pure value => exact .pure value state
  | get ref key receiver next induction =>
      rcases state with ⟨responses, trace, allocations, errorPrefix⟩
      cases responses with
      | nil => exact .getMissing ref key receiver next trace allocations errorPrefix
      | cons response rest =>
          cases response with
          | get value =>
              exact .getSuccess ref key receiver value next rest trace allocations errorPrefix _
                (induction value _)
          | call value | isCallable value | ordinaryHasInstance value =>
              exact .getMistyped ref key receiver next _ rest trace allocations errorPrefix rfl
  | call callee receiver arguments next induction =>
      rcases state with ⟨responses, trace, allocations, errorPrefix⟩
      cases responses with
      | nil => exact .callMissing callee receiver arguments next trace allocations errorPrefix
      | cons response rest =>
          cases response with
          | call value =>
              exact .callSuccess callee receiver value arguments next rest trace allocations
                errorPrefix _ (induction value _)
          | get value | isCallable value | ordinaryHasInstance value =>
              exact .callMistyped callee receiver arguments next _ rest trace allocations
                errorPrefix rfl
  | isCallable ref next induction =>
      rcases state with ⟨responses, trace, allocations, errorPrefix⟩
      cases responses with
      | nil => exact .callableMissing ref next trace allocations errorPrefix
      | cons response rest =>
          cases response with
          | isCallable value =>
              exact .callableSuccess ref value next rest trace allocations errorPrefix _
                (induction value _)
          | get value | call value | ordinaryHasInstance value =>
              exact .callableMistyped ref next _ rest trace allocations errorPrefix rfl
  | ordinaryHasInstance constructor value next induction =>
      rcases state with ⟨responses, trace, allocations, errorPrefix⟩
      cases responses with
      | nil => exact .ordinaryMissing constructor value next trace allocations errorPrefix
      | cons response rest =>
          cases response with
          | ordinaryHasInstance answer =>
              exact .ordinarySuccess constructor value answer next rest trace allocations
                errorPrefix _ (induction answer _)
          | get wrongValue =>
              exact .ordinaryMistyped constructor value next (.get wrongValue) rest trace allocations
                errorPrefix rfl
          | call wrongValue =>
              exact .ordinaryMistyped constructor value next (.call wrongValue) rest trace allocations
                errorPrefix rfl
          | isCallable wrongValue =>
              exact .ordinaryMistyped constructor value next (.isCallable wrongValue) rest trace allocations
                errorPrefix rfl
  | typeError message =>
      rcases state with ⟨responses, trace, allocations, errorPrefix⟩
      exact .typeError message responses trace allocations errorPrefix
  | throw value =>
      rcases state with ⟨responses, trace, allocations, errorPrefix⟩
      exact .throw value responses trace allocations errorPrefix

/-- The exact big-step semantics is equivalent to interpreter execution. -/
theorem executes_iff : Executes program initial result ↔ execute program initial = result :=
  ⟨Executes.sound, fun run => run ▸ Executes.complete program initial⟩

/-- Exact scripted execution is deterministic. -/
theorem Executes.deterministic (left : Executes program initial leftResult)
    (right : Executes program initial rightResult) : leftResult = rightResult := by
  rw [← left.sound, ← right.sound]

/-- Big-step execution preserves the initial trace as an exact prefix. -/
theorem Executes.tracePrefix (execution : Executes program initial result) :
    ∃ suffix, result.state.trace = initial.trace ++ suffix := by
  induction execution with
  | pure => exact ⟨[], by simp⟩
  | getSuccess ref key receiver value next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨suffix, equal⟩ := ih
      exact ⟨.get ref key receiver :: suffix, by simpa [List.append_assoc] using equal⟩
  | callSuccess callee receiver value arguments next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨suffix, equal⟩ := ih
      exact ⟨.call callee receiver arguments :: suffix, by simpa [List.append_assoc] using equal⟩
  | callableSuccess ref value next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨suffix, equal⟩ := ih
      exact ⟨.isCallable ref :: suffix, by simpa [List.append_assoc] using equal⟩
  | ordinarySuccess constructor value answer next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨suffix, equal⟩ := ih
      exact ⟨.ordinaryHasInstance constructor value :: suffix,
        by simpa [List.append_assoc] using equal⟩
  | getMissing ref key receiver next trace allocations errorPrefix =>
      exact ⟨[.get ref key receiver], rfl⟩
  | getMistyped ref key receiver next response rest trace allocations errorPrefix wrong =>
      exact ⟨[.get ref key receiver], rfl⟩
  | callMissing callee receiver arguments next trace allocations errorPrefix =>
      exact ⟨[.call callee receiver arguments], rfl⟩
  | callMistyped callee receiver arguments next response rest trace allocations errorPrefix wrong =>
      exact ⟨[.call callee receiver arguments], rfl⟩
  | callableMissing ref next trace allocations errorPrefix => exact ⟨[.isCallable ref], rfl⟩
  | callableMistyped ref next response rest trace allocations errorPrefix wrong =>
      exact ⟨[.isCallable ref], rfl⟩
  | ordinaryMissing constructor value next trace allocations errorPrefix =>
      exact ⟨[.ordinaryHasInstance constructor value], rfl⟩
  | ordinaryMistyped constructor value next response rest trace allocations errorPrefix wrong =>
      exact ⟨[.ordinaryHasInstance constructor value], rfl⟩
  | typeError message responses trace allocations errorPrefix =>
      exact ⟨[.typeError message], by simp⟩
  | throw value responses trace allocations errorPrefix => exact ⟨[.throw value], by simp⟩

/-- The first syntax operation contributes exactly one first trace event before its continuation. -/
def FirstEvent (program : CoercionProgram α) (initial : ScriptState)
    (result : ScriptResult α) : Prop :=
  match program with
  | .pure _ => result.state.trace = initial.trace
  | .get ref key receiver _ =>
      ∃ suffix, result.state.trace = initial.trace ++ .get ref key receiver :: suffix
  | .call callee receiver arguments _ =>
      ∃ suffix, result.state.trace = initial.trace ++ .call callee receiver arguments :: suffix
  | .isCallable ref _ =>
      ∃ suffix, result.state.trace = initial.trace ++ .isCallable ref :: suffix
  | .ordinaryHasInstance constructor value _ =>
      ∃ suffix, result.state.trace = initial.trace ++ .ordinaryHasInstance constructor value :: suffix
  | .typeError message => result.state.trace = initial.trace ++ [.typeError message]
  | .throw value => result.state.trace = initial.trace ++ [.throw value]

/-- Every exact execution satisfies its constructor-specific first-event equation. -/
theorem Executes.firstEvent (execution : Executes program initial result) :
    FirstEvent program initial result := by
  cases execution with
  | pure => rfl
  | getSuccess ref key receiver value next rest trace allocations errorPrefix result continued =>
      obtain ⟨suffix, equal⟩ := continued.tracePrefix
      exact ⟨suffix, by simpa [List.append_assoc] using equal⟩
  | callSuccess callee receiver value arguments next rest trace allocations errorPrefix result continued =>
      obtain ⟨suffix, equal⟩ := continued.tracePrefix
      exact ⟨suffix, by simpa [List.append_assoc] using equal⟩
  | callableSuccess ref value next rest trace allocations errorPrefix result continued =>
      obtain ⟨suffix, equal⟩ := continued.tracePrefix
      exact ⟨suffix, by simpa [List.append_assoc] using equal⟩
  | ordinarySuccess constructor value answer next rest trace allocations errorPrefix result continued =>
      obtain ⟨suffix, equal⟩ := continued.tracePrefix
      exact ⟨suffix, by simpa [List.append_assoc] using equal⟩
  | getMissing ref key receiver next trace allocations errorPrefix => exact ⟨[], rfl⟩
  | getMistyped ref key receiver next response rest trace allocations errorPrefix wrong =>
      exact ⟨[], rfl⟩
  | callMissing callee receiver arguments next trace allocations errorPrefix => exact ⟨[], rfl⟩
  | callMistyped callee receiver arguments next response rest trace allocations errorPrefix wrong =>
      exact ⟨[], rfl⟩
  | callableMissing ref next trace allocations errorPrefix => exact ⟨[], rfl⟩
  | callableMistyped ref next response rest trace allocations errorPrefix wrong => exact ⟨[], rfl⟩
  | ordinaryMissing constructor value next trace allocations errorPrefix => exact ⟨[], rfl⟩
  | ordinaryMistyped constructor value next response rest trace allocations errorPrefix wrong =>
      exact ⟨[], rfl⟩
  | typeError => rfl
  | throw => rfl

/-- Response removal and allocation increments agree exactly. -/
theorem Executes.responsesAndAllocations (execution : Executes program initial result) :
    ∃ consumed, initial.responses = consumed ++ result.state.responses ∧
      result.state.allocations = initial.allocations + consumed.length := by
  induction execution with
  | pure => exact ⟨[], by simp⟩
  | getSuccess ref key receiver value next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨consumed, responses, allocated⟩ := ih
      refine ⟨.get value :: consumed, by simpa using congrArg (List.cons (.get value)) responses, ?_⟩
      change result.state.allocations = (allocations + 1) + consumed.length at allocated
      change result.state.allocations = allocations + (consumed.length + 1)
      rw [allocated]
      omega
  | callSuccess callee receiver value arguments next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨consumed, responses, allocated⟩ := ih
      refine ⟨.call value :: consumed, by simpa using congrArg (List.cons (.call value)) responses, ?_⟩
      change result.state.allocations = (allocations + 1) + consumed.length at allocated
      change result.state.allocations = allocations + (consumed.length + 1)
      rw [allocated]
      omega
  | callableSuccess ref value next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨consumed, responses, allocated⟩ := ih
      refine ⟨.isCallable value :: consumed,
        by simpa using congrArg (List.cons (.isCallable value)) responses, ?_⟩
      change result.state.allocations = (allocations + 1) + consumed.length at allocated
      change result.state.allocations = allocations + (consumed.length + 1)
      rw [allocated]
      omega
  | ordinarySuccess constructor value answer next rest trace allocations errorPrefix result continued ih =>
      obtain ⟨consumed, responses, allocated⟩ := ih
      refine ⟨.ordinaryHasInstance answer :: consumed,
        by simpa using congrArg (List.cons (.ordinaryHasInstance answer)) responses, ?_⟩
      change result.state.allocations = (allocations + 1) + consumed.length at allocated
      change result.state.allocations = allocations + (consumed.length + 1)
      rw [allocated]
      omega
  | getMissing | getMistyped | callMissing | callMistyped | callableMissing |
    callableMistyped | ordinaryMissing | ordinaryMistyped | typeError | throw =>
      exact ⟨[], rfl, rfl⟩

/-- Interpretation threads a `get` result directly into its continuation. -/
theorem interpret_get_threads [Monad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (ref : RefId) (key : PropertyKey)
    (receiver : Value) (next : Value → CoercionProgram α) :
    interpret target ordinary (.get ref key receiver next) = (do
      let value ← target.get ref key receiver
      interpret target ordinary (next value)) := rfl

/-- Interpretation threads a call result directly into its continuation. -/
theorem interpret_call_threads [Monad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (callee : RefId) (receiver : Value)
    (arguments : Array Value) (next : Value → CoercionProgram α) :
    interpret target ordinary (.call callee receiver arguments next) = (do
      let value ← target.call callee receiver arguments
      interpret target ordinary (next value)) := rfl

/-- Interpretation threads a callability result directly into its continuation. -/
theorem interpret_isCallable_threads [Monad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (ref : RefId)
    (next : Bool → CoercionProgram α) :
    interpret target ordinary (.isCallable ref next) = (do
      let value ← target.isCallable ref
      interpret target ordinary (next value)) := rfl

/-- The ordinary-instance boundary is atomic and threads its result to the continuation. -/
theorem interpret_ordinary_threads [Monad m] (target : CoercionEffects m)
    (ordinary : RefId → Value → m Bool) (constructor : RefId) (value : Value)
    (next : Bool → CoercionProgram α) :
    interpret target ordinary (.ordinaryHasInstance constructor value next) = (do
      let result ← ordinary constructor value
      interpret target ordinary (next result)) := rfl

/-- GetMethod's first syntax operation is exactly its receiver property read. -/
theorem getMethod_startsWithGet (ref : RefId) (key : PropertyKey) :
    AbstractOperations.getMethodWith effects ref key =
      .get ref key (.object ref) (fun value =>
        match value with
        | .primitive .undefined | .primitive .null => pure none
        | .primitive _ => CoercionEffects.raiseTypeError effects "property is not callable"
        | .object method => do
            if ← effects.isCallable method then pure (some method)
            else CoercionEffects.raiseTypeError effects "property is not callable") := rfl

/-- A generated GetMethod program consumes exactly two responses in protocol order. -/
theorem getMethod_executes_two_operations (ref method : RefId) (key : PropertyKey)
    (remaining : List ScriptResponse) (trace : List TraceEvent) (allocations : Nat)
    (errorPrefix : String) :
    Executes (AbstractOperations.getMethodWith effects ref key) {
      responses := [.get (.object method), .isCallable true] ++ remaining
      trace := trace
      allocations := allocations
      typeErrorPrefix := errorPrefix
    } (.ok (some method) {
      responses := remaining
      trace := trace ++ [.get ref key (.object ref), .isCallable method]
      allocations := allocations + 2
      typeErrorPrefix := errorPrefix
    }) := by
  rw [getMethod_startsWithGet]
  apply Executes.getSuccess
  apply Executes.callableSuccess
  simpa [CoercionProgram.bind, List.append_assoc, Nat.add_assoc] using
    (Executes.pure (some method) {
      responses := remaining
      trace := trace ++ [.get ref key (.object ref), .isCallable method]
      allocations := allocations + 2
      typeErrorPrefix := errorPrefix
    })

/-- Reversing the exact generated GetMethod trace cannot satisfy big-step execution. -/
theorem getMethod_reversed_trace_impossible :
    ¬Executes (AbstractOperations.getMethodWith effects ⟨1⟩
        (.string (JSString.ofLeanString "method"))) {
      responses := [.get (.object ⟨2⟩), .isCallable true]
    } (.ok (some ⟨2⟩) {
      responses := []
      trace := [.isCallable ⟨2⟩,
        .get ⟨1⟩ (.string (JSString.ofLeanString "method")) (.object ⟨1⟩)]
      allocations := 2
    }) := by
  intro reversed
  have exact := getMethod_executes_two_operations ⟨1⟩ ⟨2⟩
    (.string (JSString.ofLeanString "method")) [] [] 0 "TypeError: "
  have equal := reversed.deterministic exact
  contradiction

/-- Resetting the trace cannot satisfy exact generated GetMethod execution. -/
theorem getMethod_reset_trace_impossible :
    ¬Executes (AbstractOperations.getMethodWith effects ⟨1⟩
        (.string (JSString.ofLeanString "method"))) {
      responses := [.get (.object ⟨2⟩), .isCallable true]
    } (.ok (some ⟨2⟩) { responses := [], trace := [], allocations := 2 }) := by
  intro reset
  have exact := getMethod_executes_two_operations ⟨1⟩ ⟨2⟩
    (.string (JSString.ofLeanString "method")) [] [] 0 "TypeError: "
  have equal := reset.deterministic exact
  contradiction

/-- Resetting allocation state cannot satisfy exact generated GetMethod execution. -/
theorem getMethod_reset_allocations_impossible :
    ¬Executes (AbstractOperations.getMethodWith effects ⟨1⟩
        (.string (JSString.ofLeanString "method"))) {
      responses := [.get (.object ⟨2⟩), .isCallable true]
    } (.ok (some ⟨2⟩) {
      responses := []
      trace := [.get ⟨1⟩ (.string (JSString.ofLeanString "method")) (.object ⟨1⟩),
        .isCallable ⟨2⟩]
      allocations := 0
    }) := by
  intro reset
  have exact := getMethod_executes_two_operations ⟨1⟩ ⟨2⟩
    (.string (JSString.ofLeanString "method")) [] [] 0 "TypeError: "
  have equal := reset.deterministic exact
  contradiction

/-- An unconsumed response must remain; consuming it again is not an exact outcome. -/
theorem getMethod_duplicate_consumption_impossible :
    ¬Executes (AbstractOperations.getMethodWith effects ⟨1⟩
        (.string (JSString.ofLeanString "method"))) {
      responses := [.get (.object ⟨2⟩), .isCallable true, .call (.primitive .undefined)]
    } (.ok (some ⟨2⟩) {
      responses := []
      trace := [.get ⟨1⟩ (.string (JSString.ofLeanString "method")) (.object ⟨1⟩),
        .isCallable ⟨2⟩]
      allocations := 2
    }) := by
  intro consumed
  have exact := getMethod_executes_two_operations ⟨1⟩ ⟨2⟩
    (.string (JSString.ofLeanString "method")) [.call (.primitive .undefined)] [] 0
      "TypeError: "
  have equal := consumed.deterministic exact
  contradiction

/-- Every generated coercion program has a total scripted execution. -/
theorem generated_programs_total :
    (∃ result, Executes (AbstractOperations.getMethodWith effects ⟨1⟩
        (.string (JSString.ofLeanString "method"))) {
          responses := [.get (.object ⟨2⟩), .isCallable true] } result) ∧
    (∃ result, Executes (AbstractOperations.toPrimitiveWith effects (.object ⟨3⟩) .number) {
          responses := [.get (.object ⟨4⟩), .isCallable true,
            .call (.primitive (.number JSNumber.one))] } result) ∧
    (∃ result, Executes (AbstractEquality.addWith effects (.object ⟨5⟩) (.object ⟨6⟩)) {
          responses := [.get (.object ⟨7⟩), .isCallable true,
            .call (.primitive (.number JSNumber.one)), .get (.object ⟨8⟩),
            .isCallable true, .call (.primitive (.number JSNumber.one))] } result) ∧
    (∃ result, Executes (Instanceof.instanceofOperatorWith effects ordinaryHasInstanceEffect
        (.object ⟨9⟩) (.object ⟨10⟩)) {
          responses := [.get (.primitive .undefined), .isCallable true,
            .ordinaryHasInstance true] } result) := by
  exact ⟨⟨_, Executes.complete _ _⟩, ⟨_, Executes.complete _ _⟩,
    ⟨_, Executes.complete _ _⟩, ⟨_, Executes.complete _ _⟩⟩

/-- Generated ToPrimitive consumes its exact exotic-method script in order. -/
theorem toPrimitive_generated_success :
    Executes (AbstractOperations.toPrimitiveWith effects (.object ⟨3⟩) .number) {
      responses := [.get (.object ⟨4⟩), .isCallable true,
        .call (.primitive (.number JSNumber.one))]
    } (.ok (.number JSNumber.one) {
      responses := []
      trace := [
        .get ⟨3⟩ (.symbol (.wellKnown .toPrimitive)) (.object ⟨3⟩),
        .isCallable ⟨4⟩,
        .call ⟨4⟩ (.object ⟨3⟩)
          #[.primitive (.string (JSString.ofLeanString "number"))]]
      allocations := 3
    }) := by
  rw [executes_iff]
  rfl

/-- Generated addition completes left coercion before right and consumes all six responses. -/
theorem add_generated_success :
    Executes (AbstractEquality.addWith effects (.object ⟨5⟩) (.object ⟨6⟩)) {
      responses := [
        .get (.object ⟨7⟩), .isCallable true,
        .call (.primitive (.string (JSString.ofLeanString "left"))),
        .get (.object ⟨8⟩), .isCallable true,
        .call (.primitive (.string (JSString.ofLeanString "right")))]
    } (.ok (.primitive (.string
        ((JSString.ofLeanString "left").append (JSString.ofLeanString "right")))) {
      responses := []
      trace := [
        .get ⟨5⟩ (.symbol (.wellKnown .toPrimitive)) (.object ⟨5⟩),
        .isCallable ⟨7⟩,
        .call ⟨7⟩ (.object ⟨5⟩)
          #[.primitive (.string (JSString.ofLeanString "default"))],
        .get ⟨6⟩ (.symbol (.wellKnown .toPrimitive)) (.object ⟨6⟩),
        .isCallable ⟨8⟩,
        .call ⟨8⟩ (.object ⟨6⟩)
          #[.primitive (.string (JSString.ofLeanString "default"))]]
      allocations := 6
    }) := by
  rw [executes_iff]
  rfl

/-- Generated custom `instanceof` dispatch consumes get/check/call and no fallback response. -/
theorem instanceof_generated_success :
    Executes (Instanceof.instanceofOperatorWith effects ordinaryHasInstanceEffect
      (.object ⟨9⟩) (.object ⟨10⟩)) {
      responses := [.get (.object ⟨11⟩), .isCallable true,
        .call (.primitive (.boolean true))]
    } (.ok true {
      responses := []
      trace := [
        .get ⟨10⟩ (.symbol (.wellKnown .hasInstance)) (.object ⟨10⟩),
        .isCallable ⟨11⟩,
        .call ⟨11⟩ (.object ⟨10⟩) #[.object ⟨9⟩]]
      allocations := 3
    }) := by
  rw [executes_iff]
  rfl

/-- Nonvacuity is witnessed by exact successful generated executions. -/
theorem generated_programs_nonvacuous :
    Executes (AbstractOperations.getMethodWith effects ⟨1⟩
        (.string (JSString.ofLeanString "method"))) {
      responses := [.get (.object ⟨2⟩), .isCallable true]
    } (.ok (some ⟨2⟩) {
      responses := []
      trace := [.get ⟨1⟩ (.string (JSString.ofLeanString "method")) (.object ⟨1⟩),
        .isCallable ⟨2⟩]
      allocations := 2
    }) ∧
    Executes (AbstractOperations.toPrimitiveWith effects (.object ⟨3⟩) .number) {
      responses := [.get (.object ⟨4⟩), .isCallable true,
        .call (.primitive (.number JSNumber.one))]
    } (.ok (.number JSNumber.one) {
      responses := []
      trace := [.get ⟨3⟩ (.symbol (.wellKnown .toPrimitive)) (.object ⟨3⟩),
        .isCallable ⟨4⟩, .call ⟨4⟩ (.object ⟨3⟩)
          #[.primitive (.string (JSString.ofLeanString "number"))]]
      allocations := 3
    }) ∧
    Executes (AbstractEquality.addWith effects (.object ⟨5⟩) (.object ⟨6⟩)) {
      responses := [.get (.object ⟨7⟩), .isCallable true,
        .call (.primitive (.string (JSString.ofLeanString "left"))),
        .get (.object ⟨8⟩), .isCallable true,
        .call (.primitive (.string (JSString.ofLeanString "right")))]
    } (.ok (.primitive (.string
        ((JSString.ofLeanString "left").append (JSString.ofLeanString "right")))) {
      responses := []
      trace := [.get ⟨5⟩ (.symbol (.wellKnown .toPrimitive)) (.object ⟨5⟩),
        .isCallable ⟨7⟩, .call ⟨7⟩ (.object ⟨5⟩)
          #[.primitive (.string (JSString.ofLeanString "default"))],
        .get ⟨6⟩ (.symbol (.wellKnown .toPrimitive)) (.object ⟨6⟩),
        .isCallable ⟨8⟩, .call ⟨8⟩ (.object ⟨6⟩)
          #[.primitive (.string (JSString.ofLeanString "default"))]]
      allocations := 6
    }) ∧
    Executes (Instanceof.instanceofOperatorWith effects ordinaryHasInstanceEffect
      (.object ⟨9⟩) (.object ⟨10⟩)) {
      responses := [.get (.object ⟨11⟩), .isCallable true,
        .call (.primitive (.boolean true))]
    } (.ok true {
      responses := []
      trace := [.get ⟨10⟩ (.symbol (.wellKnown .hasInstance)) (.object ⟨10⟩),
        .isCallable ⟨11⟩, .call ⟨11⟩ (.object ⟨10⟩) #[.object ⟨9⟩]]
      allocations := 3
    }) :=
  ⟨getMethod_executes_two_operations ⟨1⟩ ⟨2⟩
      (.string (JSString.ofLeanString "method")) [] [] 0 "TypeError: ",
    toPrimitive_generated_success, add_generated_success, instanceof_generated_success⟩

/-- Preservation obligations for interpreting free coercions into JSM. -/
structure JSMEffectsContract (target : CoercionEffects (JSM P))
    (ordinary : RefId → Value → JSM P Bool) : Prop where
  get : ∀ ref key receiver,
    JSM.PreservesResults (fun _ _ => True) (target.get ref key receiver)
  call : ∀ callee receiver arguments,
    JSM.PreservesResults (fun _ _ => True) (target.call callee receiver arguments)
  isCallable : ∀ ref, JSM.PreservesResults (fun _ _ => True) (target.isCallable ref)
  typeError : ∀ message, JSM.PreservesResults (fun _ _ => True) (target.typeError message)
  throw : ∀ primitive,
    JSM.PreservesResults (fun _ _ => True) (target.throw (.primitive primitive))
  ordinary : Instanceof.OrdinaryHasInstanceContract ordinary

/-- Free programs whose explicit throws are intrinsically valid primitive values. -/
@[simp] def Safe : CoercionProgram α → Prop
  | .pure _ => True
  | .get _ _ _ next => ∀ value, Safe (next value)
  | .call _ _ _ next => ∀ value, Safe (next value)
  | .isCallable _ next => ∀ value, Safe (next value)
  | .ordinaryHasInstance _ _ next => ∀ value, Safe (next value)
  | .typeError _ => True
  | .throw (.primitive _) => True
  | .throw (.object _) => False
@[simp] theorem safe_pure (value : α) : Safe (Pure.pure value : CoercionProgram α) := by
  change Safe (.pure value)
  trivial


/-- Predicate satisfied by every possible normal leaf of a free program. -/
def Results (predicate : α → Prop) : CoercionProgram α → Prop
  | .pure value => predicate value
  | .get _ _ _ next => ∀ value, Results predicate (next value)
  | .call _ _ _ next => ∀ value, Results predicate (next value)
  | .isCallable _ next => ∀ value, Results predicate (next value)
  | .ordinaryHasInstance _ _ next => ∀ value, Results predicate (next value)
  | .typeError _ | .throw _ => True

theorem Results.true (program : CoercionProgram α) : Results (fun _ => True) program := by
  induction program with
  | pure => trivial
  | get ref key receiver next induction | call ref receiver key next induction =>
      exact fun value => induction value
  | isCallable ref next induction | ordinaryHasInstance ref value next induction =>
      exact fun value => induction value
  | typeError | throw => trivial

theorem Results.bind (programResults : Results (fun _ => True) program)
    (nextResults : ∀ value, Results predicate (next value)) :
    Results predicate (program >>= next) := by
  induction program with
  | pure value => exact nextResults value
  | get ref key receiver continuation induction =>
      exact fun value => induction value (programResults value)
  | call callee receiver arguments continuation induction =>
      exact fun value => induction value (programResults value)
  | isCallable ref continuation induction =>
      exact fun value => induction value (programResults value)
  | ordinaryHasInstance constructor value continuation induction =>
      exact fun answer => induction answer (programResults answer)
  | typeError | throw => trivial

theorem Safe.bind (programSafe : Safe program) (nextSafe : ∀ value, Safe (next value)) :
    Safe (program >>= next) := by
  induction program with
  | pure value => exact nextSafe value
  | get ref key receiver continuation induction =>
      simp only [Bind.bind, CoercionProgram.bind, Safe] at programSafe ⊢
      intro value
      exact induction value (programSafe value)
  | call callee receiver arguments continuation induction =>
      simp only [Bind.bind, CoercionProgram.bind, Safe] at programSafe ⊢
      intro value
      exact induction value (programSafe value)
  | isCallable ref continuation induction =>
      simp only [Bind.bind, CoercionProgram.bind, Safe] at programSafe ⊢
      intro value
      exact induction value (programSafe value)
  | ordinaryHasInstance constructor value continuation induction =>
      simp only [Bind.bind, CoercionProgram.bind, Safe] at programSafe ⊢
      intro answer
      exact induction answer (programSafe answer)
  | typeError message => trivial
  | throw value =>
      cases value with
      | primitive primitive => trivial
      | object ref => contradiction

private theorem preservesResults_true (action : JSM P α)
    (preserves : JSM.PreservesResults valid action) :
    JSM.PreservesResults (fun _ _ => True) action := by
  refine ⟨preserves.1, ?_⟩
  intro machine machineValid
  have resultValid := preserves.2 machine machineValid
  cases run : action machine with
  | done completion final =>
      rw [run] at resultValid
      cases completion with
      | normal value => trivial
      | returned value | thrown value => exact resultValid
      | «break» label | «continue» label => trivial
  | exhausted final | fault fault final => trivial

/-- The production coercion effects and ordinary-instance boundary satisfy JSM preservation. -/
theorem forJSM_contract (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) :
    JSMEffectsContract (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook) := by
  constructor
  · intro ref key receiver
    exact preservesResults_true _
      (ObjectAccess.get_preservesResults hook ref key receiver hookPreserves)
  · intro callee receiver arguments
    exact preservesResults_true _
      (Call.call_preservesResults hook callee receiver arguments hookPreserves)
  · intro ref
    change JSM.PreservesResults (fun _ _ => True) (JSM.bind JSM.readHeap fun heap =>
      match heap.isCallable ref with
      | .error fault => JSM.fail (.runtime (.heap fault))
      | .ok callable => JSM.pure callable)
    apply JSM.bind_preservesResults _ _ JSM.readHeap_preservesResults
    intro heap machine valid heapEqual
    subst heap
    cases callableResult : machine.heap.isCallable ref with
    | error fault =>
        exact ⟨(JSM.fail_preservesResults (fun _ _ => True) _).1 machine valid,
          (JSM.fail_preservesResults (fun _ _ => True) _).2 machine valid⟩
    | ok isCallable =>
        exact ⟨(JSM.pure_preservesResults (fun _ _ => True) isCallable
            (by intros; trivial)).1 machine valid,
          (JSM.pure_preservesResults (fun _ _ => True) isCallable
            (by intros; trivial)).2 machine valid⟩
  · intro message
    exact ObjectAccess.throwTypeError_preservesResults message
  · intro primitive
    constructor
    · exact JSM.throwJS_preservesWellFormed _
    · intro machine valid
      simp [CoercionEffects.forJSM, JSM.throwJS, RunResult.CompletionValuesValid,
        Heap.valueValid]
  · exact Instanceof.ordinaryHasInstance_contract hook hookPreserves

/-- Interpreting a free program preserves machine continuity and escaping values. -/
theorem interpret_preservesResults (contract : JSMEffectsContract target ordinary)
    (program : CoercionProgram α) (safe : Safe program) :
    JSM.PreservesResults (fun _ _ => True) (interpret target ordinary program) := by
  induction program with
  | pure value =>
      exact JSM.pure_preservesResults (fun _ _ => True) value (by intros; trivial)
  | get ref key receiver next induction =>
      apply JSM.bind_preservesResults _ _ (contract.get ref key receiver)
      intro value machine valid _
      exact ⟨(induction value (safe value)).1 machine valid,
        (induction value (safe value)).2 machine valid⟩
  | call callee receiver arguments next induction =>
      apply JSM.bind_preservesResults _ _ (contract.call callee receiver arguments)
      intro value machine valid _
      exact ⟨(induction value (safe value)).1 machine valid,
        (induction value (safe value)).2 machine valid⟩
  | isCallable ref next induction =>
      apply JSM.bind_preservesResults _ _ (contract.isCallable ref)
      intro value machine valid _
      exact ⟨(induction value (safe value)).1 machine valid,
        (induction value (safe value)).2 machine valid⟩
  | ordinaryHasInstance constructor value next induction =>
      apply JSM.bind_preservesResults _ _ (contract.ordinary constructor value)
      intro answer machine valid _
      exact ⟨(induction answer (safe answer)).1 machine valid,
        (induction answer (safe answer)).2 machine valid⟩
  | typeError message =>
      apply JSM.bind_preservesResults _ _ (contract.typeError message)
      intro impossible
      exact impossible.elim
  | throw value =>
      cases value with
      | primitive primitive =>
          apply JSM.bind_preservesResults _ _ (contract.throw primitive)
          intro impossible
          exact impossible.elim
      | object ref => contradiction

/-- Interpretation preserves any state-independent predicate proved for all normal leaves. -/
theorem interpret_preservesResultsWhere (contract : JSMEffectsContract target ordinary)
    (program : CoercionProgram α) (safe : Safe program) (results : Results predicate program) :
    JSM.PreservesResults (fun value _ => predicate value) (interpret target ordinary program) := by
  induction program with
  | pure value =>
      exact JSM.pure_preservesResults (fun value _ => predicate value) value
        (by intros; exact results)
  | get ref key receiver next induction =>
      apply JSM.bind_preservesResults _ _ (contract.get ref key receiver)
      intro value machine valid _
      exact ⟨(induction value (safe value) (results value)).1 machine valid,
        (induction value (safe value) (results value)).2 machine valid⟩
  | call callee receiver arguments next induction =>
      apply JSM.bind_preservesResults _ _ (contract.call callee receiver arguments)
      intro value machine valid _
      exact ⟨(induction value (safe value) (results value)).1 machine valid,
        (induction value (safe value) (results value)).2 machine valid⟩
  | isCallable ref next induction =>
      apply JSM.bind_preservesResults _ _ (contract.isCallable ref)
      intro value machine valid _
      exact ⟨(induction value (safe value) (results value)).1 machine valid,
        (induction value (safe value) (results value)).2 machine valid⟩
  | ordinaryHasInstance constructor value next induction =>
      apply JSM.bind_preservesResults _ _ (contract.ordinary constructor value)
      intro answer machine valid _
      exact ⟨(induction answer (safe answer) (results answer)).1 machine valid,
        (induction answer (safe answer) (results answer)).2 machine valid⟩
  | typeError message =>
      apply JSM.bind_preservesResults _ _ (contract.typeError message)
      intro impossible
      exact impossible.elim
  | throw value =>
      cases value with
      | primitive primitive =>
          apply JSM.bind_preservesResults _ _ (contract.throw primitive)
          intro impossible
          exact impossible.elim
      | object ref => contradiction

private theorem safe_fromCoercion (result : Except CoercionFault α) :
    Safe (CoercionEffects.fromCoercion effects result) := by
  cases result <;> simp [CoercionEffects.fromCoercion, CoercionEffects.terminal,
    effects, perform, Safe, CoercionFault.toThrownValue, Bind.bind, CoercionProgram.bind]

theorem safe_getMethod (ref : RefId) (key : PropertyKey) :
    Safe (AbstractOperations.getMethodWith effects ref key) := by
  unfold AbstractOperations.getMethodWith
  apply Safe.bind (by simp [effects, perform, Safe])
  intro value
  cases value with
  | primitive primitive => cases primitive <;>
      simp [CoercionEffects.raiseTypeError, CoercionEffects.terminal, effects, perform, Safe,
        Bind.bind, CoercionProgram.bind]
  | object method =>
      simp [effects, perform, Safe, CoercionEffects.raiseTypeError,
        CoercionEffects.terminal, Bind.bind, CoercionProgram.bind]

theorem safe_tryOrdinaryMethod (receiver : RefId) (name : String) :
    Safe (AbstractOperations.tryOrdinaryMethodWith effects receiver name) := by
  unfold AbstractOperations.tryOrdinaryMethodWith
  apply Safe.bind (by simp [effects, perform, Safe])
  intro value
  cases value with
  | primitive primitive => trivial
  | object method =>
      apply Safe.bind (by simp [effects, perform, Safe])
      intro callable
      cases callable with
      | false => trivial
      | true =>
          apply Safe.bind (by simp [effects, perform, Safe])
          intro result
          cases result <;> trivial

theorem safe_tryOrdinaryMethods (receiver : RefId) (names : List String) :
    Safe (AbstractOperations.tryOrdinaryMethodsWith effects receiver names) := by
  induction names with
  | nil => simp [AbstractOperations.tryOrdinaryMethodsWith, CoercionEffects.raiseTypeError,
      CoercionEffects.terminal, effects, perform, Safe, Bind.bind, CoercionProgram.bind]
  | cons name rest induction =>
      unfold AbstractOperations.tryOrdinaryMethodsWith
      apply Safe.bind (safe_tryOrdinaryMethod receiver name)
      intro result
      cases result <;> simp [induction]

theorem safe_ordinaryToPrimitive (receiver : RefId) (hint : PreferredType) :
    Safe (AbstractOperations.ordinaryToPrimitiveWith effects receiver hint) := by
  cases hint <;> simp [AbstractOperations.ordinaryToPrimitiveWith, safe_tryOrdinaryMethods]

theorem safe_toPrimitive (value : Value) (hint : PreferredType) :
    Safe (AbstractOperations.toPrimitiveWith effects value hint) := by
  cases value with
  | primitive primitive => trivial
  | object receiver =>
      unfold AbstractOperations.toPrimitiveWith
      apply Safe.bind (safe_getMethod receiver (.symbol (.wellKnown .toPrimitive)))
      intro method
      cases method with
      | none => exact safe_ordinaryToPrimitive receiver hint
      | some method =>
          apply Safe.bind (by simp [effects, perform, Safe])
          intro result
          cases result <;> simp [effects, perform, Safe, CoercionEffects.raiseTypeError,
            CoercionEffects.terminal, Bind.bind, CoercionProgram.bind]

theorem safe_toNumber (value : Value) :
    Safe (AbstractOperations.toNumberWith effects value) := by
  unfold AbstractOperations.toNumberWith
  apply Safe.bind (safe_toPrimitive value .number)
  exact fun primitive => safe_fromCoercion primitive.toNumber

theorem safe_toString (value : Value) :
    Safe (AbstractOperations.toStringWith effects value) := by
  unfold AbstractOperations.toStringWith
  apply Safe.bind (safe_toPrimitive value .string)
  exact fun primitive => safe_fromCoercion primitive.toString

theorem safe_toNumeric (value : Value) :
    Safe (AbstractOperations.toNumericWith effects value) := by
  unfold AbstractOperations.toNumericWith
  apply Safe.bind (safe_toPrimitive value .number)
  exact fun primitive => safe_fromCoercion primitive.toNumeric

theorem safe_toPropertyKey (value : Value) :
    Safe (AbstractOperations.toPropertyKeyWith effects value) := by
  unfold AbstractOperations.toPropertyKeyWith
  apply Safe.bind (safe_toPrimitive value .string)
  exact fun primitive => safe_fromCoercion primitive.toPropertyKey

private theorem safe_primitiveAgainstObject (primitive : Primitive) (object : RefId) :
    Safe (AbstractEquality.primitiveAgainstObjectWith effects primitive object) := by
  unfold AbstractEquality.primitiveAgainstObjectWith
  split
  · trivial
  · apply Safe.bind (safe_toPrimitive (.object object) .default)
    intro converted
    trivial

theorem safe_looseEqual (left right : Value) :
    Safe (AbstractEquality.looseEqualWith effects left right) := by
  cases left <;> cases right <;>
    simp [AbstractEquality.looseEqualWith, safe_primitiveAgainstObject]

private theorem safe_stringAddition (left right : Primitive) :
    Safe (do
      let leftString ← CoercionEffects.fromCoercion effects left.toString
      let rightString ← CoercionEffects.fromCoercion effects right.toString
      pure (Value.primitive (.string (leftString.append rightString)))) := by
  apply Safe.bind (safe_fromCoercion left.toString)
  intro leftString
  apply Safe.bind (safe_fromCoercion right.toString)
  intro rightString
  trivial

private theorem safe_numericAddition (left right : Primitive) :
    Safe (do
      let leftNumeric ← CoercionEffects.fromCoercion effects left.toNumeric
      let rightNumeric ← CoercionEffects.fromCoercion effects right.toNumeric
      pure (← CoercionEffects.fromCoercion effects (Numeric.add leftNumeric rightNumeric)).toValue) := by
  apply Safe.bind (safe_fromCoercion left.toNumeric)
  intro leftNumeric
  apply Safe.bind (safe_fromCoercion right.toNumeric)
  intro rightNumeric
  apply Safe.bind (safe_fromCoercion (Numeric.add leftNumeric rightNumeric))
  intro result
  trivial

theorem safe_addPrimitives (left right : Primitive) :
    Safe (AbstractEquality.addPrimitivesWith effects left right) := by
  cases left <;> cases right <;>
    first | exact safe_stringAddition _ _ | exact safe_numericAddition _ _

theorem safe_add (left right : Value) :
    Safe (AbstractEquality.addWith effects left right) := by
  unfold AbstractEquality.addWith
  apply Safe.bind (safe_toPrimitive left .default)
  intro leftPrimitive
  apply Safe.bind (safe_toPrimitive right .default)
  exact fun rightPrimitive => safe_addPrimitives leftPrimitive rightPrimitive

/-- A value-level result is represented by a primitive rather than a heap reference. -/
def IsPrimitiveValue : Value → Prop
  | .primitive _ => True
  | .object _ => False

private theorem stringAddition_resultsPrimitive (left right : Primitive) :
    Results IsPrimitiveValue (do
      let leftString ← CoercionEffects.fromCoercion effects left.toString
      let rightString ← CoercionEffects.fromCoercion effects right.toString
      pure (Value.primitive (.string (leftString.append rightString)))) := by
  apply Results.bind (Results.true _)
  intro leftString
  apply Results.bind (Results.true _)
  intro rightString
  trivial

private theorem numericAddition_resultsPrimitive (left right : Primitive) :
    Results IsPrimitiveValue (do
      let leftNumeric ← CoercionEffects.fromCoercion effects left.toNumeric
      let rightNumeric ← CoercionEffects.fromCoercion effects right.toNumeric
      pure (← CoercionEffects.fromCoercion effects (Numeric.add leftNumeric rightNumeric)).toValue) := by
  apply Results.bind (Results.true _)
  intro leftNumeric
  apply Results.bind (Results.true _)
  intro rightNumeric
  apply Results.bind (Results.true _)
  intro result
  cases result <;> trivial

theorem addPrimitives_resultsPrimitive (left right : Primitive) :
    Results IsPrimitiveValue (AbstractEquality.addPrimitivesWith effects left right) := by
  cases left <;> cases right <;>
    first | exact stringAddition_resultsPrimitive _ _ | exact numericAddition_resultsPrimitive _ _

theorem add_resultsPrimitive (left right : Value) :
    Results IsPrimitiveValue (AbstractEquality.addWith effects left right) := by
  unfold AbstractEquality.addWith
  apply Results.bind (Results.true _)
  intro leftPrimitive
  apply Results.bind (Results.true _)
  exact fun rightPrimitive => addPrimitives_resultsPrimitive leftPrimitive rightPrimitive

theorem safe_orderedPrimitives (left right : Value) (leftFirst : Bool) :
    Safe (AbstractEquality.orderedPrimitivesWith effects left right leftFirst) := by
  cases leftFirst <;> unfold AbstractEquality.orderedPrimitivesWith
  · apply Safe.bind (safe_toPrimitive right .number)
    intro rightPrimitive
    apply Safe.bind (safe_toPrimitive left .number)
    intro leftPrimitive
    trivial
  · apply Safe.bind (safe_toPrimitive left .number)
    intro leftPrimitive
    apply Safe.bind (safe_toPrimitive right .number)
    intro rightPrimitive
    trivial

theorem safe_relationalComparison (left right : Value) (leftFirst : Bool) :
    Safe (AbstractEquality.relationalComparisonWith effects left right leftFirst) := by
  unfold AbstractEquality.relationalComparisonWith
  apply Safe.bind (safe_orderedPrimitives left right leftFirst)
  intro primitives
  exact safe_fromCoercion
    (Primitive.abstractRelationalComparison primitives.1 primitives.2 leftFirst)

theorem safe_lessThan (left right : Value) :
    Safe (AbstractEquality.lessThanWith effects left right) := by
  unfold AbstractEquality.lessThanWith
  apply Safe.bind (safe_relationalComparison left right true)
  intro result
  trivial

theorem safe_greaterThan (left right : Value) :
    Safe (AbstractEquality.greaterThanWith effects left right) := by
  unfold AbstractEquality.greaterThanWith
  apply Safe.bind (safe_relationalComparison right left false)
  intro result
  trivial

theorem safe_lessThanOrEqual (left right : Value) :
    Safe (AbstractEquality.lessThanOrEqualWith effects left right) := by
  unfold AbstractEquality.lessThanOrEqualWith
  apply Safe.bind (safe_relationalComparison right left false)
  intro result
  cases result with
  | none => trivial
  | some value => cases value <;> trivial

theorem safe_greaterThanOrEqual (left right : Value) :
    Safe (AbstractEquality.greaterThanOrEqualWith effects left right) := by
  unfold AbstractEquality.greaterThanOrEqualWith
  apply Safe.bind (safe_relationalComparison left right true)
  intro result
  cases result with
  | none => trivial
  | some value => cases value <;> trivial

theorem safe_instanceof (value constructor : Value) :
    Safe (Instanceof.instanceofOperatorWith effects ordinaryHasInstanceEffect value constructor) := by
  cases constructor with
  | primitive primitive =>
      simp [Instanceof.instanceofOperatorWith, CoercionEffects.raiseTypeError,
        CoercionEffects.terminal, effects, perform, Safe, Bind.bind, CoercionProgram.bind]
  | object constructor =>
      unfold Instanceof.instanceofOperatorWith
      apply Safe.bind (safe_getMethod constructor (.symbol (.wellKnown .hasInstance)))
      intro method
      cases method with
      | some method =>
          apply Safe.bind (by simp [effects, perform, Safe])
          intro result
          trivial
      | none =>
          apply Safe.bind (by simp [effects, perform, Safe])
          intro callable
          cases callable with
          | true => simp [ordinaryHasInstanceEffect, perform, Safe]
          | false => simp [CoercionEffects.raiseTypeError, CoercionEffects.terminal,
              effects, perform, Safe, Bind.bind, CoercionProgram.bind]

/-- An ordinary method call exists only in the callable-object continuation. -/
theorem ordinary_method_call_after_callable (receiver : RefId) (name : String) :
    AbstractOperations.tryOrdinaryMethodWith effects receiver name =
      .get receiver (.string (JSString.ofLeanString name)) (.object receiver) (fun methodValue =>
        match methodValue with
        | .primitive _ => pure none
        | .object method =>
            .isCallable method fun callable =>
              if !callable then pure none
              else .call method (.object receiver) #[] fun result =>
                match result with
                | .primitive primitive => pure (some primitive)
                | .object _ => pure none) := rfl

/-- ToPrimitive on an object starts with the exact `@@toPrimitive` GetMethod read. -/
theorem toPrimitive_object_startsWithGet (receiver : RefId) (hint : PreferredType) :
    AbstractOperations.toPrimitiveWith effects (.object receiver) hint =
      (AbstractOperations.getMethodWith effects receiver (.symbol (.wellKnown .toPrimitive)) >>=
        fun method => match method with
        | some method => do
            match ← effects.call method (.object receiver)
                #[.primitive (.string (AbstractOperations.hintString hint))] with
            | .primitive primitive => pure primitive
            | .object _ => (CoercionEffects.raiseTypeError effects
                "Symbol.toPrimitive returned an object" : CoercionProgram Primitive)
        | none => AbstractOperations.ordinaryToPrimitiveWith effects receiver hint) := rfl

/-- Number/default ordinary conversion fixes `valueOf` before `toString`. -/
theorem ordinary_number_program_order (receiver : RefId) :
    AbstractOperations.ordinaryToPrimitiveWith effects receiver .number =
      AbstractOperations.tryOrdinaryMethodsWith effects receiver ["valueOf", "toString"] := rfl

/-- String ordinary conversion fixes `toString` before `valueOf`. -/
theorem ordinary_string_program_order (receiver : RefId) :
    AbstractOperations.ordinaryToPrimitiveWith effects receiver .string =
      AbstractOperations.tryOrdinaryMethodsWith effects receiver ["toString", "valueOf"] := rfl

/-- Ordinary method lists advance only after the current method returns no primitive. -/
theorem ordinary_methods_protocol (receiver : RefId) (name : String) (rest : List String) :
    AbstractOperations.tryOrdinaryMethodsWith effects receiver (name :: rest) = (do
      match ← AbstractOperations.tryOrdinaryMethodWith effects receiver name with
      | some primitive => pure primitive
      | none => AbstractOperations.tryOrdinaryMethodsWith effects receiver rest) := rfl

/-- A terminal type error suppresses every later free operation. -/
theorem abrupt_typeError_has_no_later (message : String) (next : α → CoercionProgram β) :
    (CoercionEffects.raiseTypeError effects message : CoercionProgram α) >>= next =
      CoercionEffects.raiseTypeError effects message := rfl

/-- A terminal throw suppresses every later free operation. -/
theorem abrupt_throw_has_no_later (value : Value) (next : α → CoercionProgram β) :
    (CoercionEffects.terminal (effects.throw value) : CoercionProgram α) >>= next =
      CoercionEffects.terminal (effects.throw value) := rfl

/-- Addition binds the entire left coercion before constructing the right coercion. -/
theorem add_program_left_before_right (left right : Value) :
    AbstractEquality.addWith effects left right = (do
      let leftPrimitive ← AbstractOperations.toPrimitiveWith effects left
      let rightPrimitive ← AbstractOperations.toPrimitiveWith effects right
      AbstractEquality.addPrimitivesWith effects leftPrimitive rightPrimitive) := rfl

/-- Relational conversion syntax follows `leftFirst = false`. -/
theorem relational_program_right_first (left right : Value) :
    AbstractEquality.orderedPrimitivesWith effects left right false = (do
      let rightPrimitive ← AbstractOperations.toPrimitiveWith effects right .number
      let leftPrimitive ← AbstractOperations.toPrimitiveWith effects left .number
      pure (leftPrimitive, rightPrimitive)) := rfl

/-- Relational conversion syntax follows `leftFirst = true`. -/
theorem relational_program_left_first (left right : Value) :
    AbstractEquality.orderedPrimitivesWith effects left right true = (do
      let leftPrimitive ← AbstractOperations.toPrimitiveWith effects left .number
      let rightPrimitive ← AbstractOperations.toPrimitiveWith effects right .number
      pure (leftPrimitive, rightPrimitive)) := rfl

/-- `instanceof` reads custom `@@hasInstance` before its explicit ordinary fallback. -/
theorem instanceof_program_custom_before_ordinary (value : Value) (constructor : RefId) :
    Instanceof.instanceofOperatorWith effects ordinaryHasInstanceEffect value (.object constructor) = (do
      match ← AbstractOperations.getMethodWith effects constructor
          (.symbol (.wellKnown .hasInstance)) with
      | some method =>
          let result ← effects.call method (.object constructor) #[value]
          pure result.toBoolean
      | none =>
          if ← effects.isCallable constructor then ordinaryHasInstanceEffect constructor value
          else CoercionEffects.raiseTypeError effects "right-hand side is not callable") := rfl

/-- Production GetMethod is the JSM interpretation of the generated free program. -/
theorem getMethod_production (hook : BodyHook P) (ref : RefId) (key : PropertyKey) :
    AbstractOperations.getMethod hook ref key =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractOperations.getMethodWith effects ref key) := by
  unfold AbstractOperations.getMethod
  symm
  exact interpret_getMethodWith _ _ _ _

/-- Production OrdinaryToPrimitive is the JSM interpretation of its free program. -/
theorem ordinaryToPrimitive_production (hook : BodyHook P) (receiver : RefId)
    (hint : PreferredType) :
    AbstractOperations.ordinaryToPrimitive hook receiver hint =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractOperations.ordinaryToPrimitiveWith effects receiver hint) := by
  unfold AbstractOperations.ordinaryToPrimitive
  symm
  exact interpret_ordinaryToPrimitiveWith _ _ _ _

/-- Production ToPrimitive is the JSM interpretation of its free program. -/
theorem toPrimitive_production (hook : BodyHook P) (value : Value) (hint : PreferredType) :
    AbstractOperations.toPrimitive hook value hint =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractOperations.toPrimitiveWith effects value hint) := by
  unfold AbstractOperations.toPrimitive
  symm
  exact interpret_toPrimitiveWith _ _ _ _

/-- Production ToNumber is the JSM interpretation of its free program. -/
theorem toNumber_production (hook : BodyHook P) (value : Value) :
    AbstractOperations.toNumber hook value =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractOperations.toNumberWith effects value) := by
  unfold AbstractOperations.toNumber
  symm
  exact interpret_toNumberWith _ _ _

/-- Production ToString is the JSM interpretation of its free program. -/
theorem toString_production (hook : BodyHook P) (value : Value) :
    AbstractOperations.toString hook value =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractOperations.toStringWith effects value) := by
  unfold AbstractOperations.toString
  symm
  exact interpret_toStringWith _ _ _

/-- Production ToNumeric is the JSM interpretation of its free program. -/
theorem toNumeric_production (hook : BodyHook P) (value : Value) :
    AbstractOperations.toNumeric hook value =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractOperations.toNumericWith effects value) := by
  unfold AbstractOperations.toNumeric
  symm
  exact interpret_toNumericWith _ _ _

/-- Production ToPropertyKey is the JSM interpretation of its free program. -/
theorem toPropertyKey_production (hook : BodyHook P) (value : Value) :
    AbstractOperations.toPropertyKey hook value =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractOperations.toPropertyKeyWith effects value) := by
  unfold AbstractOperations.toPropertyKey
  symm
  exact interpret_toPropertyKeyWith _ _ _

/-- Production abstract equality is the JSM interpretation of its free program. -/
theorem looseEqual_production (hook : BodyHook P) (left right : Value) :
    AbstractEquality.looseEqual hook left right =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractEquality.looseEqualWith effects left right) := by
  unfold AbstractEquality.looseEqual
  symm
  exact interpret_looseEqualWith _ _ _ _

/-- Production addition is the JSM interpretation of its free program. -/
theorem add_production (hook : BodyHook P) (left right : Value) :
    AbstractEquality.add hook left right =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractEquality.addWith effects left right) := by
  unfold AbstractEquality.add
  symm
  exact interpret_addWith _ _ _ _

/-- Production relational comparison is the JSM interpretation of its free program. -/
theorem relationalComparison_production (hook : BodyHook P) (left right : Value)
    (leftFirst : Bool) :
    AbstractEquality.relationalComparison hook left right leftFirst =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractEquality.relationalComparisonWith effects left right leftFirst) := by
  unfold AbstractEquality.relationalComparison
  symm
  exact interpret_relationalComparisonWith _ _ _ _ _

/-- Production `<` interprets the generated free program without changing operand order. -/
theorem lessThan_production (hook : BodyHook P) (left right : Value) :
    AbstractEquality.lessThan hook left right =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractEquality.lessThanWith effects left right) := by
  unfold AbstractEquality.lessThan
  symm
  exact interpret_lessThanWith _ _ _ _

/-- Production `>` interprets the generated swapped, right-first free program. -/
theorem greaterThan_production (hook : BodyHook P) (left right : Value) :
    AbstractEquality.greaterThan hook left right =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractEquality.greaterThanWith effects left right) := by
  unfold AbstractEquality.greaterThan
  symm
  exact interpret_greaterThanWith _ _ _ _

/-- Production `<=` interprets the generated swapped, right-first free program. -/
theorem lessThanOrEqual_production (hook : BodyHook P) (left right : Value) :
    AbstractEquality.lessThanOrEqual hook left right =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractEquality.lessThanOrEqualWith effects left right) := by
  unfold AbstractEquality.lessThanOrEqual
  symm
  exact interpret_lessThanOrEqualWith _ _ _ _

/-- Production `>=` interprets the generated left-first free program. -/
theorem greaterThanOrEqual_production (hook : BodyHook P) (left right : Value) :
    AbstractEquality.greaterThanOrEqual hook left right =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (AbstractEquality.greaterThanOrEqualWith effects left right) := by
  unfold AbstractEquality.greaterThanOrEqual
  symm
  exact interpret_greaterThanOrEqualWith _ _ _ _

/-- Production `instanceof` interprets the explicit ordinary fallback operation. -/
theorem instanceof_production (hook : BodyHook P) (value constructor : Value) :
    Instanceof.instanceofOperator hook value constructor =
      interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook)
        (Instanceof.instanceofOperatorWith effects ordinaryHasInstanceEffect value constructor) := by
  unfold Instanceof.instanceofOperator
  symm
  exact interpret_instanceofOperatorWith _ _ _ _

private theorem production_preserves (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (program : CoercionProgram α)
    (safe : Safe program) :
    JSM.PreservesResults (fun _ _ => True)
      (interpret (CoercionEffects.forJSM hook) (Instanceof.ordinaryHasInstance hook) program) :=
  interpret_preservesResults (forJSM_contract hook hookPreserves) program safe

private theorem preservesResults_mono (action : JSM P α)
    (preserves : JSM.PreservesResults first action)
    (implies : ∀ value machine, first value machine → second value machine) :
    JSM.PreservesResults second action := by
  refine ⟨preserves.1, ?_⟩
  intro machine valid
  have resultValid := preserves.2 machine valid
  cases run : action machine with
  | done completion final =>
      rw [run] at resultValid
      cases completion with
      | normal value => exact implies value final resultValid
      | returned value | thrown value => exact resultValid
      | «break» label | «continue» label => trivial
  | exhausted final | fault fault final => trivial

/-- A present GetMethod result is a valid callable reference in the final heap. -/
def GetMethodResultValid (result : Option RefId) (machine : Machine P) : Prop :=
  ∀ method, result = some method →
    machine.heap.valueValid (.object method) = true ∧
      machine.heap.isCallable method = .ok true

private theorem forJSM_isCallable_preservesResults (hook : BodyHook P) (ref : RefId) :
    JSM.PreservesResults
      (fun callable machine => machine.heap.isCallable ref = .ok callable)
      ((CoercionEffects.forJSM hook).isCallable ref) := by
  change JSM.PreservesResults _ (JSM.bind JSM.readHeap fun heap =>
    match heap.isCallable ref with
    | .error fault => JSM.fail (.runtime (.heap fault))
    | .ok callable => JSM.pure callable)
  apply JSM.bind_preservesResults _ _ JSM.readHeap_preservesResults
  intro heap machine valid heapEqual
  subst heap
  cases callableResult : machine.heap.isCallable ref with
  | error fault =>
      exact ⟨JSM.fail_preservesWellFormed _ machine valid, trivial⟩
  | ok callable =>
      exact ⟨JSM.pure_preservesWellFormed callable machine valid, callableResult⟩

/-- Production GetMethod returns only absence or a valid callable reference. -/
theorem getMethod_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (ref : RefId) (key : PropertyKey) :
    JSM.PreservesResults GetMethodResultValid (AbstractOperations.getMethod hook ref key) := by
  unfold AbstractOperations.getMethod AbstractOperations.getMethodWith
  apply JSM.bind_preservesResults _ _
    (ObjectAccess.get_preservesResults hook ref key (.object ref) hookPreserves)
  intro observed machine valid observedValid
  cases observed with
  | primitive primitive =>
      cases primitive with
      | undefined | null =>
          exact ⟨JSM.pure_preservesWellFormed none machine valid,
            by intro method impossible; contradiction⟩
      | boolean value | number value | string value | bigint value | symbol value =>
          have thrown := ObjectAccess.throwTypeError_preservesResultsFor
            (GetMethodResultValid (P := P)) "property is not callable"
          exact ⟨thrown.1 machine valid, thrown.2 machine valid⟩
  | object method =>
      let continuation : Bool → JSM P (Option RefId) := fun callable =>
        if callable then JSM.pure (some method)
        else ObjectAccess.throwTypeError "property is not callable"
      have continuationPreserves : JSM.PreservesResults (GetMethodResultValid (P := P))
          (JSM.bind ((CoercionEffects.forJSM hook).isCallable method) continuation) := by
        apply JSM.bind_preservesResults _ _ (forJSM_isCallable_preservesResults hook method)
        intro callable final finalValid callableResult
        cases callable with
        | false =>
            have thrown := ObjectAccess.throwTypeError_preservesResultsFor
              (GetMethodResultValid (P := P)) "property is not callable"
            exact ⟨thrown.1 final finalValid, thrown.2 final finalValid⟩
        | true =>
            exact ⟨JSM.pure_preservesWellFormed (some method) final finalValid,
              by
                intro result equal
                cases equal
                exact ⟨Heap.isCallable_true_valueValid final.heap method callableResult,
                  callableResult⟩⟩
      change
        (JSM.bind ((CoercionEffects.forJSM hook).isCallable method) continuation machine).MachinePreserved machine ∧
        (JSM.bind ((CoercionEffects.forJSM hook).isCallable method) continuation machine).CompletionValuesValid
          (GetMethodResultValid (P := P))
      exact ⟨continuationPreserves.1 machine valid, continuationPreserves.2 machine valid⟩

/-- OrdinaryToPrimitive returns a reference-free primitive and validates every abrupt value. -/
theorem ordinaryToPrimitive_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (receiver : RefId) (hint : PreferredType) :
    JSM.PreservesResults (fun (_ : Primitive) _ => True)
      (AbstractOperations.ordinaryToPrimitive hook receiver hint) := by
  rw [ordinaryToPrimitive_production]
  exact production_preserves hook hookPreserves _ (safe_ordinaryToPrimitive receiver hint)

/-- ToPrimitive returns a reference-free primitive and validates every abrupt value. -/
theorem toPrimitive_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (value : Value) (hint : PreferredType) :
    JSM.PreservesResults (fun (_ : Primitive) _ => True)
      (AbstractOperations.toPrimitive hook value hint) := by
  rw [toPrimitive_production]
  exact production_preserves hook hookPreserves _ (safe_toPrimitive value hint)

/-- ToNumber's numeric result cannot contain a heap reference; abrupt values remain validated. -/
theorem toNumber_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (value : Value) :
    JSM.PreservesResults (fun (_ : JSNumber) _ => True) (AbstractOperations.toNumber hook value) := by
  rw [toNumber_production]
  exact production_preserves hook hookPreserves _ (safe_toNumber value)

/-- ToString's string result cannot contain a heap reference; abrupt values remain validated. -/
theorem toString_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (value : Value) :
    JSM.PreservesResults (fun (_ : JSString) _ => True) (AbstractOperations.toString hook value) := by
  rw [toString_production]
  exact production_preserves hook hookPreserves _ (safe_toString value)

/-- ToNumeric's result cannot contain a heap reference; abrupt values remain validated. -/
theorem toNumeric_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (value : Value) :
    JSM.PreservesResults (fun (_ : Numeric) _ => True) (AbstractOperations.toNumeric hook value) := by
  rw [toNumeric_production]
  exact production_preserves hook hookPreserves _ (safe_toNumeric value)

/-- Property keys contain no heap references; abrupt values remain validated. -/
theorem toPropertyKey_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (value : Value) :
    JSM.PreservesResults (fun (_ : PropertyKey) _ => True)
      (AbstractOperations.toPropertyKey hook value) := by
  rw [toPropertyKey_production]
  exact production_preserves hook hookPreserves _ (safe_toPropertyKey value)

/-- Abstract equality returns exactly a Bool and validates every abrupt value. -/
theorem looseEqual_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (left right : Value) :
    JSM.PreservesResults (fun (_ : Bool) _ => True)
      (AbstractEquality.looseEqual hook left right) := by
  rw [looseEqual_production]
  exact production_preserves hook hookPreserves _ (safe_looseEqual left right)

/-- A normal addition result is a valid primitive value in the final heap. -/
def AddResultValid (value : Value) (machine : Machine P) : Prop :=
  machine.heap.valueValid value = true ∧ IsPrimitiveValue value

/-- Production addition returns a valid primitive and validates every abrupt value. -/
theorem add_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (left right : Value) :
    JSM.PreservesResults AddResultValid (AbstractEquality.add hook left right) := by
  rw [add_production]
  have primitiveResults := interpret_preservesResultsWhere
    (forJSM_contract hook hookPreserves) (AbstractEquality.addWith effects left right)
    (safe_add left right) (add_resultsPrimitive left right)
  apply preservesResults_mono _ primitiveResults
  intro value machine primitive
  cases value with
  | primitive value => exact ⟨rfl, primitive⟩
  | object ref => contradiction

/-- Relational comparison returns exactly `Option Bool` and validates every abrupt value. -/
theorem relationalComparison_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (left right : Value) (leftFirst : Bool) :
    JSM.PreservesResults (fun (_ : Option Bool) _ => True)
      (AbstractEquality.relationalComparison hook left right leftFirst) := by
  rw [relationalComparison_production]
  exact production_preserves hook hookPreserves _
    (safe_relationalComparison left right leftFirst)

/-- Production `<` returns exactly a Bool and validates every abrupt value. -/
theorem lessThan_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (left right : Value) :
    JSM.PreservesResults (fun (_ : Bool) _ => True) (AbstractEquality.lessThan hook left right) := by
  rw [lessThan_production]
  exact production_preserves hook hookPreserves _ (safe_lessThan left right)

/-- Production `>` returns exactly a Bool and validates every abrupt value. -/
theorem greaterThan_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (left right : Value) :
    JSM.PreservesResults (fun (_ : Bool) _ => True) (AbstractEquality.greaterThan hook left right) := by
  rw [greaterThan_production]
  exact production_preserves hook hookPreserves _ (safe_greaterThan left right)

/-- Production `<=` returns exactly a Bool and validates every abrupt value. -/
theorem lessThanOrEqual_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (left right : Value) :
    JSM.PreservesResults (fun (_ : Bool) _ => True)
      (AbstractEquality.lessThanOrEqual hook left right) := by
  rw [lessThanOrEqual_production]
  exact production_preserves hook hookPreserves _ (safe_lessThanOrEqual left right)

/-- Production `>=` returns exactly a Bool and validates every abrupt value. -/
theorem greaterThanOrEqual_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (left right : Value) :
    JSM.PreservesResults (fun (_ : Bool) _ => True)
      (AbstractEquality.greaterThanOrEqual hook left right) := by
  rw [greaterThanOrEqual_production]
  exact production_preserves hook hookPreserves _ (safe_greaterThanOrEqual left right)

/-- Production `instanceof` returns exactly a Bool and validates every abrupt value. -/
theorem instanceof_preservesResults (hook : BodyHook P)
    (hookPreserves : BodyHookPreservesWellFormed hook) (value constructor : Value) :
    JSM.PreservesResults (fun (_ : Bool) _ => True)
      (Instanceof.instanceofOperator hook value constructor) := by
  rw [instanceof_production]
  exact production_preserves hook hookPreserves _ (safe_instanceof value constructor)

private def proofPlatform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def proofHook : BodyHook proofPlatform := fun _ _ _ => JSM.pure ()

private theorem proofHook_preserves : BodyHookPreservesWellFormed proofHook := by
  intro ref receiver arguments
  constructor
  · intro machine valid inputs
    exact JSM.pure_preservesWellFormed () machine valid
  · intro machine valid inputs
    change True
    trivial

/-- The production preservation theorem is inhabited by an actual evaluator hook. -/
theorem production_hook_nonvacuous :
    BodyHookPreservesWellFormed proofHook ∧
      JSM.PreservesResults (fun _ _ => True)
        (AbstractOperations.toPrimitive proofHook (.primitive .undefined) .default) :=
  ⟨proofHook_preserves,
    toPrimitive_preservesResults proofHook proofHook_preserves (.primitive .undefined) .default⟩

end CoercionProgram
end TSLean.JS
