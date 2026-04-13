-- TSLean: TypeScript → Lean 4 Runtime Library

-- Runtime
import TSLean.Runtime.Basic
import TSLean.Runtime.Monad
import TSLean.Runtime.Coercions
import TSLean.Runtime.BrandedTypes
import TSLean.Runtime.Validation
import TSLean.Runtime.WebAPI
import TSLean.Runtime.Inhabited
import TSLean.Runtime.JSTypes

-- Stdlib
import TSLean.Stdlib.Array
import TSLean.Stdlib.HashMap
import TSLean.Stdlib.HashSet
import TSLean.Stdlib.String
import TSLean.Stdlib.Numeric
import TSLean.Stdlib.OptionResult
import TSLean.Stdlib.Async
import TSLean.Stdlib.JSON

-- Effects
import TSLean.Effects.Core
import TSLean.Effects.Transformer

-- DurableObjects
import TSLean.DurableObjects.Model
import TSLean.DurableObjects.Storage
import TSLean.DurableObjects.State
import TSLean.DurableObjects.Transaction
import TSLean.DurableObjects.WebSocket
import TSLean.DurableObjects.Alarm
import TSLean.DurableObjects.RPC
import TSLean.DurableObjects.Hibernation
import TSLean.DurableObjects.RateLimiter
import TSLean.DurableObjects.ChatRoom
import TSLean.DurableObjects.SessionStore
import TSLean.DurableObjects.Queue
import TSLean.DurableObjects.Auth
import TSLean.DurableObjects.Analytics
import TSLean.DurableObjects.MultiDO
import TSLean.DurableObjects.Http

-- Verification
import TSLean.Verification.ProofObligation
import TSLean.Verification.Invariants
import TSLean.Verification.Tactics

-- Generated (hand-written)
import TSLean.Generated.Hello
import TSLean.Generated.Interfaces
import TSLean.Generated.Classes
import TSLean.Generated.CounterDO
import TSLean.Generated.RateLimiter
import TSLean.Generated.ChatRoom
import TSLean.Generated.SessionStore
import TSLean.Generated.QueueProcessor
import TSLean.Generated.FullProject.Shared.Types
import TSLean.Generated.FullProject.Shared.Validators
import TSLean.Generated.FullProject.Backend.AuthDo
import TSLean.Generated.FullProject.Backend.ChatRoomDo
import TSLean.Generated.FullProject.Backend.RateLimiterDo
import TSLean.Generated.FullProject.Backend.AnalyticsDo
import TSLean.Generated.FullProject.Backend.Router

-- Transpiler output (auto-generated from test fixtures)
import TSLean.Generated.Transpiled_basic_hello
import TSLean.Generated.Transpiled_basic_interfaces
import TSLean.Generated.Transpiled_basic_classes
import TSLean.Generated.Transpiled_advanced_class_features
import TSLean.Generated.Transpiled_advanced_export_patterns
import TSLean.Generated.Transpiled_advanced_for_loops
import TSLean.Generated.Transpiled_advanced_index_signatures
import TSLean.Generated.Transpiled_advanced_optional_chaining
import TSLean.Generated.Transpiled_advanced_template_literals
import TSLean.Generated.Transpiled_advanced_type_narrowing
import TSLean.Generated.Transpiled_effects_async
import TSLean.Generated.Transpiled_effects_exceptions
import TSLean.Generated.Transpiled_generics_branded_types
import TSLean.Generated.Transpiled_generics_discriminated_unions
import TSLean.Generated.Transpiled_generics_generics
import TSLean.Generated.Transpiled_durable_objects_counter
import TSLean.Generated.Transpiled_durable_objects_rate_limiter
import TSLean.Generated.Transpiled_durable_objects_chat_room
import TSLean.Generated.Transpiled_durable_objects_session_store
import TSLean.Generated.Transpiled_durable_objects_queue_processor
import TSLean.Generated.Transpiled_durable_objects_auth_do
import TSLean.Generated.Transpiled_durable_objects_analytics_do
import TSLean.Generated.Transpiled_durable_objects_multi_do

-- Veil Transition Systems
import TSLean.Veil.Core
import TSLean.Veil.DSL
import TSLean.Veil.DSLExamples
import TSLean.Veil.DSLAdoption
import TSLean.Veil.AuthDO
import TSLean.Veil.ChatRoomDO
import TSLean.Veil.CounterDO
import TSLean.Veil.QueueDO
import TSLean.Veil.RateLimiterDO
import TSLean.Veil.SessionStoreDO

-- Workers bindings (Cloudflare KV, R2, D1, Queues, Scheduler)
import TSLean.Workers.KV
import TSLean.Workers.R2
import TSLean.Workers.D1
import TSLean.Workers.Queue
import TSLean.Workers.Scheduler

-- External stubs (TS compiler API, Node.js path/fs)
import TSLean.External.Typescript
import TSLean.External.Path
import TSLean.External.Fs

-- Pre-built npm type stubs
import TSLean.Stubs.NodeFs
import TSLean.Stubs.NodePath
import TSLean.Stubs.NodeHttp
import TSLean.Stubs.Console
import TSLean.Stubs.Process
import TSLean.Stubs.WebAPIs

-- Self-hosting prelude (forward declarations for cross-file references)
import TSLean.Generated.SelfHost.Prelude
-- Self-hosting: all 12 transpiled source files compile (Bootstrap imports them all)
import TSLean.Generated.SelfHost.Bootstrap

-- Proofs (TSLean.Proofs.*) are excluded from the default build target.
-- They reference SelfHost generated namespaces that require a successful
-- self-host pipeline run before compilation.  Build separately:
--   lake build TSLean.Proofs.StdlibProperties  (etc.)

-- Specification & Tests
import TSLean.Specification
import TSLean.Tests
