-- TSLean.Runtime.Inhabited
-- Default (Inhabited) instances for all structures in Runtime/ and DurableObjects/.
-- Transpiled TypeScript code requires `default` for uninitialized variables.

import TSLean.Runtime.Basic
import TSLean.Runtime.BrandedTypes
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

open TSLean TSLean.DO TSLean.Stdlib.HashMap

/-! ## Runtime types -/

instance : Inhabited TSValue := ⟨TSValue.tsNull⟩
instance : Inhabited TSError := ⟨TSError.typeError ""⟩

/-! ## Branded types -/

instance : Inhabited UserId       := ⟨⟨""⟩⟩
instance : Inhabited RoomId       := ⟨⟨""⟩⟩
instance : Inhabited MessageId    := ⟨⟨""⟩⟩
instance : Inhabited SessionToken := ⟨⟨""⟩⟩

/-! ## DurableObjects.Model -/

instance : Inhabited StorageValue := ⟨StorageValue.svNull⟩
instance : Inhabited StorageOp    := ⟨StorageOp.list⟩
instance : Inhabited StorageResult := ⟨StorageResult.modified⟩
instance : Inhabited DOEvent      := ⟨DOEvent.fetch ""⟩
instance [Inhabited σ] : Inhabited (DOState σ) :=
  ⟨{ appState := default, storage := AssocMap.empty }⟩

/-! ## DurableObjects.Alarm -/

instance : Inhabited Alarm.Alarm :=
  ⟨{ id := 0, scheduledAt := 0, createdAt := 0 }⟩

instance : Inhabited Alarm.AlarmState :=
  ⟨{ pending := [], fired := [], nextId := 0 }⟩

/-! ## DurableObjects.Analytics -/

instance : Inhabited Analytics.AnalyticsEvent :=
  ⟨{ name := "", value := 0.0, timestamp := 0, tags := [] }⟩

instance : Inhabited Analytics.AnalyticsState :=
  ⟨{ events := [], counts := [], totalSeen := 0 }⟩

/-! ## DurableObjects.Transaction -/

instance : Inhabited Transaction.Transaction :=
  ⟨Transaction.Transaction.empty⟩

/-! ## DurableObjects.WebSocket -/

instance : Inhabited WebSocket.WsMessage :=
  ⟨WebSocket.WsMessage.ping⟩

instance : Inhabited WebSocket.WsState :=
  ⟨WebSocket.WsState.connecting⟩

instance : Inhabited WebSocket.WsDoState :=
  ⟨{ connections := [], messages := [] }⟩

/-! ## DurableObjects.Hibernation -/

instance [Inhabited σ] : Inhabited (Hibernation.Snapshot σ) :=
  ⟨{ appState := default, storage := AssocMap.empty, version := 0 }⟩

/-! ## DurableObjects.State -/

instance : Inhabited State.Env := ⟨{ bindings := [] }⟩

instance [Inhabited σ] : Inhabited (State.DurableObjectState σ) :=
  ⟨{ id := "", storage := AssocMap.empty, appState := default, env := default }⟩

/-! ## DurableObjects.RateLimiter -/

instance : Inhabited RateLimiter.RateLimiter :=
  ⟨RateLimiter.RateLimiter.empty 1000 10⟩

/-! ## DurableObjects.Queue -/

instance : Inhabited Queue.QueueMessage :=
  ⟨{ id := 0, payload := "", enqueueTime := 0, attempts := 0, maxAttempts := 3 }⟩

instance : Inhabited Queue.DurableQueue :=
  ⟨Queue.DurableQueue.empty⟩

/-! ## DurableObjects.Auth -/

instance : Inhabited Auth.SessionEntry :=
  ⟨{ userId := default, token := default, expiresAt := 0, createdAt := 0 }⟩

/-! ## DurableObjects.SessionStore -/

instance : Inhabited SessionStore.Session :=
  ⟨{ userId := default, token := default, data := [],
     createdAt := 0, expiresAt := 0 }⟩

/-! ## DurableObjects.Http -/

instance : Inhabited Http.HttpMethod := ⟨Http.HttpMethod.GET⟩

instance : Inhabited Http.HttpRequest :=
  ⟨{ method := default, url := "", headers := AssocMap.empty, body := none }⟩

instance : Inhabited Http.HttpResponse :=
  ⟨{ status := 200, headers := AssocMap.empty, body := "" }⟩

/-! ## DurableObjects.RPC -/

instance : Inhabited RPC.RPCRequest :=
  ⟨{ method := "", arg := "", reqId := 0 }⟩

instance : Inhabited RPC.RPCResponse :=
  ⟨{ reqId := 0, result := .ok "" }⟩

/-! ## DurableObjects.ChatRoom -/

instance : Inhabited ChatRoom.ChatMessage :=
  ⟨{ id := default, roomId := default, authorId := default,
     content := "", timestamp := 0 }⟩

instance : Inhabited ChatRoom.ChatRoom :=
  ⟨{ id := default, members := [], messages := [] }⟩

/-! ## DurableObjects.MultiDO -/

instance : Inhabited MultiDO.RPCEnvelope :=
  ⟨{ from_ := "", to_ := "", req := default }⟩

instance : Inhabited MultiDO.RPCResponseEnvelope :=
  ⟨{ from_ := "", to_ := "", resp := default }⟩

instance : Inhabited MultiDO.DONetwork :=
  ⟨{ inbox := [], outbox := [], delivered := [] }⟩
