module

public import DY.Trace
public import DY.Bytes
public import DY.Actions.Random
public import DY.Actions.Network
public import DY.Actions.PersistentGlobalState
public import DY.Actions.PersistentLocalState
import DY.Meta.Step

/-! # Pre-shared keys (identity-keyed symmetric two-party secret store)

The symmetric-secret analogue of `DY.Actions.LongTermKeys`. A pre-shared key
(PSK) is a *symmetric* secret held by exactly two participants, so — unlike a
long-term keypair (secret local / public global) — it has **no public
projection**: it is stored as `PersistentLocalState` at *both* endpoints and is
compromised if *either* holder's store leaks.

## Identity-keyed labelling (the central design point)

A `LongTermKeys` secret has a *public* projection (`pk = skToPk sk`), so its
secrecy `label` can be keyed on that public value. A PSK has no such projection,
yet a *composing* protocol still needs to refer to "the PSK for this public
identity" (e.g. HPKE's `(recipientPk, psk_id)` tuple) at a **trace-independent**
label — a label whose *value* does not change as the trace grows (only its
`isCorrupt` predicate does), because downstream monotonicity laws (e.g. HPKE's
`pskLabel_later`) demand `label id = label id` across trace extension.

Resolution (mirroring `LongTermKeys.generateKeyPair`): the store record carries
both the secret `psk` **and** the *public identity* `id` it was provisioned for,
and `installPsk` draws a *fresh* random `psk` then **stamps it with the
identity-keyed label** `label name id` (a constant function of the public `id`,
independent of the drawn value). The secrecy `label name id` is therefore keyed
on the public `id`, and `PskIdCompromised name id` — public exactly when *some*
holder's store *bound to this `id`* leaks (`∃ psk p, LocalStateCompromised p
{psk, id}`) — makes it public. This gives a composer the abstract equation
`psk.label tr = label name id` with **no trace lookup and no funext**: the
provisioning step establishes it definitionally from `genRand.spec`.

Like `LongTermKeys` this is **standalone-driver** machinery (network / trust
setup), so a *composing* protocol references only the abstract `psk` value, the
public `id`, and `psk.label tr = label name id`; the concrete store +
`PskIdCompromised` compromise action stays out of the reusable interface. -/

namespace DY.PreSharedKeys

section Execution

/-- A stored pre-shared key. Symmetric, so (unlike `LongTermKeys.SecretKeyState`)
there is no paired public-key state. The record carries both the secret `psk` and
the **public identity** `id` it was provisioned for (e.g. an encoding of HPKE's
`(recipientPk, psk_id)` tuple); the secrecy label is keyed on `id`, so the
identity is stored alongside the secret to let `PskIdCompromised` match a leaked
store to its identity. The `name` distinguishes independent PSK namespaces (e.g.
`"HPKE PSK"`). -/
public
structure PskState [BytesFunctor] (name: String) where
  psk: Bytes
  id: Bytes

public -- it is useful to implement attacker programs
instance
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (name: String)
  : Comparse.ParseableSerializeable (PskState name)
:= .make <|
  .triviallyIsomorphic
    (.prod .slowBytes .bytes)
    (fun ⟨ psk, id ⟩ => { psk, id })
    (fun { psk := psk, id := id } => ⟨ psk, id ⟩)

public -- it is useful to implement attacker programs
theorem PskState.IsWellFormed_eq
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  (pre: Bytes → τ → Prop) [Comparse.BytesCompatibleTracePred pre]
  (x: PskState name) (tr: τ):
  Comparse.IsWellFormed pre x tr = (pre x.psk tr ∧ pre x.id tr)
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern PskState.IsWellFormed_eq => Comparse.IsWellFormed pre x tr

#combine [BytesFunctor] (name: String) into
  ExecEntryT,
  baseAttackerKnowledge,
from
  PersistentLocalState.CompromisableState (PskState name)

variable [BytesFunctor]
variable (name: String)

/-- Install a fresh PSK shared by `p` and `q`, as a **standalone trust-setup
action** (the symmetric analogue of `LongTermKeys.generateKeyPair`): draw a fresh
*public* identity `id` (the `psk_id`, stamped `Label.pub` by the proof) and a
fresh *secret* `psk`, then store the *same* `PskState` — carrying both — at both
endpoints, returning both store handles. Unlike the earlier inline variant, the
identity is drawn *here* rather than supplied by the caller, so both endpoints
provably share one key (`getPsk` reads `id` back out); this is what makes a
psk-mode round-trip reachable. The proof (`installPsk.spec`) stamps the secret
with the identity-keyed label `label name id`. -/
public
def installPsk
  [ExecTraceTypes]
  [BytesFunctor.Has Random.SubF]
  [ExecTraceTypes.Has Random.ExecEntryT]
  [ExecTraceTypes.Has <| ExecEntryT name]
  (p q: Participant)
  : Traceful (Nat × Nat)
:= do
  let id ← Random.genRand 32
  let psk ← Random.genRand 32
  let hp ← PersistentLocalState.storeLocalState p ({psk, id}: PskState name)
  let hq ← PersistentLocalState.storeLocalState q ({psk, id}: PskState name)
  pure (hp, hq)

/-- Read a stored PSK back out at one of its holders. -/
public
def getPsk
  [ExecTraceTypes]
  [ExecTraceTypes.Has <| ExecEntryT name]
  (p: Participant)
  (handle: Nat)
  : Traceful (PskState name)
:= do
  let st: PskState name ← PersistentLocalState.getLocalState p handle
  pure st

/-- Compromise a PSK store (attacker learns the PSK). Publishing at *one* holder's
handle suffices to make the whole shared key public (see `PskIdCompromised`). -/
public
def compromisePsk
  [ExecTraceTypes]
  [ExecTraceTypes.Has <| ExecEntryT name]
  [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [ExecTraceTypes.Has Network.ExecEntryT]
  (handle: Nat)
  : Traceful Nat
:= do
  PersistentLocalState.compromise (PskState name) handle

/-- A PSK identity `id` is compromised once *any* holder's store bound to `id` is
compromised (symmetric secret: either party leaking exposes it). Keyed on the
public identity `id`, existentially quantified over both the holder and the (now
public) secret value, so both endpoints' stores agree on the resulting label. -/
public
def PskIdCompromised
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT name)]
  (id: Bytes)
  (tr: ExecTrace)
  : Prop
:=
  ∃ psk: Bytes, ∃ p: Participant,
    PersistentLocalState.LocalStateCompromised p ({psk, id}: PskState name) tr

public
theorem PskIdCompromised_le
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT name)]
  (id: Bytes)
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    PskIdCompromised name id tr1 →
    PskIdCompromised name id tr2
:= by
  simp [PskIdCompromised]
  grind

grind_pattern PskIdCompromised_le => tr1 ≤ tr2, PskIdCompromised name id tr1
grind_pattern [grind_later] PskIdCompromised_le => tr1 ≤ tr2, PskIdCompromised name id tr1

end Execution

section Proof

/-- The secrecy label of a PSK, keyed on its **public identity** `id`: public
exactly when *some* holder's store bound to `id` is compromised. The *value* is
independent of the trace (only `isCorrupt` grows), so a composer can transport it
across trace extension by `rfl`. -/
@[expose]
public
def label
  [BytesFunctor]
  (name: String)
  [ExecTraceTypes] [ExecTraceTypes.Has (ExecEntryT name)]
  (id: Bytes)
  : Label
where
  isCorrupt := PskIdCompromised name id

/-- Trust configuration for a PSK namespace: the intended usage the standalone
driver assigns to installed PSKs. Mirrors `LongTermKeys.ProofConfig` minus the
public-key half; the secrecy label is fixed (the identity-keyed `label name id`),
so — unlike `LongTermKeys` — there is no per-value `lab` degree of freedom. -/
public
class ProofConfig
  [BytesFunctor] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  (name: String) (usage: outParam Usage)
  [ExecTraceTypes.Has (ExecEntryT name)]
where
  psk_usage: Usage := usage

variable [BytesFunctor]

/-- The proof-side well-formedness of an installed PSK bound to public identity
`id`: well-formed, labeled at the identity-keyed secrecy label `label name id`,
tagged with the configured usage, and provisioned for a *public* identity `id`.
The symmetric analogue of `LongTermKeys.IsLongTermSecretKey`. -/
@[expose]
public
def IsPreSharedKey
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants]
  (name: String) {usage: Usage}
  [ExecTraceTypes.Has (ExecEntryT name)]
  [ProofConfig name usage]
  (b: Bytes) (id: Bytes) (tr: ProofTrace)
  : Prop
:=
  b.Invariant tr ∧
  b.label tr = label name id ∧
  b.HasUsage usage tr ∧
  id.Invariant tr ∧
  id.label tr = Label.pub

public
theorem IsPreSharedKey_later
  [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
  (name: String) {usage: Usage}
  [ExecTraceTypes.Has (ExecEntryT name)]
  [ProofConfig name usage]
  (b: Bytes) (id: Bytes) (tr1 tr2: ProofTrace)
  : tr1 ≤ tr2 →
    IsPreSharedKey name b id tr1 →
    IsPreSharedKey name b id tr2
:= by
  grind [IsPreSharedKey]

grind_pattern [grind_later] IsPreSharedKey_later => tr1 ≤ tr2, IsPreSharedKey name b id tr1

section
variable [BytesLength] [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariantsProofs]
variable [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
variable [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
variable [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
variable (name: String)
variable [ExecTraceTypes.Has <| ExecEntryT name]
variable {usage: Usage}
variable [ProofConfig name usage]

public
instance: PersistentLocalState.CompromisableLocalStateInv (PskState name) where
  invariant _p st tr :=
    IsPreSharedKey name st.psk st.id tr
  invariant_later := by grind [IsPreSharedKey]
  invariant_implies_KnowableBy := by
    intro participant state tr h
    cases state with | mk psk id =>
    obtain ⟨h_inv, h_lbl, h_usage, h_id_inv, h_id_lbl⟩ := h
    have h_psk_flow:
        (label name id).canFlow
          (PersistentLocalState.label participant ({psk, id}: PskState name)) tr.erase := by
      simp_all [Label.canFlow, label, PskIdCompromised, PersistentLocalState.label_isCorrupt]
      grind
    have h_id_flow:
        (id.label tr).canFlow
          (PersistentLocalState.label participant ({psk, id}: PskState name)) tr.erase := by
      rw [h_id_lbl]
      exact Label.pubCanFlow (PersistentLocalState.label participant ({psk, id}: PskState name)) tr.erase
    simp only [PskState.IsWellFormed_eq, Bytes.KnowableBy]
    rw [h_lbl]
    exact ⟨⟨h_inv, h_psk_flow⟩, ⟨h_id_inv, h_id_flow⟩⟩

end

#combine [BytesFunctor] (name: String) into ProofEntryT
from
  PersistentLocalState.CompromisableState (PskState name)

#combine
  [BytesFunctor] (name: String)
  [BytesLength] [BytesInvariants] [BytesInvariantsProofs]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  [ExecTraceTypes.Has <| ExecEntryT name]
  {usage: Usage}
  [ProofConfig name usage]
into
  SubTraceInvariant,
  SubBaseAttackerKnowledgeTheorem__noExecHas,
from
  PersistentLocalState.CompromisableState (PskState name)

@[instance]
public
theorem installPsk.spec
  [BytesFunctor]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]

  (name: String) {usage: Usage}

  [BytesFunctor.Has Random.SubF]
  [ExecTraceTypes.Has <| Random.ExecEntryT]
  [ProofTraceTypes.Has <| Random.ProofEntryT]
  [ExecTraceTypes.Has <| ExecEntryT name]
  [ProofTraceTypes.Has <| ProofEntryT name]
  [BytesInvariants.Has <| Random.invariants]
  [ProofConfig name usage]
  [TraceInvariant.Has <| Random.ProofEntryT]
  [TraceInvariant.Has <| ProofEntryT name]
  (p q: Participant)
  : HoareTriple
    (installPsk name p q)
    (fun _ => True)
    (fun _ _ => True)
:= by
  apply HoareTriple.mk
  unfold installPsk
  step with ⟨ fun _id => Label.pub, Usage.nothing ⟩
  step with ⟨ fun _psk => label name id, usage ⟩
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant, IsPreSharedKey]
    exact ⟨‹psk.Invariant tr›, ‹psk.label tr = label name id›, ‹psk.HasUsage usage tr›,
      ‹id.Invariant tr›, ‹id.label tr = Label.pub›⟩
  step by
    simp only [PersistentLocalState.LocalStateInv.invariant, IsPreSharedKey]
    exact ⟨‹psk.Invariant tr›, ‹psk.label tr = label name id›, ‹psk.HasUsage usage tr›,
      ‹id.Invariant tr›, ‹id.label tr = Label.pub›⟩
  step
  trivial

@[instance]
public
theorem getPsk.spec
  [BytesFunctor]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]

  (name: String) {usage: Usage}
  [ExecTraceTypes.Has <| ExecEntryT name]
  [ProofTraceTypes.Has <| ProofEntryT name]
  [ProofConfig name usage]
  [TraceInvariant.Has <| ProofEntryT name]
  (p: Participant) (handle: Nat)
  : HoareTriple
    (getPsk name p handle)
    (fun _ => True)
    (fun res tr => IsPreSharedKey name res.psk res.id tr)
:= by
  unfold getPsk
  step
  step
  simp_all [PersistentLocalState.LocalStateInv.invariant, IsPreSharedKey]

@[instance]
public
theorem compromisePsk.spec
  [BytesFunctor]
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesLength] [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length] [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length] [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]

  (name: String) {usage: Usage}
  [ExecTraceTypes.Has <| ExecEntryT name]
  [ProofTraceTypes.Has <| ProofEntryT name]
  [ProofConfig name usage]
  [ExecTraceTypes.Has <| Network.ExecEntryT]
  [ProofTraceTypes.Has <| Network.ProofEntryT]
  [TraceInvariant.Has <| Network.ProofEntryT]
  [TraceInvariant.Has <| ProofEntryT name]
  (handle: Nat)
  : HoareTriple
    (compromisePsk name handle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold compromisePsk
  step
  trivial

end Proof

section Reachability

variable
  [BytesFunctor]
  (name: String)
  [ExecTraceTypes]
  [BytesLength]
  [BytesFunctor.Has Literal.SubF] [BytesLength.Has Literal.SubF.length]
  [BytesFunctor.Has Concat.SubF] [BytesLength.Has Concat.SubF.length]
  [BytesFunctor.Has Random.SubF]
  [ExecTraceTypes.Has Random.ExecEntryT]
  [ExecTraceTypes.Has Network.ExecEntryT]
  [ExecTraceTypes.Has <| ExecEntryT name]

/-- Standalone trust-setup action for a PSK namespace: provision a fresh shared
PSK for the participant pair `(p, q)` (the symmetric analogue of
`LongTermKeys.generateKeyPair`). Both endpoints receive handles to the *same*
stored key, so a psk-mode round-trip between them is reachable. -/
@[expose]
public
def installPsk.reachability : ReachabilityConfig :=
  .make (fun (p, q) => installPsk name p q)

/-- Attacker action for a PSK namespace: compromise a stored PSK (leak the shared
symmetric secret). -/
@[expose]
public
def compromisePsk.reachability : ReachabilityConfig :=
  .make (fun handle => compromisePsk name handle)

@[expose]
public
def reachability.internal : Fin 2 → ReachabilityConfig
  | 0 => installPsk.reachability name
  | 1 => compromisePsk.reachability name

@[expose]
public
def reachability : ReachabilityConfig :=
  .combine (reachability.internal name)

public instance: ReachabilityConfig.HasStep (installPsk.reachability name) (reachability name) := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal name 0) (.combine (reachability.internal name))
public instance: ReachabilityConfig.HasStep (compromisePsk.reachability name) (reachability name) := inferInstanceAs <| ReachabilityConfig.HasStep (reachability.internal name 1) (.combine (reachability.internal name))

variable
  [ProofTraceTypes]
  [TraceInvariant]
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has Literal.invariants] [BytesInvariants.Has Concat.invariants]
  {usage: Usage}
  [ProofTraceTypes.Has <| Random.ProofEntryT]
  [ProofTraceTypes.Has <| Network.ProofEntryT]
  [ProofTraceTypes.Has <| ProofEntryT name]
  [BytesInvariants.Has <| Random.invariants]
  [ProofConfig name usage]
  [TraceInvariant.Has <| Random.ProofEntryT]
  [TraceInvariant.Has <| Network.ProofEntryT]
  [TraceInvariant.Has <| ProofEntryT name]

public
instance: ReachableImpliesInvariant (installPsk.reachability name) where
  pf := fun (p, q) => installPsk.spec name p q

public
instance: ReachableImpliesInvariant (compromisePsk.reachability name) where
  pf handle := compromisePsk.spec name handle

public instance: ∀ id, ReachableImpliesInvariant (reachability.internal name id)
  | 0 => inferInstanceAs <| ReachableImpliesInvariant (installPsk.reachability name)
  | 1 => inferInstanceAs <| ReachableImpliesInvariant (compromisePsk.reachability name)

public instance: ReachableImpliesInvariant (reachability name) := inferInstanceAs (ReachableImpliesInvariant (.combine (reachability.internal name)))

end Reachability

end DY.PreSharedKeys
