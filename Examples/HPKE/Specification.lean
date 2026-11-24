module

public import DY.Trace
public import DY.Bytes
public import DY.EquationalTheory.Literal
public import DY.EquationalTheory.Concat
public import DY.EquationalTheory.Hash
public import Examples.HPKE.EqT.AEAD
public import Examples.HPKE.EqT.AKEM
public import DY.Actions.Network
public import DY.Actions.Random
public import DY.Actions.ProtocolEvent
public import DY.Actions.LongTermKeys
public import DY.Comparse

namespace DY.Example.HPKE

open DY.Comparse

public section ExecBytesConfig

class HasExecBytes where
  [bytesFunc: BytesFunctor]
  [bytesFunc0: BytesFunctor.Has Random.SubF]
  [bytesFunc1: BytesFunctor.Has Literal.SubF]
  [bytesFunc2: BytesFunctor.Has Concat.SubF]
  [bytesFunc3: BytesFunctor.Has Hash.SubF]
  [bytesFunc4: BytesFunctor.Has AKEM.SubF]
  [bytesFunc5: BytesFunctor.Has AEAD.SubF]
  [bytesLen: BytesLength]
  [bytesLen0: BytesLength.Has Random.SubF.length]
  [bytesLen1: BytesLength.Has Literal.SubF.length]
  [bytesLen2: BytesLength.Has Concat.SubF.length]
  [bytesLen3: BytesLength.Has Hash.SubF.length]
  [bytesLen4: BytesLength.Has AKEM.SubF.length]
  [bytesLen5: BytesLength.Has AEAD.SubF.length]
  [att: AttackerKnowledge]
  [att0: AttackerKnowledge.Has Random.attackerKnowledge]
  [att1: AttackerKnowledge.Has Literal.attackerKnowledge]
  [att2: AttackerKnowledge.Has Concat.attackerKnowledge]
  [att3: AttackerKnowledge.Has Hash.attackerKnowledge]
  [att4: AttackerKnowledge.Has AKEM.attackerKnowledge]
  [att5: AttackerKnowledge.Has AEAD.attackerKnowledge]

attribute [reducible, scoped instance] HasExecBytes.bytesFunc
attribute [reducible, scoped instance] HasExecBytes.bytesFunc0
attribute [reducible, scoped instance] HasExecBytes.bytesFunc1
attribute [reducible, scoped instance] HasExecBytes.bytesFunc2
attribute [reducible, scoped instance] HasExecBytes.bytesFunc3
attribute [reducible, scoped instance] HasExecBytes.bytesFunc4
attribute [reducible, scoped instance] HasExecBytes.bytesFunc5
attribute [reducible, scoped instance] HasExecBytes.bytesLen
attribute [           scoped instance] HasExecBytes.bytesLen0
attribute [           scoped instance] HasExecBytes.bytesLen1
attribute [           scoped instance] HasExecBytes.bytesLen2
attribute [           scoped instance] HasExecBytes.bytesLen3
attribute [           scoped instance] HasExecBytes.bytesLen4
attribute [           scoped instance] HasExecBytes.bytesLen5
attribute [reducible, scoped instance] HasExecBytes.att
attribute [           scoped instance] HasExecBytes.att0
attribute [           scoped instance] HasExecBytes.att1
attribute [           scoped instance] HasExecBytes.att2
attribute [           scoped instance] HasExecBytes.att3
attribute [           scoped instance] HasExecBytes.att4
attribute [           scoped instance] HasExecBytes.att5

end ExecBytesConfig

public section Structures

variable [HasExecBytes]

structure CiphertextMessage where
  enc: Bytes
  aad: Bytes
  ct: Bytes

inductive HPKEAuthEvent where
  | SealEvent (sender recipient: Participant) (enc: Bytes) (sharedSecret: Bytes) (pt: Bytes)
  | OpenEvent (recipient sender: Participant) (enc: Bytes) (sharedSecret: Bytes) (pt: Bytes)
deriving DecidableEq

end Structures

public section Formats

variable [HasExecBytes]

public
instance: ParseableSerializeable CiphertextMessage := .make <|
  .triviallyIsomorphic
    (.prod .unboundedBytes (.prod .unboundedBytes .bytes))
    (fun ⟨ enc, aad, ct ⟩ => { enc, aad, ct })
    (fun { enc, aad, ct } => ⟨ enc, aad, ct ⟩)

public
theorem CiphertextMessage.IsWellFormed_eq
  (pre: Bytes → τ → Prop) [BytesCompatibleTracePred pre] (x: CiphertextMessage) (tr: τ):
  IsWellFormed pre x tr = (
    pre x.enc tr ∧
    pre x.aad tr ∧
    pre x.ct tr
  )
:= by
  simp [Comparse.IsWellFormed, Comparse.ParseableSerializeable.mf]

grind_pattern CiphertextMessage.IsWellFormed_eq => IsWellFormed pre x tr
grind_pattern [grind_later] CiphertextMessage.IsWellFormed_eq => IsWellFormed pre x tr

end Formats

public section ExecTraceConfig

class HasExecTrace extends HasExecBytes where
  [traceExec: ExecTraceTypes]
  [traceExec0: ExecTraceTypes.Has Network.ExecEntryT]
  [traceExec1: ExecTraceTypes.Has Random.ExecEntryT]
  [traceExec2: ExecTraceTypes.Has (ProtocolEvent.ExecEntryT HPKEAuthEvent)]
  [traceExec3: ExecTraceTypes.Has (LongTermKeys.ExecEntryT "HPKE Auth PKI")]
  [attBase: BaseAttackerKnowledge]

attribute [reducible, scoped instance] HasExecTrace.traceExec
attribute [reducible, scoped instance] HasExecTrace.traceExec0
attribute [reducible, scoped instance] HasExecTrace.traceExec1
attribute [reducible, scoped instance] HasExecTrace.traceExec2
attribute [reducible, scoped instance] HasExecTrace.traceExec3
attribute [reducible, scoped instance] HasExecTrace.attBase

end ExecTraceConfig

public section Specification

variable [HasExecTrace]

instance: LongTermKeys.ExecConfig "HPKE Auth PKI" AKEM.kemPk where

/--
Derives the AEAD encryption key from a shared secret.

RFC mapping:
- HPKE key/nonce material in RFC 9180 is produced by the key schedule
  (Section 5.1, "Creating the Encryption Context") and then consumed by
  `Seal/Open` (Section 5.2; single-shot API in Section 6.1).
- This model uses a simplified deterministic derivation to stand in for the
  RFC key schedule while preserving domain separation intent (Section 9.6).
-/
def deriveKey (sharedSecret: Bytes): Bytes :=
  Hash.hash (Concat.concat (Literal.literalToBytes "key".toByteArray) sharedSecret)

/--
Derives the AEAD nonce from a shared secret.

RFC mapping:
- In RFC 9180, nonce material is derived by the HPKE key schedule
  (Section 5.1) and used by AEAD operations (Section 5.2 / 6.1).
- This model intentionally abstracts that schedule into a direct hash-based
  derivation while retaining explicit domain separation (Section 9.6).
-/
def deriveNonce (sharedSecret: Bytes): Bytes :=
  Hash.hash (Concat.concat (Literal.literalToBytes "nonce".toByteArray) sharedSecret)

/--
Sender-side HPKE protocol action.

RFC mapping:
- Context creation in authenticated asymmetric mode corresponds to
  RFC 9180 Section 5.1.3.
- KEM authenticated encapsulation corresponds to the `AuthEncap` interface
  in Section 4 (see 4.1 for DHKEM realization and 9.2.2 for requirements).
- AEAD encryption behavior corresponds to Section 5.2 (`Seal`) and
  Section 6.1 (single-shot encryption).
- `SealEvent` is model instrumentation for proofs and is not an RFC primitive.
-/
def Sender.seal
  (me recipient: Participant)
  (meSkHandle recipientPkHandle: Nat)
  : Traceful Nat := do
  let recipientPk ← LongTermKeys.getPublicKey "HPKE Auth PKI" recipient recipientPkHandle
  let senderSk ← LongTermKeys.getPrivateKey "HPKE Auth PKI" me meSkHandle
  let entropy ← Random.genRand 32
  let pt ← Random.genRand 32
  let aad ← Random.genRand 32
  let (enc, sharedSecret) := AKEM.kemEncap recipientPk senderSk entropy
  let key := deriveKey sharedSecret
  let nonce := deriveNonce sharedSecret
  ProtocolEvent.logEvent (HPKEAuthEvent.SealEvent me recipient enc sharedSecret pt)
  let ct := AEAD.aead_enc key nonce aad pt
  let msgHandle ← Network.sendMessage (serialize ({ enc, aad, ct } : CiphertextMessage))
  return msgHandle

/--
Recipient-side HPKE protocol action.

RFC mapping:
- Context creation in authenticated asymmetric mode corresponds to
  RFC 9180 Section 5.1.3.
- KEM authenticated decapsulation corresponds to the `AuthDecap` interface
  in Section 4 (see 4.1 for DHKEM realization and 9.2.2 for requirements).
- AEAD decryption behavior corresponds to Section 5.2 (`Open`) and
  Section 6.1 (single-shot decryption).
- `OpenEvent` is model instrumentation for proofs and is not an RFC primitive.
-/
def Recipient.open
  (me sender: Participant)
  (meSkHandle senderPkHandle: Nat)
  (msgHandle: Nat)
  : Traceful Unit := do
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: CiphertextMessage ← parse msgBytes
  let meSk ← LongTermKeys.getPrivateKey "HPKE Auth PKI" me meSkHandle
  let senderPk ← LongTermKeys.getPublicKey "HPKE Auth PKI" sender senderPkHandle
  let sharedSecret ← AKEM.kemDecap meSk senderPk msg.enc
  let key := deriveKey sharedSecret
  let nonce := deriveNonce sharedSecret
  let pt ← (show Err Bytes from AEAD.aead_dec key nonce msg.aad msg.ct)
  ProtocolEvent.logEvent (HPKEAuthEvent.OpenEvent me sender msg.enc sharedSecret pt)
  return ()

end Specification

public section Reachability

variable [HasExecTrace]

@[expose] public section
def Sender.seal.reachability: ReachabilityConfig := .make (fun (me, recipient, meSkHandle, recipientPkHandle) => Sender.seal me recipient meSkHandle recipientPkHandle)
def Recipient.open.reachability: ReachabilityConfig := .make (fun (me, sender, meSkHandle, senderPkHandle, msgHandle) => Recipient.open me sender meSkHandle senderPkHandle msgHandle)
end

#combine into ReachabilityConfig from
  Network,
  LongTermKeys "HPKE Auth PKI",
  Sender.seal,
  Recipient.open,

end Reachability

end DY.Example.HPKE
