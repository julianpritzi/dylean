module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation -- HoareTriplePure

namespace DY.AEAD

public
class CanAEAD (Bytes: Type u) where
  aead_enc: (key: Bytes) → (nonce: Bytes) → (aad: Bytes) → (msg: Bytes) → Bytes
  aead_dec: (key: Bytes) → (nonce: Bytes) → (aad: Bytes) → (ct: Bytes) → Option Bytes

export CanAEAD (aead_enc)
export CanAEAD (aead_dec)

section Constructors

namespace AeadEnc

public
structure SubF (Bytes: Type) where
  key: Bytes
  nonce: Bytes
  aad: Bytes
  msg: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {key, nonce, aad, msg} => sizeOf key + sizeOf nonce + sizeOf aad + sizeOf msg

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 4 }

  toRepr | {key, nonce, aad, msg} => {
    id := ()
    data := ()
    as := #v[key, nonce, aad, msg]
  }
  fromRepr
  | {id, data, as} =>
    let key := as[0]
    let nonce := as[1]
    let aad := as[2]
    let msg := as[3]
    { key, nonce, aad, msg }
  from_to | {key, nonce, aad, msg} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {key, nonce, aad, msg} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

-- Ciphertext length follows plaintext length only in this symbolic model;
-- associated data is authenticated but not carried in the ciphertext size.
-- Authentication tag overhead is still not modeled explicitly.
public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { key, nonce, aad, msg } rec =>
    rec msg

end AeadEnc

#combine into BytesFunctor, BytesLength from
  AeadEnc,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev AeadEnc.SubF.pack (x: AeadEnc.SubF Bytes) := BytesView.pack x

public
instance: CanAEAD Bytes where
  -- Encryption: pack key, nonce, associated data, and plaintext into a symbolic ciphertext term.
  aead_enc key nonce aad msg :=
    ({key, nonce, aad, msg}: AeadEnc.SubF Bytes).pack

  -- Decryption: extract msg only if key, nonce, and associated data all match exactly.
  aead_dec key nonce aad ct :=
    match ct.view? AeadEnc.SubF with
    | some { key := key', nonce := nonce', aad := aad', msg } =>
      if key == key' && nonce == nonce' && aad == aad' then some msg else none
    | none => none

-- Core equational property: decryption undoes encryption when key, nonce, and aad agree.
public
theorem aead_dec_enc
  (key nonce aad msg: Bytes)
  : aead_dec key nonce aad (aead_enc key nonce aad msg) = some msg
:= by
  simp only [aead_dec, aead_enc]
  grind

-- Decryption fails when the key does not match.
public
theorem aead_dec_enc_wrong_key
  (key key' nonce aad msg: Bytes)
  (h: key ≠ key')
  : aead_dec key' nonce aad (aead_enc key nonce aad msg) = none
:= by
  simp only [aead_dec, aead_enc]
  grind

-- Decryption fails when the nonce does not match.
public
theorem aead_dec_enc_wrong_nonce
  (key nonce nonce' aad msg: Bytes)
  (h: nonce ≠ nonce')
  : aead_dec key nonce' aad (aead_enc key nonce aad msg) = none
:= by
  simp only [aead_dec, aead_enc]
  grind

-- Decryption fails when the associated data does not match.
public
theorem aead_dec_enc_wrong_aad
  (key nonce aad aad' msg: Bytes)
  (h: aad ≠ aad')
  : aead_dec key nonce aad' (aead_enc key nonce aad msg) = none
:= by
  simp only [aead_dec, aead_enc]
  grind

end Constructors

section AttackerKnowledge

-- Forward rule: attacker can compute a ciphertext if they know key, nonce, aad, and plaintext.
public
def aead_enc.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key nonce aad msg,
      out = aead_enc key nonce aad msg ∧
      p key ∧ p nonce ∧ p aad ∧ p msg

-- Recovery rule: attacker can recover the plaintext if they know key, nonce, aad, and ciphertext.
public
def aead_open.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ key nonce aad,
      p key ∧ p nonce ∧ p aad ∧ p (aead_enc key nonce aad out)

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  aead_enc,
  aead_open,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

-- If the attacker knows key, nonce, aad, and plaintext, they can produce the ciphertext.
public
theorem attacker_knows_aead_enc
  (key nonce aad msg: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    nonce.AttackerKnows tr →
    aad.AttackerKnows tr →
    msg.AttackerKnows tr →
    (aead_enc key nonce aad msg).AttackerKnows tr
:= by
  intro h_key h_nonce h_aad h_msg
  apply Bytes.AttackerKnows.prove aead_enc.attackerKnowledge
  simp only [aead_enc.attackerKnowledge]
  grind

-- If the attacker knows key, nonce, aad, and the ciphertext, they recover the plaintext.
public
theorem attacker_knows_aead_dec
  (key nonce aad msg: Bytes) (tr: ExecTrace)
  : key.AttackerKnows tr →
    nonce.AttackerKnows tr →
    aad.AttackerKnows tr →
    (aead_enc key nonce aad msg).AttackerKnows tr →
    msg.AttackerKnows tr
:= by
  intro h_key h_nonce h_aad h_ct
  apply Bytes.AttackerKnows.prove aead_open.attackerKnowledge
  simp only [aead_open.attackerKnowledge]
  exact ⟨key, nonce, aad, h_key, h_nonce, h_aad, h_ct⟩

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

/--
`AeadPred` is the protocol-specific *authentication hook* carried by every AEAD
ciphertext. It is the direct analogue of `DY.Signature.SignPred`.
-/
public
class AeadPred where
  pred: [BytesWellFormed] → [GetUsage] → [GetLabel] →
    (key aad msg: Bytes) → ProofTrace → Prop

public
class AeadPredProof [BytesInvariants] [AeadPred] where
  pred_later:
    [BytesWellFormedLater] → [GetUsageLater] → [GetLabelLater] →
    ∀ key aad msg tr1 tr2,
      key.WellFormed tr1 →
      aad.WellFormed tr1 →
      msg.WellFormed tr1 →
      tr1 ≤ tr2 →
      AeadPred.pred key aad msg tr1 →
      AeadPred.pred key aad msg tr2

grind_pattern AeadPredProof.pred_later => tr1 ≤ tr2, AeadPred.pred key aad msg tr1

public
theorem AeadPredProof.pred_later_fast
  [BytesInvariants] [AeadPred] [AeadPredProof] [BytesInvariantsProofs]
  (key aad msg: Bytes) (tr1 tr2: ProofTrace)
  : key.Invariant tr1 →
    aad.Invariant tr1 →
    msg.Invariant tr1 →
    tr1 ≤ tr2 →
    AeadPred.pred key aad msg tr1 →
    AeadPred.pred key aad msg tr2
:= by grind

grind_pattern [grind_later] AeadPredProof.pred_later_fast => tr1 ≤ tr2, AeadPred.pred key aad msg tr1

variable [AeadPred]

public
def AeadEnc.invariants: Bytes.PartialInvariants AeadEnc.SubF where
  well_formed := fun {key, nonce, aad, msg} rec tr =>
    (rec key) tr ∧
    (rec nonce) tr ∧
    (rec aad) tr ∧
    (rec msg) tr

  usage := fun {key, nonce, aad, msg} rec tr =>
    Usage.nothing

  label := fun {key, nonce, aad, msg} rec tr =>
    Label.pub

  invariant := fun {key, nonce, aad, msg} rec tr =>
    (rec key) tr ∧
    (rec nonce) tr ∧
    (rec aad) tr ∧
    (rec msg) tr ∧
    (msg.label tr).canFlow (key.label tr) tr.erase ∧
    (
      (
        -- Honest case: the authentication predicate holds.
        AeadPred.pred key aad msg tr
      ) ∨ (
        -- Attacker case: the key is (or has become) public.
        (key.label tr).canFlow Label.pub tr.erase
      )
    )

public
def AeadEnc.invariantsProofs [BytesInvariants] [AeadPredProof]: Bytes.PartialInvariantsProofs AeadEnc.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind

#combine [BytesFunctor.Has SubF] [AeadPred] into
  BytesInvariants,
  BytesInvariantsProofs [AeadPredProof]
from
  AeadEnc,

variable [BytesInvariants] [BytesInvariants.Has invariants]

@[simp]
public
theorem aead_enc.WellFormed
  (key nonce aad msg: Bytes) (tr: ProofTrace)
  : (aead_enc key nonce aad msg).WellFormed tr =
    (key.WellFormed tr ∧ nonce.WellFormed tr ∧ aad.WellFormed tr ∧ msg.WellFormed tr)
:= by
  simp [aead_enc, Bytes.WellFormed.eq, AeadEnc.invariants]

@[simp]
public
theorem aead_enc.label_eq
  (key nonce aad msg: Bytes) (tr: ProofTrace)
  : (aead_enc key nonce aad msg).label tr = Label.pub
:= by
  simp [aead_enc, Bytes.label.eq, AeadEnc.invariants]

public
theorem aead_enc.Invariant
  (key nonce aad msg: Bytes) (tr: ProofTrace)
  : (
      key.Invariant tr ∧
      nonce.Invariant tr ∧
      aad.Invariant tr ∧
      msg.Invariant tr ∧
      (msg.label tr).canFlow (key.label tr) tr.erase ∧
      (
        (
          AeadPred.pred key aad msg tr
        ) ∨ (
          (key.label tr).canFlow Label.pub tr.erase
        )
      )
    ) →
    (aead_enc key nonce aad msg).Invariant tr
:= by
  simp [aead_enc, Bytes.Invariant.eq, AeadEnc.invariants]

public
theorem aead_dec.Invariant
  (key nonce aad ct pt: Bytes) (tr: ProofTrace)
  : ct.Invariant tr →
    aead_dec key nonce aad ct = some pt →
    (
      (
        AeadPred.pred key aad pt tr
      ) ∨ (
        (key.label tr).canFlow Label.pub tr.erase
      )
    )
:= by
  simp only [aead_dec]
  split
  · rename_i key' nonce' aad' msg heq
    have := Bytes.pack_view? AeadEnc.SubF ct
    simp only [heq] at this
    subst this
    split
    · rename_i hcond
      intro h_ct h_eq
      simp_all [Bytes.Invariant.eq, AeadEnc.invariants]
    · simp
  · simp

end Invariants

section AttackerKnowledgeTheoremInstances

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [AeadPred]
variable [BytesInvariants.Has invariants]

public
instance : SubAttackerKnowledgeTheorem aead_enc.attackerKnowledge where
  pf := by
    simp only [aead_enc.attackerKnowledge]
    intro out tr h_tr ⟨key, nonce, aad, msg, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    simp [aead_enc, Bytes.Invariant.eq, AeadEnc.invariants]
    grind [canFlowTrans]

public
instance : SubAttackerKnowledgeTheorem aead_open.attackerKnowledge where
  pf := by
    simp only [aead_open.attackerKnowledge]
    intro out tr h_tr ⟨key, nonce, aad, h_inputs⟩
    simp_all [Bytes.Publishable, aead_enc, Bytes.Invariant.eq, AeadEnc.invariants]
    grind [canFlowTrans]

end AttackerKnowledgeTheoremInstances

section HoareTriples

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [AeadPred]
variable [BytesInvariants] [BytesInvariants.Has invariants]

public
instance aead_enc_hoareTriple
  (key nonce aad msg: Bytes)
  : HoareTriplePure
    (aead_enc key nonce aad msg)
    (fun tr =>
      key.Invariant tr ∧
      nonce.Invariant tr ∧
      aad.Invariant tr ∧
      msg.Invariant tr ∧
      (msg.label tr).canFlow (key.label tr) tr.erase ∧
      (
        (
          AeadPred.pred key aad msg tr
        ) ∨ (
          (key.label tr).canFlow Label.pub tr.erase
        )
      )
    )
    (fun ct tr =>
      ct.Publishable tr ∧
      ct.Invariant tr ∧
      ct.label tr = Label.pub
    )
where
  pf := by
    intro tr h
    have hi := aead_enc.Invariant key nonce aad msg tr h
    have hl := aead_enc.label_eq key nonce aad msg tr
    grind

public
instance aead_dec_hoareTriple
  (key nonce aad ct: Bytes)
  : HoareTriplePure
    (aead_dec key nonce aad ct)
    (fun tr =>
      key.Invariant tr ∧
      nonce.Invariant tr ∧
      aad.Invariant tr ∧
      ct.Invariant tr
    )
    (fun result tr =>
      match result with
      | none => True
      | some pt =>
        pt.Invariant tr ∧
        (pt.label tr).canFlow (key.label tr) tr.erase ∧
        (
          (
            AeadPred.pred key aad pt tr
          ) ∨ (
            (key.label tr).canFlow Label.pub tr.erase
          )
        )
    )
where
  pf := by
    intro tr ⟨h_key, h_nonce, h_aad, h_ct⟩
    cases heq : aead_dec key nonce aad ct with
    | none => trivial
    | some pt =>
      simp only [aead_dec] at heq
      split at heq
      · rename_i key' nonce' aad' msg hview_eq
        have hview := Bytes.pack_view? AeadEnc.SubF ct
        simp only [hview_eq] at hview
        subst hview
        split at heq
        · rename_i hcond
          simp_all [Bytes.Invariant.eq, AeadEnc.invariants]
        · simp at heq
      · simp at heq

end HoareTriples

section CombinedAttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [AeadPred]
variable [BytesInvariants.Has invariants]

#combine [BytesFunctor.Has SubF] [AeadPred] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  aead_enc,
  aead_open,

public
instance attackerKnowledgeTheorem : SubAttackerKnowledgeTheorem attackerKnowledge := by
  infer_instance

end CombinedAttackerKnowledgeTheorem

end DY.AEAD
