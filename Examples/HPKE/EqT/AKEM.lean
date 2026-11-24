module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation
public import DY.Meta

-- Modified version of Examples/SignedDHKEM/KEM.lean to add support for authenticated KEMs (AKEMs).
-- Also simplified the attacker model, by omitting the "Broken" sections.
namespace DY.AKEM

public
class CanAkem (Bytes: Type u) where
  kemPk: (sk: Bytes) → Bytes
  kemEncap: (pkR: Bytes) → (skS: Bytes) → (entropy: Bytes) → Bytes × Bytes
  kemDecap: (skR: Bytes) → (pkS: Bytes) → (cipher: Bytes) → Err Bytes

export CanAkem (kemPk)
export CanAkem (kemEncap)
export CanAkem (kemDecap)

section Constructors

namespace Pk

public
structure SubF (Bytes: Type) where
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {sk} => sizeOf sk

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }

  toRepr | {sk} => {
    id := ()
    data := ()
    as := #v[sk]
  }
  fromRepr
  | {id, data, as} =>
    let sk := as[0]
    { sk }
  from_to | {sk} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {sk} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    800 -- modeled after ML-KEM-512 public-key size

end Pk

namespace Encap

public
structure SubF (Bytes: Type) where
  pkR: Bytes
  skS: Bytes
  entropy: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {pkR, skS, entropy} => sizeOf pkR + sizeOf skS + sizeOf entropy

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 3 }

  toRepr | {pkR, skS, entropy} => {
    id := ()
    data := ()
    as := #v[pkR, skS, entropy]
  }
  fromRepr
  | {id, data, as} =>
    let pkR := as[0]
    let skS := as[1]
    let entropy := as[2]
    { pkR, skS, entropy }
  from_to | {pkR, skS, entropy} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {pkR, skS, entropy} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    768 -- modeled after ML-KEM-512 ciphertext size

end Encap

namespace SharedSecret

public
structure SubF (Bytes: Type) where
  pkR: Bytes
  skS: Bytes
  entropy: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {pkR, skS, entropy} => sizeOf pkR + sizeOf skS + sizeOf entropy

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 3 }

  toRepr | {pkR, skS, entropy} => {
    id := ()
    data := ()
    as := #v[pkR, skS, entropy]
  }
  fromRepr
  | {id, data, as} =>
    let pkR := as[0]
    let skS := as[1]
    let entropy := as[2]
    { pkR, skS, entropy }
  from_to | {pkR, skS, entropy} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {pkR, skS, entropy} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32 -- modeled after ML-KEM-512 shared-secret size

end SharedSecret

#combine into BytesFunctor, BytesLength from
  Pk,
  Encap,
  SharedSecret,

variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev Pk.SubF.pack (x: Pk.SubF Bytes) := BytesView.pack x
public abbrev Encap.SubF.pack (x: Encap.SubF Bytes) := BytesView.pack x
public abbrev SharedSecret.SubF.pack (x: SharedSecret.SubF Bytes) := BytesView.pack x

public
instance: CanAkem Bytes where
  kemPk sk :=
    ({sk}: Pk.SubF Bytes).pack

  kemEncap pkR skS entropy :=
    (({pkR, skS, entropy}: Encap.SubF Bytes).pack, ({pkR, skS, entropy}: SharedSecret.SubF Bytes).pack)

  kemDecap skR pkS cipher :=
    match cipher.view? Encap.SubF with
    | some {pkR, skS := skS', entropy} =>
      if ({sk := skR}: Pk.SubF Bytes).pack = pkR && pkS = ({sk := skS'}: Pk.SubF Bytes).pack then
        some ({pkR, skS := skS', entropy}: SharedSecret.SubF Bytes).pack
      else
        none
    | none => none

public
theorem kemDecap_kemEncap
  (skR skS entropy: Bytes)
  : let (cipher, ss) := kemEncap (kemPk skR) skS entropy
    kemDecap skR (kemPk skS) cipher = some ss
:= by
  simp only [kemPk, kemEncap, kemDecap]
  grind

-- A successful `kemDecap` fully determines the ciphertext's encapsulation view and
-- pins every field: the sender key, the receiver key, and the shared-secret shape.
public
theorem decap_success
  (skR pkS cipher ss: Bytes)
  (hDecap: kemDecap skR pkS cipher = some ss)
  : ∃ pkR skS' entropy,
    cipher.view? Encap.SubF = some ({pkR, skS := skS', entropy} : Encap.SubF Bytes) ∧
    kemPk skS' = pkS ∧
    pkR = kemPk skR ∧
    ss = ({pkR := pkR, skS := skS', entropy := entropy} : SharedSecret.SubF Bytes).pack
:= by
  change
    (match cipher.view? Encap.SubF with
    | some {pkR, skS := skS', entropy} =>
      if ({sk := skR}: Pk.SubF Bytes).pack = pkR && pkS = ({sk := skS'}: Pk.SubF Bytes).pack then
        some ({pkR, skS := skS', entropy}: SharedSecret.SubF Bytes).pack
      else
        none
    | none =>
      none) = some ss at hDecap
  split at hDecap
  · rename_i pkR skS' entropy hView
    by_cases hPkR : ({sk := skR}: Pk.SubF Bytes).pack = pkR
    · by_cases hPkS : pkS = ({sk := skS'}: Pk.SubF Bytes).pack
      · refine ⟨pkR, skS', entropy, hView, ?_, ?_, ?_⟩
        · simp [kemPk]; exact hPkS.symm
        · unfold kemPk; exact hPkR.symm
        · simp [hPkR, hPkS] at hDecap; exact hDecap.symm
      · simp [hPkR, hPkS] at hDecap
    · simp [hPkR] at hDecap
  · cases hDecap

@[simp]
public
theorem Encap.SubF.pack_view_eq
  (x : Encap.SubF Bytes)
  : (x.pack).view? Encap.SubF = some x
:= by
  exact BytesView.view_pack x

@[simp]
public
theorem SharedSecret.SubF.pack_view_eq
  (x : SharedSecret.SubF Bytes)
  : (x.pack).view? SharedSecret.SubF = some x
:= by
  exact BytesView.view_pack x

end Constructors

section AttackerKnowledge

public
def kemPk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = kemPk sk ∧
      p sk

public
def kemEncapCipher.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pkR skS entropy rhs,
      (out, rhs) = kemEncap pkR skS entropy ∧
      p pkR ∧ p skS ∧ p entropy

public
def kemEncapSS.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ pkR skS entropy lhs,
      (lhs, out) = kemEncap pkR skS entropy ∧
      p pkR ∧ p skS ∧ p entropy

public
def kemDecap.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ skR pkS cipher,
      some out = kemDecap skR pkS cipher ∧
      p skR ∧ p pkS ∧ p cipher

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  kemPk,
  kemEncapCipher,
  kemEncapSS,
  kemDecap,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem kemPk.attacker_knows
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (kemPk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove kemPk.attackerKnowledge
  simp only [kemPk.attackerKnowledge]
  grind

public
theorem kemEncap.attacker_knows
  (pkR skS entropy: Bytes) (tr: ExecTrace)
  : pkR.AttackerKnows tr →
    skS.AttackerKnows tr →
    entropy.AttackerKnows tr →
    (kemEncap pkR skS entropy).fst.AttackerKnows tr ∧
    (kemEncap pkR skS entropy).snd.AttackerKnows tr
:= by
  intro h_pkR h_skS h_entropy
  apply And.intro
  · apply Bytes.AttackerKnows.prove kemEncapCipher.attackerKnowledge
    simp only [kemEncapCipher.attackerKnowledge]
    grind
  · apply Bytes.AttackerKnows.prove kemEncapSS.attackerKnowledge
    simp only [kemEncapSS.attackerKnowledge]
    grind

public
theorem kemDecap.attacker_knows
  (skR pkS cipher: Bytes) (tr: ExecTrace)
  : skR.AttackerKnows tr →
    pkS.AttackerKnows tr →
    cipher.AttackerKnows tr →
    match kemDecap skR pkS cipher with
    | none => True
    | some ss => ss.AttackerKnows tr
:= by
  intro h_skR h_pkS h_cipher
  split
  · grind
  apply Bytes.AttackerKnows.prove kemDecap.attackerKnowledge
  simp only [kemDecap.attackerKnowledge]
  grind

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has AKEM.SubF]

public
def Pk.invariants: Bytes.PartialInvariants Pk.SubF where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := sk} rec tr =>
    Usage.nothing

  label := fun {sk := sk} rec tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (rec sk) tr

public
def Pk.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Pk.invariants where

section PkLemmas

variable [BytesInvariants] [BytesInvariants.Has Pk.invariants]

@[simp]
public
theorem kemPk.WellFormed
  (inp: Bytes) (tr: ProofTrace)
  : (kemPk inp).WellFormed tr = inp.WellFormed tr
:= by
  simp [kemPk, Bytes.WellFormed.eq, Pk.invariants]

@[simp]
public
theorem kemPk.label
  (inp: Bytes) (tr: ProofTrace)
  : (kemPk inp).label tr = Label.pub
:= by
  simp [kemPk, Bytes.label.eq, Pk.invariants]

@[simp]
public
theorem kemPk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  : sk.Invariant tr →
    (kemPk sk).Invariant tr
:= by
  simp [kemPk, Bytes.Invariant.eq, Pk.invariants]

end PkLemmas

end Invariants

end AKEM

section ExtractKemPk

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]
variable [BytesFunctor.Has AKEM.SubF]

public
noncomputable
def AKEM.extractKemSk (pk: Bytes): Option Bytes :=
  match pk.view? AKEM.Pk.SubF with
  | some { sk } =>
    some sk
  | none => none

omit [ExecTraceTypes] [ProofTraceTypes] in
theorem AKEM.kemPk_extractKemSk (b: Bytes)
  : match extractKemSk b with
    | none => True
    | some sk => b = AKEM.kemPk sk
:= by
  simp [extractKemSk, AKEM.kemPk]
  grind

public
theorem AKEM.extractKemSk.preserves_WellFormed
  [BytesInvariants] [BytesInvariants.Has AKEM.Pk.invariants]
: ExtractPreservesWellFormed AKEM.extractKemSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [AKEM.kemPk_extractKemSk, AKEM.kemPk.WellFormed]

@[expose]
public
def Bytes.KemSkHasUsage
  [BytesInvariants]
  (pk: Bytes) (skUsg: Usage) (tr: ProofTrace): Prop
:=
  Bytes.XXXHasUsage AKEM.extractKemSk pk skUsg tr

public
theorem Bytes.KemSkHasUsage_eq_XXXHasUsage
  [BytesInvariants]
  (pk: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : Bytes.KemSkHasUsage pk skUsg tr = Bytes.XXXHasUsage AKEM.extractKemSk pk skUsg tr
:= rfl

public
theorem Bytes.KemSkHasUsage_kemPk
  [BytesInvariants]
  (sk: Bytes) (skUsg: Usage) (tr: ProofTrace)
  : (AKEM.kemPk sk).KemSkHasUsage skUsg tr = sk.HasUsage skUsg tr
:= by
  simp [Bytes.KemSkHasUsage, Bytes.XXXHasUsage, AKEM.extractKemSk, AKEM.kemPk]
  grind

grind_pattern Bytes.KemSkHasUsage_kemPk => (AKEM.kemPk sk).KemSkHasUsage skUsg tr

public
theorem Bytes.KemSkHasUsage_later
  [BytesInvariants]
  [BytesInvariants.Has AKEM.Pk.invariants]
  [GetUsageLater] [GetLabelLater]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.KemSkHasUsage usg tr1 →
    b.KemSkHasUsage usg tr2
:= by
  simp [Bytes.KemSkHasUsage]
  apply Bytes.XXXHasUsage_later AKEM.extractKemSk AKEM.extractKemSk.preserves_WellFormed

grind_pattern Bytes.KemSkHasUsage_later => tr1 ≤ tr2, b.KemSkHasUsage usg tr1

public
theorem Bytes.KemSkHasUsage_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has AKEM.Pk.invariants]
  (b: Bytes) (usg: Usage) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.KemSkHasUsage usg tr1 →
    b.KemSkHasUsage usg tr2
:= by grind

grind_pattern [grind_later] Bytes.KemSkHasUsage_later_fast => tr1 ≤ tr2, b.KemSkHasUsage usg tr1

public
noncomputable
def Bytes.kemSkLabel
  [GetLabel]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel AKEM.extractKemSk pk tr

public
theorem Bytes.kemSkLabel_kemPk
  [BytesInvariants]
  [BytesInvariants.Has AKEM.Pk.invariants]
  (sk: Bytes) (tr: ProofTrace)
  : (AKEM.kemPk sk).kemSkLabel tr = sk.label tr
:= by
  simp [Bytes.kemSkLabel, Bytes.xxxLabel, AKEM.extractKemSk, AKEM.kemPk]
  grind

grind_pattern Bytes.kemSkLabel_kemPk => (AKEM.kemPk sk).kemSkLabel tr

public
theorem Bytes.kemSkLabel_later
  [BytesInvariants]
  [BytesInvariants.Has AKEM.Pk.invariants]
  [GetLabelLater]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.kemSkLabel tr1 = b.kemSkLabel tr2
:= by
  simp [Bytes.kemSkLabel]
  apply Bytes.xxxLabel_later AKEM.extractKemSk AKEM.extractKemSk.preserves_WellFormed

grind_pattern Bytes.kemSkLabel_later => tr1 ≤ tr2, b.kemSkLabel tr1

public
theorem Bytes.kemSkLabel_later_fast
  [BytesInvariants] [BytesInvariantsProofs]
  [BytesInvariants.Has AKEM.Pk.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  : b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.kemSkLabel tr1 = b.kemSkLabel tr2
:= by grind

grind_pattern [grind_later] Bytes.kemSkLabel_later_fast => tr1 ≤ tr2, b.kemSkLabel tr1

end ExtractKemPk

namespace AKEM

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has AKEM.SubF]

public
def Encap.invariants: Bytes.PartialInvariants Encap.SubF where
  well_formed := fun {pkR, skS, entropy} rec tr =>
      (rec pkR) tr ∧
      (rec skS) tr ∧
      (rec entropy) tr

  usage := fun {pkR, skS, entropy} rec tr =>
    Usage.nothing

  label := fun {pkR, skS, entropy} rec tr =>
    Label.pub

  invariant := fun {pkR, skS, entropy} rec tr =>
      (rec pkR) tr ∧
      (rec skS) tr ∧
      (rec entropy) tr ∧
      (entropy.label tr).canFlow (pkR.kemSkLabel tr) tr.erase ∧
      ( (skS.label tr).canFlow Label.pub tr.erase
        ∨ (pkR.kemSkLabel tr).canFlow (entropy.label tr) tr.erase )

public
def Encap.invariantsProofs [BytesInvariants] [BytesInvariants.Has Pk.invariants] : Bytes.PartialInvariantsProofs Encap.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind [Bytes.kemSkLabel_later, Bytes.kemSkLabel]

public
def SharedSecret.invariants: Bytes.PartialInvariants SharedSecret.SubF where
  well_formed := fun {pkR, skS, entropy} rec tr =>
    (rec pkR) tr ∧
    (rec skS) tr ∧
    (rec entropy) tr

  -- Inherit the entropy's usage, mirroring the `label` rule below.
  --
  -- NOTE: this is deliberately *not* the rule used by the real
  -- `AKEM.SharedSecret.invariants` in `Crypto/KEM/Symbolic.lean`, which mints
  -- the established secret's usage through a protocol-supplied
  -- `AKEM.UsageConfig`. This equational-theory model has no protocol attached
  -- and no receive-side naming obligation, so the simpler inherited rule is
  -- adequate here. Do not copy it into a protocol.
  usage := fun {pkR := _, skS := _, entropy} rec tr =>
    (rec entropy) tr

  label := fun {pkR, skS, entropy} rec tr =>
    (rec entropy) tr

  invariant := fun {pkR, skS, entropy} rec tr =>
    (rec pkR) tr ∧
    (rec skS) tr ∧
    (rec entropy) tr ∧
    ( (skS.label tr).canFlow Label.pub tr.erase
      ∨ (pkR.kemSkLabel tr).canFlow (entropy.label tr) tr.erase )

public
def SharedSecret.invariantsProofs [BytesInvariants] [BytesInvariants.Has Pk.invariants] : Bytes.PartialInvariantsProofs SharedSecret.invariants where
  invariant_later := by
    intro _ _ _ _ x rec tr1 tr2
    cases x
    simp_all [invariants, DY.ALaCarte.FunctorSizeOf.sizeOf, BytesInvariantLaterT]
    grind [Bytes.kemSkLabel_later, Bytes.kemSkLabel]

#combine [BytesFunctor.Has SubF] into
  BytesInvariants,
  BytesInvariantsProofs [BytesInvariants.Has Pk.invariants]
from
  Pk,
  Encap,
  SharedSecret,

section EncapLemmas

variable [BytesInvariants] [BytesInvariants.Has AKEM.invariants]

public
theorem kemEncap.WellFormed
  (pkR skS entropy: Bytes) (tr: ProofTrace)
  : let (cipher, ss) := kemEncap pkR skS entropy
    cipher.WellFormed tr = (pkR.WellFormed tr ∧ skS.WellFormed tr ∧ entropy.WellFormed tr) ∧
    ss.WellFormed tr = (pkR.WellFormed tr ∧ skS.WellFormed tr ∧ entropy.WellFormed tr)
:= by
  simp [kemEncap, Bytes.WellFormed.eq, Encap.invariants, SharedSecret.invariants]

public
theorem kemEncap.ss_label
  (pkR skS entropy: Bytes) (tr: ProofTrace)
  : let (_, ss) := kemEncap pkR skS entropy
    ss.label tr = entropy.label tr
:= by
  simp [kemEncap, SharedSecret.invariants]

public
theorem SharedSecret.label_pack
  (pkR skS entropy: Bytes) (tr: ProofTrace)
  : (({ pkR := pkR, skS := skS, entropy := entropy } : SharedSecret.SubF Bytes).pack).label tr
      = entropy.label tr
:= by
  simp [Bytes.label.eq, SharedSecret.invariants]

public
theorem SharedSecret.WellFormed_pack
  (pkR skS entropy: Bytes) (tr: ProofTrace)
  : (({ pkR := pkR, skS := skS, entropy := entropy } : SharedSecret.SubF Bytes).pack).WellFormed tr
      = ( pkR.WellFormed tr ∧ skS.WellFormed tr ∧ entropy.WellFormed tr )
:= by
  simp [Bytes.WellFormed.eq, SharedSecret.invariants]

public
theorem SharedSecret.Invariant_pack
  (pkR skS entropy: Bytes) (tr: ProofTrace)
  : (({ pkR := pkR, skS := skS, entropy := entropy } : SharedSecret.SubF Bytes).pack).Invariant tr
      = ( pkR.Invariant tr ∧
          skS.Invariant tr ∧
          entropy.Invariant tr ∧
          ( (skS.label tr).canFlow Label.pub tr.erase
            ∨ (pkR.kemSkLabel tr).canFlow (entropy.label tr) tr.erase ) )
:= by
  simp [Bytes.Invariant.eq, SharedSecret.invariants]

end EncapLemmas

section DecapLemmas

variable [BytesInvariants] [BytesInvariants.Has AKEM.invariants]

omit [ExecTraceTypes] [ProofTraceTypes] [BytesInvariants] [BytesInvariants.Has invariants] in
public
theorem kemDecap.WellFormed
  (skR pkS cipher: Bytes)
  : match kemDecap skR pkS cipher with
    | none => True
    | some _ => True
:= by
  unfold kemDecap
  split <;> trivial

end DecapLemmas

end Invariants

section HoareTriples

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has AKEM.SubF]
variable [BytesInvariants] [BytesInvariants.Has AKEM.invariants]

public
instance kemPk_hoareTriple
  (sk: Bytes)
  : HoareTriplePure
    (kemPk sk)
    (fun tr =>
      sk.Invariant tr
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
where
  pf := by
    grind [kemPk.Invariant, kemPk.label]

public
instance kemEncap_hoareTriple
  (pkR skS entropy: Bytes)
  : HoareTriplePure
    (kemEncap pkR skS entropy)
    (fun tr =>
      pkR.Invariant tr ∧
      skS.Invariant tr ∧
      entropy.Invariant tr ∧
      entropy.label tr = pkR.kemSkLabel tr
    )
    (fun (cipher, ss) tr =>
      cipher.Publishable tr ∧
      ss.Invariant tr ∧
      ss.label tr = entropy.label tr
      -- TODO usage
    )
where
  pf := by
    simp [kemEncap, Bytes.Publishable, Bytes.Invariant.eq, Encap.invariants, SharedSecret.invariants]
    grind [canFlowRefl]


public
instance kemDecap_hoareTriple
  [TraceInvariant]
  (skR pkS cipher: Bytes)
  : HoareTriple
    (kemDecap skR pkS cipher)
    (fun tr =>
      skR.Invariant tr ∧
      pkS.Invariant tr ∧
      cipher.Invariant tr
      -- sk usage
    )
    (fun ss tr =>
      kemDecap skR pkS cipher = some ss ∧
      ss.Invariant tr ∧
      (ss.label tr).canFlow (skR.label tr) tr.erase
      -- TODO usage
    )
where
  pf := by
    simp only [hoareTriple, wp, OptionT.run, kemDecap]
    intro tr h_pre h_inv
    split
    · grind
    rename_i ss heq
    split at heq
    · rename_i pkR skS' entropy _
      split at heq
      · have := Bytes.pack_view? Encap.SubF cipher
        have := Bytes.kemSkLabel_kemPk skR tr
        simp only [kemPk] at this
        simp_all only
        subst_eqs
        simp_all [Encap.invariants, SharedSecret.invariants]
      · grind
    · grind

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has AKEM.SubF]
variable [BytesInvariants.Has AKEM.invariants]

-- Preserve publishability

public
instance : SubAttackerKnowledgeTheorem kemPk.attackerKnowledge where
  pf := by
    simp only [kemPk.attackerKnowledge]
    intro out tr h_tr ⟨sk, h_out, h_sk⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind [kemPk.Invariant, canFlowTrans]

public
instance : SubAttackerKnowledgeTheorem kemEncapCipher.attackerKnowledge where
  pf := by
    simp only [kemEncapCipher.attackerKnowledge]
    intro out tr h_tr ⟨pkR, skS, entropy, rhs, h_out, h_inputs⟩
    simp_all [kemEncap, Bytes.Publishable, Bytes.Invariant.eq, Encap.invariants]
    grind [canFlowTrans]

public
instance : SubAttackerKnowledgeTheorem kemEncapSS.attackerKnowledge where
  pf := by
    simp only [kemEncapSS.attackerKnowledge]
    intro out tr h_tr ⟨pkR, skS, entropy, lhs, h_out, h_inputs⟩
    simp_all [kemEncap, Bytes.Publishable, Bytes.Invariant.eq, SharedSecret.invariants]

public
instance : SubAttackerKnowledgeTheorem kemDecap.attackerKnowledge where
  pf := by
    simp only [kemDecap.attackerKnowledge]
    intro out tr h_tr ⟨skR, pkS, cipher, h_out, h_inputs⟩
    have := (kemDecap_hoareTriple skR pkS cipher).pf
    simp only [hoareTriple, wp, OptionT.run, ← h_out] at this
    grind [canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  kemPk,
  kemEncapCipher,
  kemEncapSS,
  kemDecap,

end AttackerKnowledgeTheorem

end DY.AKEM
