module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.Concat

public
class CanConcat (Bytes: Type u) where
  concat: Bytes → Bytes → Bytes
  split: Bytes → Nat → Option (Bytes × Bytes)

export CanConcat (concat)
export CanConcat (split)

section Constructors

namespace Concat

public
structure SubF (Bytes: Type) where
  lhs: Bytes
  rhs: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {lhs, rhs} => sizeOf lhs + sizeOf rhs

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {lhs, rhs} => {
    id := ()
    data := ()
    as := #v[lhs, rhs]
  }
  fromRepr
  | {id, data, as} =>
    let lhs := as[0]
    let rhs := as[1]
    { lhs, rhs }
  from_to | {lhs, rhs} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {lhs, rhs} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { lhs, rhs } rec =>
    rec lhs + rec rhs

end Concat

#combine into BytesFunctor, BytesLength from
  Concat,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesLength]

public
abbrev Concat.SubF.pack (x: Concat.SubF Bytes) := BytesView.pack x

public
instance: CanConcat Bytes where
  concat lhs rhs := ({lhs, rhs}: Concat.SubF Bytes).pack

  split buf i :=
    match buf.view? Concat.SubF with
    | some ({ lhs, rhs }) =>
      if lhs.length = i then
        some (lhs, rhs)
      else
        none
    | none => none

public
theorem split_concat
  (lhs rhs: Bytes)
  : split (concat lhs rhs) (lhs.length) = some (lhs, rhs)
:= by
  simp only [split, concat]
  grind

public
theorem concat_split
  (buf: Bytes) (i: Nat) (lhs rhs: Bytes)
  : split buf i = some (lhs, rhs) → concat lhs rhs = buf
:= by
  simp only [concat, split]
  grind

/-- Index-free top-level destructor: recover a `concat`'s two operands without
    knowing where the boundary lies. `split` requires the left operand's length,
    which a caller inspecting an otherwise-opaque term does not have. This is
    what a usage rule peeling a *labelled* ikm needs -- see
    `Crypto.KDF.UsageConfig.ikmNaming`, where a protocol reads the usage of a
    sub-term of its own key-schedule input. Returns `none` on any term that is
    not a `concat`. -/
public
def unconcat? (b: Bytes) : Option (Bytes × Bytes) :=
  match b.view? Concat.SubF with
  | some ({ lhs, rhs }) => some (lhs, rhs)
  | none => none

public
theorem unconcat?_concat (lhs rhs: Bytes)
  : unconcat? (concat lhs rhs) = some (lhs, rhs)
:= by
  simp only [unconcat?, concat]
  grind

/-- `unconcat?` bottoms out on any term that does not view as a `concat`. The
    hypothesis is normally supplied by `BytesView.view_pack_ne`, which is how a
    deployment shows that (say) a string literal is not a concatenation. -/
public
theorem unconcat?_of_view?_none (b: Bytes) (h: b.view? Concat.SubF = none)
  : unconcat? b = none
:= by
  simp only [unconcat?, h]

public
theorem concat_unconcat? (b lhs rhs: Bytes)
  : unconcat? b = some (lhs, rhs) → concat lhs rhs = b
:= by
  simp only [unconcat?, concat]
  grind

/-- `concat` is injective in both operands, since `unconcat?` recovers them.
    A term that is a `concat` therefore has exactly ONE top-level split, which is
    what lets a property stated over *all* splits of a buffer be discharged from
    the one split its builder used. -/
public
theorem concat_inj {lhs rhs lhs' rhs': Bytes}
  (h: concat lhs rhs = concat lhs' rhs')
  : lhs = lhs' ∧ rhs = rhs'
:= by
  have h1 := unconcat?_concat lhs rhs
  rw [h, unconcat?_concat] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- The operands of a `concat` are genuine sub-terms, so a selector built from
    `unconcat?` satisfies `UsageConfig.ikmNaming_size`. -/
public
theorem sizeOf_concat (lhs rhs: Bytes)
  : sizeOf lhs + sizeOf rhs ≤ sizeOf (concat lhs rhs)
:= by
  have h := Bytes.sizeOf_view Concat.SubF (concat lhs rhs)
  rw [show (concat lhs rhs).view? Concat.SubF = some ({lhs, rhs}: Concat.SubF Bytes) from
    BytesView.view_pack _] at h
  simpa [ALaCarte.FunctorSizeOf.sizeOf] using h

public
theorem sizeOf_unconcat? (b lhs rhs: Bytes)
  : unconcat? b = some (lhs, rhs) → sizeOf lhs + sizeOf rhs ≤ sizeOf b
:= by
  intro h
  rw [← concat_unconcat? b lhs rhs h]
  exact sizeOf_concat lhs rhs

/-- Peel one `concat` layer, keeping the right operand (the payload). This is
    the single step a labelled-KDF naming rule iterates -- see
    `Crypto.KDF.UsageConfig.ikmNaming`. It is total: a term that is not a
    `concat` is returned unchanged, so no rule built from it can fail. -/
public
def unconcatR (b: Bytes) : Bytes :=
  match unconcat? b with
  | some (_, r) => r
  | none => b

@[simp]
public
theorem unconcatR_concat (lhs rhs: Bytes)
  : unconcatR (concat lhs rhs) = rhs
:= by
  simp only [unconcatR, unconcat?_concat]

/-- The other half of `unconcatR`'s totality: a term that is not a `concat` is
    returned unchanged. A naming rule that peels a fixed number of layers needs
    this to argue that a protocol passing an *unwrapped* keying material through
    the same `ikmNaming` selector still names itself. -/
public
theorem unconcatR_of_unconcat?_none (b: Bytes) (h: unconcat? b = none)
  : unconcatR b = b
:= by
  simp only [unconcatR, h]

public
theorem sizeOf_unconcatR (b: Bytes)
  : sizeOf (unconcatR b) ≤ sizeOf b
:= by
  unfold unconcatR
  split
  · next l r hv =>
    have := sizeOf_unconcat? b l r hv
    omega
  · exact Nat.le_refl _

@[simp]
public
theorem length_concat
  [BytesLength.Has SubF.length]
  (lhs rhs: Bytes)
  : Bytes.length (concat lhs rhs) = Bytes.length lhs + Bytes.length rhs
:= by
  simp only [concat]
  grind [Concat.SubF.length]

@[simp]
public
theorem length_split
  [BytesLength.Has SubF.length]
  (buf: Bytes) (i: Nat) (lhs rhs: Bytes)
  : split buf i = some (lhs, rhs) →
    (Bytes.length lhs = i ∧ i+Bytes.length rhs = Bytes.length buf)
:= by
  simp only [split]
  grind [Concat.SubF.length]

end Constructors

section AttackerKnowledge

public
def concat.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ lhs rhs,
      out = concat lhs rhs ∧
      p lhs ∧
      p rhs

public
def splitLeft.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ inp rhs i,
      some (out, rhs) = split inp i ∧
      p inp

public
def splitRight.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ inp lhs i,
      some (lhs, out) = split inp i ∧
      p inp

#combine [BytesFunctor.Has SubF] [BytesLength] into attackerKnowledge' from
  concat,
  splitLeft,
  splitRight


variable [BytesFunctor] [BytesFunctor.Has SubF] [BytesLength]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_concat
  (lhs rhs: Bytes) (tr: ExecTrace)
  : lhs.AttackerKnows tr →
    rhs.AttackerKnows tr →
    (concat lhs rhs).AttackerKnows tr
:= by
  intro h_lhs h_rhs
  apply Bytes.AttackerKnows.prove concat.attackerKnowledge
  simp only [concat.attackerKnowledge]
  grind

public
theorem attacker_knows_split
  (buf: Bytes) (i: Nat) (tr: ExecTrace)
  : buf.AttackerKnows tr →
    match split buf i with
    | none => True
    | some (lhs, rhs) =>
      lhs.AttackerKnows tr ∧
      rhs.AttackerKnows tr
:= by
  intro h_buf
  split
  · grind
  rename_i lhs rhs _
  constructor
  · apply Bytes.AttackerKnows.prove splitLeft.attackerKnowledge
    simp only [splitLeft.attackerKnowledge]
    grind
  · apply Bytes.AttackerKnows.prove splitRight.attackerKnowledge
    simp only [splitRight.attackerKnowledge]
    grind

end AttackerKnowledge

section Invariants

section Definition

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor]

public
def Concat.invariants: Bytes.PartialInvariants Concat.SubF where
  well_formed := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

  usage := fun {lhs, rhs} rec tr => Usage.nothing

  label := fun {lhs, rhs} rec tr =>
    Label.meet ((rec lhs) tr) ((rec rhs) tr)

  invariant := fun {lhs, rhs} rec tr =>
    (rec lhs) tr ∧ (rec rhs) tr

public
theorem Concat.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Concat.invariants where

end Definition

#combine into
  BytesInvariants,
  BytesInvariantsProofs
from
  Concat,


variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [BytesLength]

@[simp]
public
theorem concat.WellFormed
  [BytesWellFormed] [BytesWellFormed.Has Concat.invariants.well_formed]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
:= by
  simp [concat, Bytes.WellFormed.eq, Concat.invariants]

/-- Well-formedness descends through a peel. This is what a naming rule needs in
    order to take the *usage* of a peeled sub-term: `usage_later` may only appeal
    to the structural recursor at sub-terms that are well-formed at the earlier
    trace (see `Crypto.KDF.UsageConfigProof.ikmNaming_wf`). -/
public
theorem unconcatR.WellFormed
  [BytesWellFormed] [BytesWellFormed.Has Concat.invariants.well_formed]
  (b: Bytes) (tr: ProofTrace)
  : b.WellFormed tr → (unconcatR b).WellFormed tr
:= by
  intro h
  unfold unconcatR
  split
  · next l r hv =>
    rw [← concat_unconcat? b l r hv, concat.WellFormed] at h
    exact h.2
  · exact h

@[simp]
public
theorem concat.label
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).label tr = Label.meet (lhs.label tr) (rhs.label tr)
:= by
  simp [concat, Bytes.label.eq, Concat.invariants]

/-- Concatenation carries **no** usage: a `concat` term is never a named key.

    This is the accessor form of `Concat.invariants.usage`, and it is worth
    stating explicitly because it is a real constraint on protocol usage rules,
    not a triviality. Any rule that tries to read a name out of a *labeled*
    construction — RFC 9180's `LabeledExtract(salt, label, ikm)`, whose `ikm`
    argument is `concat("HPKE-v1", suite_id, label, ikm)` — reads this
    `Usage.nothing` instead of the underlying secret's usage. A naming chain
    that has to pass through a `concat` is therefore severed here, silently,
    with no proof failing. -/
@[simp]
public
theorem concat.usage
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).usage tr = Usage.nothing
:= by
  simp [concat, Bytes.usage.eq, Concat.invariants]

@[simp]
public
theorem concat.Invariant
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lhs rhs: Bytes) (tr: ProofTrace)
  : (concat lhs rhs).Invariant tr = (lhs.Invariant tr ∧ rhs.Invariant tr)
:= by
  simp [concat, Bytes.Invariant.eq, Concat.invariants]

@[simp]
public
theorem split.WellFormed
  [BytesWellFormed] [BytesWellFormed.Has Concat.invariants.well_formed]
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : match split buf i with
    | none => True
    | some (lhs, rhs) =>
      buf.WellFormed tr = (lhs.WellFormed tr ∧ rhs.WellFormed tr)
:= by
  split
  · grind
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq]
  simp

@[simp]
public
theorem split.label
  [BytesInvariants] [BytesInvariants.Has invariants]
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : match split buf i with
    | none => True
    | some (lhs, rhs) =>
      buf.label tr = Label.meet (lhs.label tr) (rhs.label tr)
:= by
  split
  · grind
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq]
  simp

@[simp]
public
theorem split.Invariant
  [BytesInvariants] [BytesInvariants.Has invariants]
  (buf: Bytes) (i: Nat) (tr: ProofTrace)
  : buf.Invariant tr →
    match split buf i with
    | none => True
    | some (lhs, rhs) =>
      lhs.Invariant tr ∧ rhs.Invariant tr
:= by
  intro h_buf
  split
  · grind
  rename_i lhs rhs heq
  rewrite [← concat_split buf i lhs rhs heq] at h_buf
  simp_all

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesLength]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem concat.attackerKnowledge where
  pf := by
    simp only [concat.attackerKnowledge]
    intro out tr h_tr ⟨lhs, rhs, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

public
instance: SubAttackerKnowledgeTheorem splitLeft.attackerKnowledge where
  pf := by
    simp only [splitLeft.attackerKnowledge]
    intro out tr h_tr ⟨inp, rhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

public
instance: SubAttackerKnowledgeTheorem splitRight.attackerKnowledge where
  pf := by
    simp only [splitRight.attackerKnowledge]
    intro out tr h_tr ⟨inp, lhs, i, ⟨ h_out, h_inputs ⟩⟩
    simp [Bytes.Publishable]
    have := split.label inp i tr
    have := split.Invariant inp i tr
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesLength] [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  concat,
  splitLeft,
  splitRight,

end AttackerKnowledgeTheorem

end DY.Concat
