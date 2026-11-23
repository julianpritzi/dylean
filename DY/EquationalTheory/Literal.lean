module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances

namespace DY.Literal

public
class CanMkLiteral (Bytes: Type u) where
  literalToBytes: ByteArray → Bytes
  bytesToLiteral: Bytes → Option ByteArray

export CanMkLiteral (literalToBytes)
export CanMkLiteral (bytesToLiteral)

-- Constructors

section Constructors

namespace Literal

public
structure SubF (Bytes: Type) where
  lit: ByteArray

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {lit := _} => 0

public
instance: ALaCarte.Representable SubF where
  CtorId := Unit
  ctors | () => { Data := ByteArray, nRec := 0 }

  toRepr | {lit} => {
    id := ()
    data := lit
    as := #v[]
  }
  fromRepr
  | {id, data := lit, as} =>
    { lit }
  from_to | {lit} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {lit := _} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where

public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun { lit := lit } _ =>
    lit.size


end Literal

#combine into BytesFunctor, BytesLength from
  Literal,

public
abbrev Literal.SubF.pack [BytesFunctor] [BytesFunctor.Has SubF] (x: Literal.SubF Bytes) := BytesView.pack x

public
instance [BytesFunctor] [BytesFunctor.Has SubF]: CanMkLiteral Bytes where
  literalToBytes lit :=
    ({ lit }: Literal.SubF Bytes).pack

  bytesToLiteral buf :=
    match buf.view? Literal.SubF with
    | some { lit } =>
      some lit
    | none => none

public
theorem bytesToLiteral_literalToBytes
  [BytesFunctor] [BytesFunctor.Has SubF]
  (lit: ByteArray)
  : bytesToLiteral (literalToBytes lit: Bytes) = some lit
:= by
  simp only [bytesToLiteral, literalToBytes]
  grind

public
theorem literalToBytes_bytesToLiteral
  [BytesFunctor] [BytesFunctor.Has SubF]
  (buf: Bytes)
  : match bytesToLiteral buf with
    | none => True
    | some lit =>
      buf = literalToBytes lit
:= by
  simp only [bytesToLiteral, literalToBytes]
  grind

/-- A literal is NOT a member of any OTHER sub-functor of the byte algebra.
    A deployment needs this to argue that a fixed KDF `info` string cannot be
    parsed as a structured term, hence that a rule keyed on such a parse leaves
    the string's expansion alone. Discharge `h_ne` with
    `ALaCarte.FunctorUnion.inj_ne`. -/
public
theorem literalToBytes_view?_ne
  [BytesFunctor] [BytesFunctor.Has SubF]
  (SubF2: Type → Type) [SubBytesFunctor SubF2] [BytesFunctor.Has SubF2]
  (lit: ByteArray)
  (h_ne: ∀ (y: BytesView SubF2) (x: BytesView Literal.SubF),
    (ALaCarte.SubFunctorTC.inj (f := SubF2) (g := BytesF) y: BytesF Bytes)
      ≠ ALaCarte.SubFunctorTC.inj (f := Literal.SubF) (g := BytesF) x)
  : (literalToBytes lit: Bytes).view? SubF2 = none
:= by
  show (BytesView.pack ({ lit }: Literal.SubF Bytes)).view? SubF2 = none
  exact BytesView.view_pack_ne SubF2 _ (fun y => h_ne y _)

@[simp]
public
theorem length_literalToBytes
  [BytesFunctor] [BytesLength]
  [BytesFunctor.Has SubF] [BytesLength.Has SubF.length]
  (buf: ByteArray)
  : Bytes.length (literalToBytes buf) = buf.size
:= by
  simp only [literalToBytes]
  grind [Literal.SubF.length]

end Constructors

section AttackerKnowledge

public
def literalToBytes.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ lit,
      out = literalToBytes lit

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  literalToBytes,

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_literalToBytes
  (lit: ByteArray) (tr: ExecTrace)
  : (literalToBytes lit: Bytes).AttackerKnows tr
:= by
  apply Bytes.AttackerKnows.prove literalToBytes.attackerKnowledge
  simp only [literalToBytes.attackerKnowledge]
  exists lit

end AttackerKnowledge

section Invariants

variable [ExecTraceTypes] [ProofTraceTypes]
variable [BytesFunctor] [BytesFunctor.Has SubF]

public
def Literal.invariants: Bytes.PartialInvariants Literal.SubF where
  well_formed := fun {lit := _} _rec _tr =>
    True

  usage := fun {lit := _} _rec _tr => Usage.nothing

  label := fun {lit := _} _rec _tr =>
    Label.pub

  invariant := fun {lit := _} _rec _tr =>
    True

public
def Literal.invariantsProofs [BytesInvariants]: Bytes.PartialInvariantsProofs Literal.invariants where

#combine into
  BytesInvariants,
  BytesInvariantsProofs
from
  Literal,

@[simp]
public
theorem literalToBytes.WellFormed
  [BytesWellFormed] [BytesWellFormed.Has Literal.invariants.well_formed]
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).WellFormed tr
:= by
  simp [literalToBytes, Bytes.WellFormed.eq, Literal.invariants]

@[simp]
public
theorem literalToBytes.label
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).label tr = Label.pub
:= by
  simp [literalToBytes, Bytes.label.eq, Literal.invariants]

/-- A literal carries **no name**. Protocol key-separation arguments need this
in the negative direction: a composed deployment whose `KDF.UsageConfig` guards
on a parent's `Usage.tag` must show that a key schedule seeded from a literal
(an `Extract` under an empty or constant salt, say) cannot pick up another
protocol's tag. -/
@[simp]
public
theorem literalToBytes.usage
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).usage tr = Usage.nothing
:= by
  simp [literalToBytes, Bytes.usage.eq, Literal.invariants]

@[simp]
public
theorem literalToBytes.Invariant
  [BytesInvariants] [BytesInvariants.Has invariants]
  (lit: ByteArray) (tr: ProofTrace)
  : (literalToBytes lit: Bytes).Invariant tr
:= by
  simp [literalToBytes, Bytes.Invariant.eq, Literal.invariants]

end Invariants

section AttackerKnowledgeTheorem

variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesFunctor] [BytesInvariants]
variable [BytesFunctor.Has SubF]
variable [BytesInvariants.Has invariants]

public
instance: SubAttackerKnowledgeTheorem literalToBytes.attackerKnowledge where
  pf := by
    simp only [literalToBytes.attackerKnowledge]
    intro out tr h_tr ⟨lit, h_out⟩
    subst h_out
    simp [Bytes.Publishable]
    grind

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [BytesFunctor.Has SubF] [BytesInvariants.Has invariants] into SubAttackerKnowledgeTheorem' from
  literalToBytes,

end AttackerKnowledgeTheorem

end DY.Literal
