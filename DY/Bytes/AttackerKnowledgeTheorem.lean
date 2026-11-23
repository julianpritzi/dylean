/-
  This module allows to modularly prove the attacker knowledge theorem:
  this is a key theorem in the DyLean methodology,
  saying for traces that satisfy the trace invariant,
  if the attacker knows a `Bytes`,
  then this `Bytes` must be publishable.
-/

module

public import DY.Bytes.Basic
public import DY.Bytes.Invariants
public import DY.Bytes.AttackerKnowledge
import all DY.Bytes.AttackerKnowledge
public import DY.Trace
public meta import DY.Meta.CombineMacro

namespace DY

variable [BytesFunctor]
variable [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
variable [BytesInvariants]

public
class SubAttackerKnowledgeTheorem {SubF: Type → Type} (att: SubAttackerKnowledge SubF) where
  pf: ∀ b: Bytes, ∀ tr: ProofTrace, tr.Invariant → att.pred (·.Publishable tr) b → b.Publishable tr

public
class AttackerKnowledgeTheorem [AttackerKnowledge] where
  inst: SubAttackerKnowledgeTheorem (AttackerKnowledge.attackerKnowledge)

section AttackerKnowledgeTheorem

public
instance
  {SubF: Type → Type}
  {t: Type}
  (atts: t → SubAttackerKnowledge SubF)
  [pfs: ∀ id, SubAttackerKnowledgeTheorem (atts id)]
  : SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine' atts)
where
  pf := by
    intro b tr h_tr
    apply SubAttackerKnowledge.combine'.implies
    intro id b
    exact (pfs id).pf b tr h_tr

public
instance
  {t: Type}
  {SubFs: t → Type → Type}
  (atts: ∀ id, SubAttackerKnowledge (SubFs id))
  [pfs: ∀ id, SubAttackerKnowledgeTheorem (atts id)]
  : SubAttackerKnowledgeTheorem (SubAttackerKnowledge.combine atts)
where
  pf := by
    intro b tr h_tr
    apply SubAttackerKnowledge.combine.implies
    intro id b
    exact (pfs id).pf b tr h_tr

end AttackerKnowledgeTheorem

public
theorem Bytes.AttackerKnows_implies_Publishable
  [BytesInvariantsProofs]
  [AttackerKnowledge] [BaseAttackerKnowledge]
  [inst: AttackerKnowledgeTheorem]
  [BaseAttackerKnowledgeTheorem]
  (b: Bytes) (tr: ProofTrace)
  : tr.Invariant →
    Bytes.AttackerKnows b tr.erase →
    b.Publishable tr
:= by
  intro h_tr
  apply Bytes.AttackerKnows.is_least_fixpoint (·.Publishable tr) b tr.erase
  · intro b
    exact inst.inst.pf b tr h_tr
  · intro b
    simp only [AttackerKnows.baseKnowledge, SubAttackerKnowledge.fromPred]
    apply Trace.BaseAttackerKnows_implies_Publishable
    assumption

grind_pattern Bytes.AttackerKnows_implies_Publishable => Bytes.AttackerKnows b tr.erase

/-! ### The secrecy corollary

Standalone secrecy theorems all run the same five-step argument: attacker
knowledge of a value gives publishability, publishability gives
`value-label ⤳ pub`, the event invariant gives a *floor* `floor ⤳ value-label`
at the logging point, the floor is transported forward across the trace, and
transitivity concludes `floor ⤳ pub` — i.e. the floor label is corrupt.

`floor_of_AttackerKnows` packages exactly that. It is generic in the floor, the
value and the trace, and mentions no protocol content, so a protocol supplies
only the fact its own event invariant already gives it.

This is **optional**. A protocol whose secrecy clause has a different shape (a
label *equality* rather than a `canFlow` floor, say) states its own argument;
nothing here forces the floor form. -/

public
theorem Label.corrupt_of_floor_of_AttackerKnows
  [BytesInvariantsProofs]
  [AttackerKnowledge] [BaseAttackerKnowledge]
  [AttackerKnowledgeTheorem] [BaseAttackerKnowledgeTheorem]
  (floor : Label) (b : Bytes) (trPre tr : ProofTrace)
  : tr.Invariant →
    trPre ≤ tr →
    -- what the event invariant gives at the logging point:
    b.Invariant trPre →
    floor.canFlow (b.label trPre) trPre.erase →
    -- what the theorem's hypothesis gives:
    Bytes.AttackerKnows b tr.erase →
    floor.isCorrupt tr.erase
:= by
  intro h_trinv h_le h_b_inv h_floor h_knows
  -- attacker knowledge ⇒ publishable ⇒ `b.label tr ⤳ pub`
  have h_pub : b.Publishable tr :=
    Bytes.AttackerKnows_implies_Publishable b tr h_trinv h_knows
  have h_b_pub : (b.label tr).canFlow Label.pub tr.erase := h_pub.2
  -- the value's label is stable across the extension (it was `Invariant` early)
  have h_lbl : b.label trPre = b.label tr :=
    Bytes.label_later_fast b trPre tr h_le h_b_inv
  -- transport the floor flow forward, then compose with publishability
  have h_floor_now : floor.canFlow (b.label tr) tr.erase := by
    rw [← h_lbl]
    exact Label.canFlowLater floor (b.label trPre) trPre.erase tr.erase
      (Trace.erase_le trPre tr h_le) h_floor
  have : floor.canFlow Label.pub tr.erase :=
    canFlowTrans floor (b.label tr) Label.pub tr.erase h_floor_now h_b_pub
  simpa [canFlowPubEqIsCorrupt] using this

namespace Meta.CombineMacro

macro_rules
  | `(command| #combine_one $options* SubAttackerKnowledgeTheorem $params* from $sources,*) => do
    let options := parseOptions options
    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.BytesFunctor])),
      (← `(bracketedBinder| [DY.ExecTraceTypes])),
      (← `(bracketedBinder| [DY.ProofTraceTypes])),
      (← `(bracketedBinder| [DY.TraceInvariant])),
      (← `(bracketedBinder| [DY.BytesInvariants])),
    ]
    let params := if options.toplevel then params else baseGlobalInstances ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources <| .makeSimple {
      refereeName := `attackerKnowledge
      combineName := ``DY.SubAttackerKnowledge.combine
      outTypeName := ``DY.SubAttackerKnowledgeTheorem
    }

    let attStx := Lean.mkIdent `attackerKnowledge
    let topLevelInst ← `(command| public instance: DY.AttackerKnowledgeTheorem where inst := inferInstanceAs (DY.SubAttackerKnowledgeTheorem $attStx))
    let topLevel := if options.toplevel then #[topLevelInst] else #[]

    return Lean.mkNullNode (combined ++ topLevel)

macro_rules
  | `(command| #combine_one $_options* SubAttackerKnowledgeTheorem' $params* from $sources,*) => do
    -- options.toplevel does not make sense in this case, hence we ignore it
    let baseGlobalInstances := #[
      (← `(bracketedBinder| [DY.BytesFunctor])),
      (← `(bracketedBinder| [DY.ExecTraceTypes])),
      (← `(bracketedBinder| [DY.ProofTraceTypes])),
      (← `(bracketedBinder| [DY.TraceInvariant])),
      (← `(bracketedBinder| [DY.BytesInvariants])),
    ]
    let params := baseGlobalInstances ++ params
    let sources := sources.getElems

    let combined ← combineTypeclass params sources <| .makeSimple {
      refereeName := `attackerKnowledge
      combineName := ``DY.SubAttackerKnowledge.combine'
      outTypeName := ``DY.SubAttackerKnowledgeTheorem
    }

    return Lean.mkNullNode (combined)

end Meta.CombineMacro

end DY
