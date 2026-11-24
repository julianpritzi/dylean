module

import DY.Meta
import DY.Meta.Utils
public import Examples.HPKE.Specification
public import Examples.HPKE.Proof
import all Examples.HPKE.Proof
public import Examples.HPKE.Instance

namespace DY.Example.HPKE

/--
Plaintext secrecy theorem for authenticated HPKE in this symbolic model.

If the attacker knows `pt` of a logged `SealEvent sender recipient enc sharedSecret pt` at index `time`,
then either some sender key or some recipient key is compromised.

Intuition: `pt` remains confidential; attacker knowledge of
the sealed plaintext is only possible if a relevant long-term secret has leaked.
-/
public
theorem pt_secrecy
  (sender recipient: Participant) (enc sharedSecret pt: Bytes) (time: Nat) :
  ∀ tr: ExecTrace,
    tr.Reachable reachability →
    pt.AttackerKnows tr →
    tr.EventLoggedAt (HPKEAuthEvent.SealEvent sender recipient enc sharedSecret pt) time →
    (
      let tr_before := tr.prefix time
      (∃ spk, LongTermKeys.LongTermKeyCompromised "HPKE Auth PKI" sender spk tr_before) ∨
      (∃ rpk, LongTermKeys.LongTermKeyCompromised "HPKE Auth PKI" recipient rpk tr)
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_pub h_ev
  have h_pub_pt : pt.Publishable tr := Bytes.AttackerKnows_implies_Publishable pt tr h_trinv h_pub
  simp [Bytes.Publishable] at h_pub_pt
  have hInv :
      HPKEAuthEventInv.invariant (tr.prefix time) (HPKEAuthEvent.SealEvent sender recipient enc sharedSecret pt) :=
    Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  cases hInv with
  | intro h_ss_inv hInv =>
    cases hInv with
    | intro h_pt_inv_prefix hInv =>
      cases hInv with
      | intro h_pt_flow h_ltk_pt_prefix_exists =>
        rcases h_ltk_pt_prefix_exists with ⟨rpk, h_ltk_pt_prefix⟩
        have h_pt_wf_prefix : pt.WellFormed (tr.prefix time) :=
          Bytes.Invariant_implies_WellFormed pt (tr.prefix time) h_pt_inv_prefix
        have h_pt_lbl_eq : pt.label (tr.prefix time) = pt.label tr :=
          Bytes.label_later pt (tr.prefix time) tr (Trace.prefix_le_self tr time) h_pt_wf_prefix
        have h_ltk_pt_current' :
            (LongTermKeys.label "HPKE Auth PKI" recipient rpk).canFlow (pt.label (tr.prefix time)) (Trace.erase tr) :=
          by
            have h_ltk_pt_prefix' :
                (LongTermKeys.label "HPKE Auth PKI" recipient rpk).canFlow (pt.label (tr.prefix time)) (Trace.prefix (Trace.erase tr) time) := by
              simpa [Trace.prefix_erase] using h_ltk_pt_prefix
            exact Label.canFlowLater (LongTermKeys.label "HPKE Auth PKI" recipient rpk) (pt.label (tr.prefix time))
              (Trace.prefix (Trace.erase tr) time) (Trace.erase tr)
              (Trace.prefix_le_self (Trace.erase tr) time)
              h_ltk_pt_prefix'
        have h_ltk_pt_current :
            (LongTermKeys.label "HPKE Auth PKI" recipient rpk).canFlow (pt.label tr) (Trace.erase tr) := by
          simpa [h_pt_lbl_eq] using h_ltk_pt_current'
        have h_pt_pub : (pt.label tr).canFlow Label.pub (Trace.erase tr) := h_pub_pt.2
        have h_ltk_pub :
            (LongTermKeys.label "HPKE Auth PKI" recipient rpk).canFlow Label.pub (Trace.erase tr) :=
          canFlowTrans (LongTermKeys.label "HPKE Auth PKI" recipient rpk) (pt.label tr) Label.pub (Trace.erase tr)
            h_ltk_pt_current h_pt_pub
        have h_ltk_corrupt :
            (LongTermKeys.label "HPKE Auth PKI" recipient rpk).isCorrupt (Trace.erase tr) := by
          simpa [canFlowPubEqIsCorrupt] using h_ltk_pub
        right
        exact ⟨rpk, by simpa [LongTermKeys.label] using h_ltk_corrupt⟩

/--
Sender authentication theorem for HPKE open events.

If an `OpenEvent recipient sender enc sharedSecret pt` is logged at time `time`, then either
a matching `SealEvent sender recipient enc sharedSecret pt` was logged, or
a sender long-term key was compromised, or the recipient's own long-term key was
compromised.

The recipient-compromise disjunct is unavoidable: HPKE's authenticated mode only
provides *outsider* sender authentication. A party holding the recipient's secret
key can recompute the authenticated shared secret (it depends on
`DH(skR, pkS)`, computable from the recipient secret and the *public* sender key)
and thus forge a ciphertext that opens as if it came from the honest sender.
-/
public
theorem sender_auth
  (recipient sender: Participant) (enc sharedSecret pt: Bytes) (time: Nat) :
  ∀ tr: ExecTrace,
    tr.Reachable reachability →
    tr.EventLoggedAt (HPKEAuthEvent.OpenEvent recipient sender enc sharedSecret pt) time →
    (
      let tr_before := tr.prefix time
      tr_before.EventLogged (HPKEAuthEvent.SealEvent sender recipient enc sharedSecret pt) ∨
      (∃ spk, LongTermKeys.LongTermKeyCompromised "HPKE Auth PKI" sender spk tr_before) ∨
      (∃ rpk, LongTermKeys.LongTermKeyCompromised "HPKE Auth PKI" recipient rpk tr_before)
    )
:= by
  apply Trace.apply_Reachable_implies_Invariant
  intro tr h_trinv h_ev
  have := Trace.EventLoggedAt_imp_EventInv _ _ _ h_trinv h_ev
  simp [ProtocolEvent.EventInv.invariant] at this
  grind

end DY.Example.HPKE
