module

import DY.Meta.Step
import DY.Meta.Utils
public import Examples.HPKE.Specification
import all Examples.HPKE.Specification
import Examples.HPKE.EqT.AKEM

namespace DY.Example.HPKE

open DY.Comparse

public section ProofTraceConfig

class HasProofTrace extends HasExecTrace where
  [traceProof: ProofTraceTypes]
  [traceProof0: ProofTraceTypes.Has Network.ProofEntryT]
  [traceProof1: ProofTraceTypes.Has Random.ProofEntryT]
  [traceProof2: ProofTraceTypes.Has (ProtocolEvent.ProofEntryT HPKEAuthEvent)]
  [traceProof3: ProofTraceTypes.Has (LongTermKeys.ProofEntryT "HPKE Auth PKI")]

attribute [reducible, scoped instance] HasProofTrace.traceProof
attribute [reducible, scoped instance] HasProofTrace.traceProof0
attribute [reducible, scoped instance] HasProofTrace.traceProof1
attribute [reducible, scoped instance] HasProofTrace.traceProof2
attribute [reducible, scoped instance] HasProofTrace.traceProof3

end ProofTraceConfig

public section BytesInvariants

variable [HasProofTrace]

structure LongTermKeyUsage where
  principal: Participant

instance : ParseableSerializeable LongTermKeyUsage := .make <|
  .triviallyIsomorphic
    (.string)
    (fun principal => { principal })
    (fun { principal := principal } => principal)

@[grind]
def mk_long_term_usage (me: Participant): Usage := {
  type := "EncKey",
  tag := "HPKE Auth PKI",
  data := serialize ({ principal := me }: LongTermKeyUsage)
}

@[grind inj]
theorem mk_long_term_usage_inj:
  Function.Injective mk_long_term_usage
  := by
    simp [Function.Injective, mk_long_term_usage]
    grind

/--
The HPKE authentication predicate carried by every AEAD ciphertext (the AEAD
analogue of `SignedDHKEMSignPred`).
-/
instance HPKEAeadPred : DY.AEAD.AeadPred where
  pred key aad msg tr :=
    ∃ sender recipient senderSk recipientPk entropy,
      key = deriveKey (AKEM.kemEncap recipientPk senderSk entropy).2 ∧
      senderSk.HasUsage (mk_long_term_usage sender) tr ∧
      Bytes.XXXHasUsage AKEM.extractKemSk recipientPk (mk_long_term_usage recipient) tr ∧
      tr.erase.EventLogged
        (HPKEAuthEvent.SealEvent sender recipient
          (AKEM.kemEncap recipientPk senderSk entropy).1
          (AKEM.kemEncap recipientPk senderSk entropy).2
          msg)

instance
  [BytesInvariants]
  [BytesInvariants.Has Literal.invariants]
  [BytesInvariants.Has Concat.invariants]
  [BytesInvariants.Has Hash.invariants]
  [BytesInvariants.Has AKEM.invariants]
  : DY.AEAD.AeadPredProof where
  pred_later := by
    rintro _ _ _ key aad msg tr1 tr2 h_key_wf _ _ h_le
      ⟨ sender, recipient, senderSk, recipientPk, entropy, h_key, h_sUsg, h_rUsg, h_logged ⟩
    -- Recover the field well-formedness from the key's: the key is derived from the
    -- KEM shared secret, whose well-formedness decomposes into the three fields.
    have h_ss_wf : (AKEM.kemEncap recipientPk senderSk entropy).2.WellFormed tr1 := by
      rw [h_key] at h_key_wf
      simpa [deriveKey, Hash.hash.WellFormed, Concat.concat.WellFormed,
        Literal.literalToBytes.WellFormed] using h_key_wf
    simp only [AKEM.kemEncap, AKEM.SharedSecret.WellFormed_pack] at h_ss_wf
    obtain ⟨h_pkR_wf, h_skS_wf, h_entropy_wf⟩ := h_ss_wf
    refine ⟨ sender, recipient, senderSk, recipientPk, entropy, h_key, ?_, ?_, ?_ ⟩
    · exact Bytes.HasUsage_later senderSk _ tr1 tr2 h_skS_wf h_le h_sUsg
    · exact Bytes.XXXHasUsage_later AKEM.extractKemSk AKEM.extractKemSk.preserves_WellFormed
        recipientPk _ tr1 tr2 h_pkR_wf h_le h_rUsg
    · grind

end BytesInvariants

public section BytesInvariantsConfig

class HasBytesInvariants extends HasProofTrace where
  [bytesInv: BytesInvariants]
  [bytesInvProof: BytesInvariantsProofs]
  [bytesInv0: BytesInvariants.Has Random.invariants]
  [bytesInv1: BytesInvariants.Has Literal.invariants]
  [bytesInv2: BytesInvariants.Has Concat.invariants]
  [bytesInv3: BytesInvariants.Has Hash.invariants]
  [bytesInv4: BytesInvariants.Has AKEM.invariants]
  [bytesInv5: BytesInvariants.Has AEAD.invariants]

attribute [reducible, scoped instance] HasBytesInvariants.bytesInv
attribute [           scoped instance] HasBytesInvariants.bytesInvProof
attribute [           scoped instance] HasBytesInvariants.bytesInv0
attribute [           scoped instance] HasBytesInvariants.bytesInv1
attribute [           scoped instance] HasBytesInvariants.bytesInv2
attribute [           scoped instance] HasBytesInvariants.bytesInv3
attribute [           scoped instance] HasBytesInvariants.bytesInv4
attribute [           scoped instance] HasBytesInvariants.bytesInv5

end BytesInvariantsConfig

public section TraceInvariant

variable [HasBytesInvariants]

instance HPKEAuthEventInv : ProtocolEvent.EventInv HPKEAuthEvent
where
  invariant tr ev :=
    match ev with
    | .SealEvent _ recipient _ sharedSecret pt =>
      sharedSecret.Invariant tr ∧
      pt.Invariant tr ∧
      (pt.label tr).canFlow (sharedSecret.label tr) tr.erase ∧
      (∃ rpk,
        (LongTermKeys.label "HPKE Auth PKI" recipient rpk).canFlow (pt.label tr) tr.erase)

    | .OpenEvent recipient sender enc sharedSecret pt =>
      sharedSecret.Invariant tr ∧
      pt.Invariant tr ∧
      (pt.label tr).canFlow (sharedSecret.label tr) tr.erase ∧
      (
        tr.erase.EventLogged (HPKEAuthEvent.SealEvent sender recipient enc sharedSecret pt) ∨
        (∃ spk, LongTermKeys.LongTermKeyCompromised "HPKE Auth PKI" sender spk tr.erase) ∨
        (∃ rpk, LongTermKeys.LongTermKeyCompromised "HPKE Auth PKI" recipient rpk tr.erase)
      )

@[grind]
instance : LongTermKeys.ProofConfig "HPKE Auth PKI" mk_long_term_usage (LongTermKeys.label "HPKE Auth PKI")
where
  IsLongTermPublicKey who vk tr :=
    vk.Publishable tr ∧
    vk.kemSkLabel tr = LongTermKeys.label "HPKE Auth PKI" who vk ∧
    vk.KemSkHasUsage (mk_long_term_usage who) tr

  IsLongTermPublicKey_implied := by
    simp_all [Bytes.Publishable]
    grind

end TraceInvariant

public section TraceInvariantConfig

class HasTraceInvariant extends HasBytesInvariants where
  [traceInv: TraceInvariant]
  [traceInv0: TraceInvariant.Has Network.ProofEntryT]
  [traceInv1: TraceInvariant.Has Random.ProofEntryT]
  [traceInv2: TraceInvariant.Has (ProtocolEvent.ProofEntryT HPKEAuthEvent)]
  [traceInv3: TraceInvariant.Has (LongTermKeys.ProofEntryT "HPKE Auth PKI")]
  [attBaseThm: BaseAttackerKnowledgeTheorem]
  [attThm: AttackerKnowledgeTheorem]

attribute [reducible, scoped instance] HasTraceInvariant.traceInv
attribute [           scoped instance] HasTraceInvariant.traceInv0
attribute [           scoped instance] HasTraceInvariant.traceInv1
attribute [           scoped instance] HasTraceInvariant.traceInv2
attribute [           scoped instance] HasTraceInvariant.traceInv3
attribute [           scoped instance] HasTraceInvariant.attBaseThm
attribute [           scoped instance] HasTraceInvariant.attThm

end TraceInvariantConfig

public section Proofs

variable [HasTraceInvariant]

attribute [local grind] ProtocolEvent.EventInv.invariant
attribute [local grind] HPKEAuthEventInv
attribute [local grind] LongTermKeys.IsLongTermPublicKey
attribute [local grind] LongTermKeys.IsLongTermSecretKey

instance deriveKey.spec (sharedSecret: Bytes)
  : HoareTriplePure
      (deriveKey sharedSecret)
      (fun tr => sharedSecret.Invariant tr)
      (fun key tr => key.Invariant tr)
where
  pf := by
    intro tr h_ss_inv
    change (deriveKey sharedSecret).Invariant tr
    simpa [deriveKey] using h_ss_inv

instance deriveNonce.spec (sharedSecret: Bytes)
  : HoareTriplePure
      (deriveNonce sharedSecret)
      (fun tr => sharedSecret.Invariant tr)
      (fun nonce tr => nonce.Invariant tr)
where
  pf := by
    intro tr h_ss_inv
    change (deriveNonce sharedSecret).Invariant tr
    simpa [deriveNonce] using h_ss_inv


theorem deriveKey_inj (ss1 ss2: Bytes)
  : deriveKey ss1 = deriveKey ss2 → ss1 = ss2
:= by
  intro h
  simp only [deriveKey] at h
  have hc :
      Concat.concat (Literal.literalToBytes "key".toByteArray) ss1
        = Concat.concat (Literal.literalToBytes "key".toByteArray) ss2 :=
    Hash.hash_inj _ _ h
  have h1 := Concat.split_concat (Literal.literalToBytes "key".toByteArray) ss1
  have h2 := Concat.split_concat (Literal.literalToBytes "key".toByteArray) ss2
  rw [hc] at h1
  rw [h1] at h2
  simp at h2
  exact h2

-- @[instance]
-- theorem AKEM.kemDecap.spec
--   (skR senderPk enc: Bytes)
--   : HoareTriple
--       (monadLift (m := Err) (n := Traceful) (AKEM.kemDecap skR senderPk enc))
--       (fun tr =>
--         skR.Invariant tr ∧
--         senderPk.Invariant tr ∧
--         enc.Invariant tr
--       )
--       (fun sharedSecret tr =>
--         AKEM.kemDecap skR senderPk enc = some sharedSecret ∧
--         sharedSecret.Invariant tr ∧
--         (sharedSecret.label tr).canFlow (skR.label tr) tr.erase
--       )
--   := by
--     apply HoareTriple.mk
--     simp only [hoareTriple, wp, monadLift, MonadLift.monadLift, Traceful.run_mk]
--     intro tr h_pre h_inv
--     have h_kem := (AKEM.kemDecap_hoareTriple (skR := skR) (pkS := senderPk) (cipher := enc)).pf tr h_pre h_inv
--     refine ⟨tr, ?_, h_inv, rfl, ?_⟩
--     · cases h : AKEM.kemDecap skR senderPk enc with
--       | none => trivial
--       | some ss =>
--         have h_post := h_kem
--         simp [wp, h] at h_post
--         simpa using h_post.2
--     · grind

@[instance]
theorem AEAD.aead_dec.spec
  (key nonce aad ct: Bytes)
  : HoareTriple
      (monadLift (m := Err) (n := Traceful) (AEAD.aead_dec key nonce aad ct))
      (fun tr =>
        key.Invariant tr ∧
        nonce.Invariant tr ∧
        aad.Invariant tr ∧
        ct.Invariant tr
      )
      (fun pt tr =>
        pt.Invariant tr ∧
        (pt.label tr).canFlow (key.label tr) tr.erase ∧
        (
          AEAD.AeadPred.pred key aad pt tr ∨
          (key.label tr).canFlow Label.pub tr.erase
        )
      )
  := by
    apply HoareTriple.mk
    simp only [hoareTriple, wp, monadLift, MonadLift.monadLift, Traceful.run_mk]
    intro tr h_pre h_inv
    refine ⟨tr, ?_, h_inv, rfl, ?_⟩
    · cases h : AEAD.aead_dec key nonce aad ct with
      | none => trivial
      | some pt =>
        -- Read the authentication disjunction back out of the (pure) decryption
        -- triple; `open` turns it into the `SealEvent`-or-compromise disjunct.
        have h_triple := (AEAD.aead_dec_hoareTriple key nonce aad ct).pf tr h_pre
        rw [h] at h_triple
        exact h_triple
    · grind

@[instance]
theorem Sender.seal.spec
  (me recipient: Participant)
  (meSkHandle recipientPkHandle: Nat)
  : HoareTriple
      (Sender.seal me recipient meSkHandle recipientPkHandle)
      (fun _ => True)
      (fun _ _ => True)
  := by
    apply HoareTriple.mk
    unfold Sender.seal
    step
    step
    step with ⟨ fun _ => recipientPk.kemSkLabel tr, Usage.nothing ⟩
    step with ⟨ fun _ => recipientPk.kemSkLabel tr, Usage.nothing ⟩
    step with ⟨ fun _ => Label.pub, Usage.nothing ⟩
    split
    rename_i _ enc sharedSecret heq
    have kemPost : ∀ tr,
        recipientPk.Invariant tr → senderSk.Invariant tr → entropy.Invariant tr →
        entropy.label tr = recipientPk.kemSkLabel tr →
        enc.Publishable tr ∧ sharedSecret.Invariant tr ∧
          sharedSecret.label tr = entropy.label tr := by
      intro tr h_pkR h_skS h_ent h_lbl
      have h_post := (AKEM.kemEncap_hoareTriple (pkR := recipientPk) (skS := senderSk)
        (entropy := entropy)).pf tr ⟨h_pkR, h_skS, h_ent, h_lbl⟩
      rw [heq] at h_post
      exact h_post
    step by
      exact (kemPost tr (by grind) (by grind) ‹entropy.Invariant tr›
        ‹entropy.label tr = recipientPk.kemSkLabel tr›).2.1
    step by
      exact (kemPost tr (by grind) (by grind) ‹entropy.Invariant tr›
        ‹entropy.label tr = recipientPk.kemSkLabel tr›).2.1
    step by
      have h_kem_post := kemPost tr (by grind) (by grind) ‹entropy.Invariant tr›
        ‹entropy.label tr = recipientPk.kemSkLabel tr›
      have h_ss_inv : sharedSecret.Invariant tr := h_kem_post.2.1
      have h_ss_lbl : sharedSecret.label tr = entropy.label tr := h_kem_post.2.2
      have h_pt_flow : (pt.label tr).canFlow (sharedSecret.label tr) tr.erase := by
        simpa [‹pt.label tr = recipientPk.kemSkLabel tr›, h_ss_lbl, ‹entropy.label tr = recipientPk.kemSkLabel tr›] using canFlowRefl (recipientPk.kemSkLabel tr) tr.erase
      have h_rec_flow : (LongTermKeys.label "HPKE Auth PKI" recipient recipientPk).canFlow (pt.label tr) tr.erase := by
        grind [canFlowTrans]
      -- Construct the SealEvent invariant: 4 conjuncts
      exact ⟨h_ss_inv, ‹pt.Invariant tr›, h_pt_flow, recipientPk, h_rec_flow⟩
    step by
      have h_kem_post := kemPost tr (by grind) (by grind) ‹entropy.Invariant tr›
        ‹entropy.label tr = recipientPk.kemSkLabel tr›
      have h_ss_inv : sharedSecret.Invariant tr := h_kem_post.2.1
      have h_ss_lbl : sharedSecret.label tr = entropy.label tr := h_kem_post.2.2
      have h_key_inv : key.Invariant tr := by
        change (deriveKey sharedSecret).Invariant tr
        simpa [deriveKey] using h_ss_inv
      have h_nonce_inv : nonce.Invariant tr := by
        change (deriveNonce sharedSecret).Invariant tr
        simpa [deriveNonce] using h_ss_inv
      have h_pub_meet (l: Label) : Label.meet Label.pub l = l := by
        ext tr'
        simp [Label.meetIsCorrupt, Label.pubIsCorrupt]
      have h_key_lbl : key.label tr = sharedSecret.label tr := by
        change (deriveKey sharedSecret).label tr = sharedSecret.label tr
        simp [deriveKey, h_pub_meet]
      obtain ⟨_, _, h_senderSk_usg⟩ :=
        ‹LongTermKeys.IsLongTermSecretKey "HPKE Auth PKI" me senderSk tr›
      obtain ⟨_, _, h_recipientPk_usg⟩ :=
        ‹LongTermKeys.IsLongTermPublicKey "HPKE Auth PKI" recipient recipientPk tr›
      rw [Bytes.KemSkHasUsage_eq_XXXHasUsage] at h_recipientPk_usg
      refine ⟨h_key_inv, h_nonce_inv, ‹aad.Invariant tr›, ‹pt.Invariant tr›, ?_,
        Or.inl ⟨me, recipient, senderSk, recipientPk, entropy,
          ?_, h_senderSk_usg, h_recipientPk_usg, ?_⟩⟩
      · rw [h_key_lbl, h_ss_lbl, ‹pt.label tr = recipientPk.kemSkLabel tr›,
          ‹entropy.label tr = recipientPk.kemSkLabel tr›]
        exact canFlowRefl _ _
      · rw [heq]
      · simp only [heq]
        exact ‹Trace.EventLogged (HPKEAuthEvent.SealEvent me recipient enc sharedSecret pt) tr.erase›
    step by
      have h_enc_pub : enc.Publishable tr := (kemPost tr (by grind) (by grind)
        ‹entropy.Invariant tr› ‹entropy.label tr = recipientPk.kemSkLabel tr›).1
      grind
    step
    trivial


@[instance]
theorem Recipient.open.spec
  (me sender: Participant)
  (meSkHandle senderPkHandle: Nat)
  (msgHandle: Nat)
  : HoareTriple
      (Recipient.open me sender meSkHandle senderPkHandle msgHandle)
      (fun _ => True)
      (fun _ _ => True)
  := by
    apply HoareTriple.mk
    unfold Recipient.open
    step
    step
    step
    step
    step
    step
    step with ⟨ () ⟩
    rename_i h_msgBytes h_msg h_meSk h_senderPk h_ss_inv h_ss_flow h_key h_nonce
    obtain ⟨pkR, pkS', entropy, h_encap_view, h_pkS_match, h_pkR_match, h_ss_shape⟩ :=
      DY.AKEM.decap_success meSk senderPk msg.enc sharedSecret h_senderPk
    mark_non_monotone h_ss_flow
    step
    step by
      have h_pub_meet (l: Label) : Label.meet Label.pub l = l := by
        ext tr'
        simp [Label.meetIsCorrupt, Label.pubIsCorrupt]
      have h_key_ss : key.label tr = sharedSecret.label tr := by
        change (deriveKey sharedSecret).label tr = sharedSecret.label tr
        simp [deriveKey, h_pub_meet]
      have h_pt_ss : (pt.label tr).canFlow (sharedSecret.label tr) tr.erase := by
        simpa [h_key_ss] using ‹(pt.label tr).canFlow (key.label tr) tr.erase›
      refine ⟨‹sharedSecret.Invariant tr›, ‹pt.Invariant tr›, h_pt_ss, ?_⟩
      -- A public long-term-key label means that key is compromised. Used by every
      -- key-compromise fallback below, in both the honest and attacker branches.
      have compromised : ∀ (who : Participant) (vk : Bytes),
          (LongTermKeys.label "HPKE Auth PKI" who vk).canFlow Label.pub tr.erase →
          LongTermKeys.LongTermKeyCompromised "HPKE Auth PKI" who vk tr.erase := by
        intro who vk hpub
        have hcorrupt : (LongTermKeys.label "HPKE Auth PKI" who vk).isCorrupt tr.erase := by
          simpa [canFlowPubEqIsCorrupt] using hpub
        simpa [LongTermKeys.label] using hcorrupt
      -- The sender's public-key label equals its registered long-term label; shared
      -- by both sender-compromise fallbacks.
      have h_pkS_lbl : pkS'.label tr = LongTermKeys.label "HPKE Auth PKI" sender senderPk := by
        obtain ⟨_, h_senderPk_lbl, _⟩ :=
          ‹LongTermKeys.IsLongTermPublicKey "HPKE Auth PKI" sender senderPk tr›
        rw [← Bytes.kemSkLabel_kemPk pkS' tr, h_pkS_match]
        exact h_senderPk_lbl
      rcases ‹AEAD.AeadPred.pred key msg.aad pt tr ∨ (key.label tr).canFlow Label.pub tr.erase›
        with h_pred | h_pub
      · -- Honest branch: the AEAD predicate pins the KEM shape; we match it to the
        -- recipient's decapsulation view to recover the original `SealEvent`.
        obtain ⟨s', r', senderSk', recipientPk', entropy', h_key_eq, h_sUsg, h_rUsg, h_sealed⟩ := h_pred
        have h_ss_eq : sharedSecret = (AKEM.kemEncap recipientPk' senderSk' entropy').snd :=
          deriveKey_inj _ _ h_key_eq
        simp only [AKEM.kemEncap] at h_ss_eq h_sealed
        -- Pin the KEM fields by injectivity of `SharedSecret` packing.
        rw [h_ss_eq] at h_ss_shape
        have hview := congrArg (fun b => Bytes.view? b AKEM.SharedSecret.SubF) h_ss_shape
        simp only [AKEM.SharedSecret.SubF.pack_view_eq] at hview
        obtain ⟨rfl, rfl, rfl⟩ := hview
        -- The sealed ciphertext component is exactly `msg.enc`.
        have h_enc_eq :
            ({ pkR := pkR, skS := pkS', entropy := entropy } : AKEM.Encap.SubF Bytes).pack = msg.enc := by
          have h := Bytes.pack_view? AKEM.Encap.SubF msg.enc
          rw [h_encap_view] at h
          exact h
        -- Sender's registered public key carries the sender usage on `pkS'`.
        obtain ⟨_, _, h_senderPk_usg⟩ :=
          ‹LongTermKeys.IsLongTermPublicKey "HPKE Auth PKI" sender senderPk tr›
        rw [← h_pkS_match, Bytes.KemSkHasUsage_kemPk] at h_senderPk_usg
        -- Recipient's registered secret key carries the recipient usage on `meSk`.
        obtain ⟨_, h_meSk_lbl, h_meSk_usg⟩ :=
          ‹LongTermKeys.IsLongTermSecretKey "HPKE Auth PKI" me meSk tr›
        rw [h_pkR_match] at h_rUsg
        rw [← Bytes.KemSkHasUsage_eq_XXXHasUsage, Bytes.KemSkHasUsage_kemPk] at h_rUsg
        -- Pin the sender principal (or fall back to sender-key compromise).
        rcases Bytes.HasUsage_inj pkS' (mk_long_term_usage s') (mk_long_term_usage sender) tr h_sUsg h_senderPk_usg
          with h_s_eq | h_pkS_pub
        · have hs : s' = sender := mk_long_term_usage_inj h_s_eq
          subst hs
          -- Pin the recipient principal (or fall back to recipient-key compromise).
          rcases Bytes.HasUsage_inj meSk (mk_long_term_usage r') (mk_long_term_usage me) tr h_rUsg h_meSk_usg
            with h_r_eq | h_meSk_pub
          · have hr : r' = me := mk_long_term_usage_inj h_r_eq
            subst hr
            left
            rw [h_enc_eq, ← h_ss_eq] at h_sealed
            exact h_sealed
          · -- `meSk` is public ⇒ the recipient (me) long-term key is compromised.
            right; right
            exact ⟨AKEM.kemPk meSk, compromised me (AKEM.kemPk meSk) (by
              rw [← h_meSk_lbl]; exact h_meSk_pub)⟩
        · -- `pkS'` is public ⇒ the sender long-term key is compromised.
          right; left
          exact ⟨senderPk, compromised sender senderPk (by rw [← h_pkS_lbl]; exact h_pkS_pub)⟩
      · -- Attacker branch: the key (hence the shared secret) is public.  The
        -- shared-secret authentication invariant then forces either the sender's
        -- or the recipient's long-term key to be compromised.
        have h_ss_pub : (sharedSecret.label tr).canFlow Label.pub tr.erase := by
          rw [← h_key_ss]; exact h_pub
        have h_ss_lbl_eq : sharedSecret.label tr = entropy.label tr := by
          rw [h_ss_shape]; exact AKEM.SharedSecret.label_pack pkR pkS' entropy tr
        -- Unpack the authentication clause from the shared-secret invariant.
        have h_ss_inv' : sharedSecret.Invariant tr := ‹sharedSecret.Invariant tr›
        rw [h_ss_shape, AKEM.SharedSecret.Invariant_pack] at h_ss_inv'
        obtain ⟨_, _, _, h_auth⟩ := h_ss_inv'
        rcases h_auth with h_pkS_pub | h_pkR_flow
        · -- The sender's secret key is public ⇒ the sender's long-term key is compromised.
          right; left
          exact ⟨senderPk, compromised sender senderPk (by rw [← h_pkS_lbl]; exact h_pkS_pub)⟩
        · -- The entropy is public (since the shared secret is), and `pkR`'s underlying
          -- secret-key label flows into it ⇒ the recipient's long-term key is compromised.
          right; right
          have h_entropy_pub : (entropy.label tr).canFlow Label.pub tr.erase := by
            rw [← h_ss_lbl_eq]; exact h_ss_pub
          have h_pkR_pub : (pkR.kemSkLabel tr).canFlow Label.pub tr.erase :=
            canFlowTrans _ _ _ tr.erase h_pkR_flow h_entropy_pub
          obtain ⟨_, h_meSk_lbl, _⟩ :=
            ‹LongTermKeys.IsLongTermSecretKey "HPKE Auth PKI" me meSk tr›
          have h_pkR_kemsk : pkR.kemSkLabel tr = meSk.label tr := by
            rw [h_pkR_match]; exact Bytes.kemSkLabel_kemPk meSk tr
          exact ⟨AKEM.kemPk meSk, compromised me (AKEM.kemPk meSk) (by
            rw [← h_meSk_lbl, ← h_pkR_kemsk]; exact h_pkR_pub)⟩
    step
    trivial

end Proofs

section ReachabilityImpliesInvariant

variable [HasTraceInvariant]

public instance: ReachableImpliesInvariant Sender.seal.reachability := .mk (fun (me, recipient, meSkHandle, recipientPkHandle) => Sender.seal.spec me recipient meSkHandle recipientPkHandle)
public instance: ReachableImpliesInvariant Recipient.open.reachability := .mk (fun (me, sender, meSkHandle, senderPkHandle, msgHandle) => Recipient.open.spec me sender meSkHandle senderPkHandle msgHandle)

#combine into ReachabilityTheorem from
  Network,
  LongTermKeys "HPKE Auth PKI",
  Sender.seal,
  Recipient.open,

end ReachabilityImpliesInvariant

end DY.Example.HPKE
