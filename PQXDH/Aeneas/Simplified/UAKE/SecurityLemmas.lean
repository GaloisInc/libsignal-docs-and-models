/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.SecurityDefs

/-!
# Security Lemmas for the Simplified Extraction

The bridge from the extracted scheme to the Spec model: under the clean-group
model, each extracted party simulates its Spec counterpart, and the UAKE
advantage transports along the simulation. The proofs in this file are
AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

noncomputable section

variable {SPK SSK S C Msg IdC IdK : Type}

def specParams (P : Parameters SPK SSK S C Msg IdC IdK) (F : Type) (gen : ECKey) :
    _root_.PQXDH.Parameters F ECKey SS PQPK PQSK CT SPK SSK S C Msg Key IdC IdK where
  gen := gen
  pqkem := pqkem P
  sig := P.sig
  aead := P.aead
  kdf := fun km => getOk (deriveKeys km.1 km.2.1 km.2.2.1 km.2.2.2.1 km.2.2.2.2)
  idEC := P.idEC
  idKEM := P.idKEM

variable {F : Type}

def ukOfSpec (privEnc : F → Bytes 32#usize)
    (uk : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg) :
    InitiatorParameters SPK Msg where
  ikA := kpOfPair privEnc uk.ikA
  ikB := uk.ikB
  sigpkB := uk.sigpkB
  msg := uk.msg

def tkOfSpec (privEnc : F → Bytes 32#usize)
    (tk : _root_.PQXDH.RecipientIdentity F ECKey SPK SSK S) :
    RecipientIdentity SPK SSK S where
  ikB := kpOfPair privEnc tk.ikB
  sigkB := tk.sigkB
  spkB := kpOfPair privEnc tk.spkB
  spkSigB := tk.spkSigB

def rpOfSpec (privEnc : F → Bytes 32#usize)
    (rp : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S) :
    RecipientParameters SPK SSK S where
  ikB := kpOfPair privEnc rp.ikB
  sigkB := rp.sigkB
  spkB := kpOfPair privEnc rp.spkB
  spkSigB := rp.spkSigB
  opkB := rp.opkB.map (kpOfPair privEnc)
  pqpkB := rp.pqpkB


section GroupModelBridge

variable [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey]
  (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECKey) (privEnc : F → Bytes 32#usize)

lemma genOPK_toSpec (hM : ECGroupModel P gen privEnc) (hasOPK : Bool) :
    genOPK P.ecKeygen hasOPK
      = Option.map (kpOfPair privEnc) <$> _root_.PQXDH.genOPK (F := F) gen hasOPK := by
  rw [hM.keygen_eq]
  cases hasOPK <;> simp [genOPK, _root_.PQXDH.genOPK, Functor.map_map]

lemma setup_toSpec (hM : ECGroupModel P gen privEnc) (msg : Msg) :
    setup P msg
      = Prod.map (ukOfSpec privEnc) (tkOfSpec privEnc) <$>
          _root_.PQXDH.setup (specParams P F gen) msg := by
  simp only [setup, _root_.PQXDH.setup, hM.keygen_eq, map_bind, bind_map_left]
  rfl

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
lemma publish_toSpec
    (rp : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S) :
    publish P (rpOfSpec privEnc rp) = _root_.PQXDH.publish (specParams P F gen) rp := by
  refine bind_congr fun σ => ?_
  rcases hopk : rp.opkB with _ | opk <;>
    simp [rpOfSpec, kpOfPair, hopk, specParams]

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
lemma kpOfPair_public (p : ECKey × F) :
    (kpOfPair privEnc p).public_key = p.1 :=
  rfl

lemma pqxdh_initiate_groupModel (hM : ECGroupModel P gen privEnc)
    (p₁ p₂ : ECKey × F) (ikB spk : ECKey) (opk : Option ECKey) (pqpk : PQPK)
    (coins : Coins) {ss : SS} {ct : CT} {ks : Key × Key × Key}
    (henc : pqxdh.mlkem_encapsulate pqpk coins = .ok (ss, ct))
    (hks : deriveKeys (_root_.PQXDH.DH p₁.2 spk) (_root_.PQXDH.DH p₂.2 ikB)
      (_root_.PQXDH.DH p₂.2 spk) (Option.map (fun o => _root_.PQXDH.DH p₂.2 o) opk) ss
      = .ok ks) :
    pqxdh.pqxdh_initiate
      { our_identity_key_pair := kpOfPair privEnc p₁
        our_ephemeral_key_pair := kpOfPair privEnc p₂
        their_identity_key := ikB
        their_signed_pre_key := spk
        their_one_time_pre_key := opk
        their_kyber_pre_key := pqpk } coins
      = .ok ⟨⟨ks.1, ks.2.1, ks.2.2⟩, ct⟩ := by
  unfold pqxdh.pqxdh_initiate
  cases opk with
  | none =>
      simp only [Option.map_none] at hks
      cases hsi : pqxdh.pqxdh_secret_input (_root_.PQXDH.DH p₁.2 spk)
          (_root_.PQXDH.DH p₂.2 ikB) (_root_.PQXDH.DH p₂.2 spk) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.agree_eq, Aeneas.Std.lift, henc, hsi, hokm, hsplit]
  | some o =>
      simp only [Option.map_some] at hks
      cases hsi : pqxdh.pqxdh_secret_input_with_opk (_root_.PQXDH.DH p₁.2 spk)
          (_root_.PQXDH.DH p₂.2 ikB) (_root_.PQXDH.DH p₂.2 spk)
          (_root_.PQXDH.DH p₂.2 o) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.agree_eq, Aeneas.Std.lift, henc, hsi, hokm, hsplit]

lemma pqxdh_accept_groupModel (hM : ECGroupModel P gen privEnc)
    (q₁ q₂ : ECKey × F) (opkq : Option (ECKey × F)) (pqsk : PQSK)
    (ikA ekA : ECKey) (ct : CT) {ss : SS} {ks : Key × Key × Key}
    (hdec : pqxdh.mlkem_decapsulate pqsk ct = .ok ss)
    (hks : deriveKeys (_root_.PQXDH.DH q₂.2 ikA) (_root_.PQXDH.DH q₁.2 ekA)
      (_root_.PQXDH.DH q₂.2 ekA) (Option.map (fun o => _root_.PQXDH.DH o.2 ekA) opkq) ss
      = .ok ks) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := kpOfPair privEnc q₁
        our_signed_pre_key_pair := kpOfPair privEnc q₂
        our_one_time_pre_key_pair := opkq.map (kpOfPair privEnc)
        our_kyber_secret_key := pqsk
        their_identity_key := ikA
        their_ephemeral_key := ekA
        their_kyber_ciphertext := ct } = .ok (some ⟨ks.1, ks.2.1, ks.2.2⟩) := by
  unfold pqxdh.pqxdh_accept
  cases opkq with
  | none =>
      simp only [Option.map_none] at hks ⊢
      cases hsi : pqxdh.pqxdh_secret_input (_root_.PQXDH.DH q₂.2 ikA)
          (_root_.PQXDH.DH q₁.2 ekA) (_root_.PQXDH.DH q₂.2 ekA) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.canonical_eq, hM.agree_eq, Aeneas.Std.lift, hdec, hsi, hokm, hsplit]
  | some o =>
      simp only [Option.map_some] at hks ⊢
      cases hsi : pqxdh.pqxdh_secret_input_with_opk (_root_.PQXDH.DH q₂.2 ikA)
          (_root_.PQXDH.DH q₁.2 ekA) (_root_.PQXDH.DH q₂.2 ekA)
          (_root_.PQXDH.DH o.2 ekA) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.canonical_eq, hM.agree_eq, Aeneas.Std.lift, hdec, hsi, hokm, hsplit]

lemma initiate_toSpec (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (uk : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg)
    (bundle : PreKeyBundle ECKey PQPK S IdC IdK) :
    initiate P (ukOfSpec privEnc uk) bundle
      = _root_.PQXDH.initiate (specParams P F gen) uk bundle := by
  simp only [initiate, _root_.PQXDH.initiate, ukOfSpec, specParams, hM.keygen_eq,
    bind_map_left]
  by_cases hpin : bundle.ikB = uk.ikB
  · simp only [hpin, ne_eq, not_true_eq_false, if_false]
    refine bind_congr fun _ => ?_
    refine bind_congr fun okSPK => ?_
    refine bind_congr fun okPQPK => ?_
    cases okSPK with
    | false => simp
    | true =>
    cases okPQPK with
    | false => simp
    | true =>
    simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false]
    refine bind_congr fun _ => ?_
    refine bind_congr fun a => ?_
    simp only [pqkem, bind_assoc]
    refine bind_congr fun coins => ?_
    obtain ⟨⟨ss, ct⟩, henc⟩ := hencTotal bundle.pqpkB.1 coins
    obtain ⟨ks, hks⟩ := hkdfTotal (_root_.PQXDH.DH uk.ikA.2 bundle.spkB.1)
      (_root_.PQXDH.DH a.2 uk.ikB) (_root_.PQXDH.DH a.2 bundle.spkB.1)
      (Option.map (fun o => _root_.PQXDH.DH a.2 o) (bundle.opkB.map Prod.fst)) ss
    rw [pqxdh_initiate_groupModel P gen privEnc hM uk.ikA a uk.ikB bundle.spkB.1
      (bundle.opkB.map Prod.fst) bundle.pqpkB.1 coins henc hks]
    have hmap : Option.map (fun o => _root_.PQXDH.DH a.2 o) (bundle.opkB.map Prod.fst)
        = bundle.opkB.map fun opk => _root_.PQXDH.DH a.2 opk.1 := by
      cases bundle.opkB <;> rfl
    rw [hmap] at hks
    simp [henc, hks, getOk, kpOfPair]
  · simp [hpin]

lemma accept_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc)
    (hkdfTotal : DeriveKeysTotal)
    (rp : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S)
    (im : InitialMessage ECKey CT C IdC IdK) :
    accept P (rpOfSpec privEnc rp) im = _root_.PQXDH.accept (specParams P F gen) rp im := by
  simp only [accept, _root_.PQXDH.accept, rpOfSpec, specParams, kpOfPair_public,
    Option.map_map, Function.comp_def]
  by_cases hguard : im.idSPK ≠ P.idEC rp.spkB.1 ∨ im.idPQPK ≠ P.idKEM rp.pqpkB.1 ∨
      im.idOPK ≠ Option.map (fun opk => P.idEC opk.1) rp.opkB
  · simp [hguard]
  · simp only [hguard, if_false]
    cases hdec : pqxdh.mlkem_decapsulate rp.pqpkB.2 im.ct with
    | ok ss =>
        obtain ⟨ks, hks⟩ := hkdfTotal (_root_.PQXDH.DH rp.spkB.2 im.ikA)
          (_root_.PQXDH.DH rp.ikB.2 im.ekA) (_root_.PQXDH.DH rp.spkB.2 im.ekA)
          (Option.map (fun opk => _root_.PQXDH.DH opk.2 im.ekA) rp.opkB) ss
        rw [pqxdh_accept_groupModel P gen privEnc hM rp.ikB rp.spkB rp.opkB rp.pqpkB.2
          im.ikA im.ekA im.ct hdec hks]
        simp only [pqkem, hdec, pure_bind]
        simp only [hks, getOk]
        cases P.aead.decrypt ks.2.1 (im.ikA, rp.ikB.1, rp.pqpkB.1) im.ctxt <;> rfl
    | fail e =>
        have hacc : pqxdh.pqxdh_accept
            { our_identity_key_pair := kpOfPair privEnc rp.ikB
              our_signed_pre_key_pair := kpOfPair privEnc rp.spkB
              our_one_time_pre_key_pair := rp.opkB.map (kpOfPair privEnc)
              our_kyber_secret_key := rp.pqpkB.2
              their_identity_key := im.ikA
              their_ephemeral_key := im.ekA
              their_kyber_ciphertext := im.ct } = .fail e := by
          simp [pqxdh.pqxdh_accept, kpOfPair, hM.canonical_eq, hM.agree_eq, hdec]
        rw [hacc]
        simp [pqkem, hdec]
    | div =>
        have hacc : pqxdh.pqxdh_accept
            { our_identity_key_pair := kpOfPair privEnc rp.ikB
              our_signed_pre_key_pair := kpOfPair privEnc rp.spkB
              our_one_time_pre_key_pair := rp.opkB.map (kpOfPair privEnc)
              our_kyber_secret_key := rp.pqpkB.2
              their_identity_key := im.ikA
              their_ephemeral_key := im.ekA
              their_kyber_ciphertext := im.ct } = .div := by
          simp [pqxdh.pqxdh_accept, kpOfPair, hM.canonical_eq, hM.agree_eq, hdec]
        rw [hacc]
        simp [pqkem, hdec]

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
lemma confirm_toSpec [DecidableEq Msg]
    (ctx : SessionContext ECKey PQPK Msg Key) (conf : C) :
    confirm P ctx conf = _root_.PQXDH.confirm (specParams P F gen) ctx conf :=
  rfl

lemma initiator_init_toSpec [DecidableEq Msg]
    (uk : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg) :
    (initiator P).init (ukOfSpec privEnc uk)
      = Party.InitResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (_root_.PQXDH.initiator (specParams P F gen)).init uk := by
  simp only [initiator, _root_.PQXDH.initiator, map_pure, Party.InitResult.map, Sum.map_inl]

lemma initiator_step_toSpec [DecidableEq Msg]
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (st : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg ⊕
      SessionContext ECKey PQPK Msg Key ⊕ Key)
    (w : Message ECKey PQPK CT S C IdC IdK) :
    (initiator P).step (Sum.map (ukOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (_root_.PQXDH.initiator (specParams P F gen)).step st w := by
  rcases st with p | ctx | k
  · cases w with
    | bundle b =>
        simp only [initiator, _root_.PQXDH.initiator, Sum.map_inl,
          initiate_toSpec P gen privEnc hM hencTotal hkdfTotal p b, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ⟨im, ctx⟩ <;> simp [Party.StepResult.map]
    | initial im => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
    | confirmation c => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
  · cases w with
    | bundle b => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
    | initial im => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
    | confirmation conf =>
        simp only [initiator, _root_.PQXDH.initiator, Sum.map_inr, id_eq]
        rw [confirm_toSpec (F := F) P gen ctx conf]
        cases _root_.PQXDH.confirm (specParams P F gen) ctx conf <;> simp [Party.StepResult.map]
  · cases w <;> simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]

lemma initiator_output_toSpec [DecidableEq Msg]
    (st : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg ⊕
      SessionContext ECKey PQPK Msg Key ⊕ Key) :
    (initiator P).output (Sum.map (ukOfSpec privEnc) id st)
      = (_root_.PQXDH.initiator (specParams P F gen)).output st := by
  rcases st with p | ctx | k <;> rfl

lemma recipient_init_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc) (hasOPK : Bool)
    (tk : _root_.PQXDH.RecipientIdentity F ECKey SPK SSK S) :
    (recipient P hasOPK).init (tkOfSpec privEnc tk)
      = Party.InitResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (_root_.PQXDH.recipient (specParams P F gen) hasOPK).init tk := by
  simp only [recipient, _root_.PQXDH.recipient, genOPK_toSpec P gen privEnc hM hasOPK,
    specParams, pqkem, tkOfSpec, map_bind, bind_map_left]
  refine bind_congr fun opkB => ?_
  refine bind_congr fun pqpkB => ?_
  have hrp : (⟨kpOfPair privEnc tk.ikB, tk.sigkB, kpOfPair privEnc tk.spkB,
      tk.spkSigB, Option.map (kpOfPair privEnc) opkB, pqpkB⟩ :
        RecipientParameters SPK SSK S)
      = rpOfSpec privEnc ⟨tk.ikB, tk.sigkB, tk.spkB, tk.spkSigB, opkB, pqpkB⟩ := rfl
  rw [hrp, publish_toSpec]
  refine bind_congr fun bundle => ?_
  simp [Party.InitResult.map, rpOfSpec]

lemma recipient_step_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc)
    (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool)
    (st : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S ⊕ Key)
    (w : Message ECKey PQPK CT S C IdC IdK) :
    (recipient P hasOPK).step (Sum.map (rpOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (_root_.PQXDH.recipient (specParams P F gen) hasOPK).step st w := by
  rcases st with rp | k
  · cases w with
    | bundle b => simp [recipient, _root_.PQXDH.recipient, Party.StepResult.map]
    | initial im =>
        simp only [recipient, _root_.PQXDH.recipient, Sum.map_inl,
          accept_toSpec P gen privEnc hM hkdfTotal rp im, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ctx <;> simp [Party.StepResult.map, specParams]
    | confirmation c => simp [recipient, _root_.PQXDH.recipient, Party.StepResult.map]
  · cases w <;> simp [recipient, _root_.PQXDH.recipient, Party.StepResult.map]

lemma recipient_output_toSpec [DecidableEq IdC] [DecidableEq IdK] (hasOPK : Bool)
    (st : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S ⊕ Key) :
    (recipient P hasOPK).output (Sum.map (rpOfSpec privEnc) id st)
      = (_root_.PQXDH.recipient (specParams P F gen) hasOPK).output st := by
  rcases st with rp | k <;> rfl

variable {msg : Msg} {hasOPK : Bool}

def _root_.AKE.UAKE.Adversary.toSpec
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (gen : ECKey) (privEnc : F → Bytes 32#usize)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (_root_.PQXDH.uakeInitiator (specParams P F gen) msg hasOPK) where
  State := A.State
  challenge := fun uk w => A.challenge (ukOfSpec privEnc uk) w
  post := A.post

lemma opensAtMost_toSpec
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) {q : ℕ}
    (hq : A.OpensAtMost q) : (A.toSpec gen privEnc).OpensAtMost q :=
  ⟨fun uk w => hq.1 (ukOfSpec privEnc uk) w, hq.2⟩

lemma initiator_sim [DecidableEq Msg]
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal) :
    Party.Sim (_root_.PQXDH.initiator (specParams P F gen)) (initiator P)
      (ukOfSpec privEnc) (Sum.map (ukOfSpec privEnc) id) where
  init_eq := initiator_init_toSpec P gen privEnc
  step_eq := initiator_step_toSpec P gen privEnc hM hencTotal hkdfTotal
  output_eq := initiator_output_toSpec P gen privEnc

lemma recipient_sim [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc) (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool) :
    Party.Sim (_root_.PQXDH.recipient (specParams P F gen) hasOPK) (recipient P hasOPK)
      (tkOfSpec privEnc) (Sum.map (rpOfSpec privEnc) id) where
  init_eq := recipient_init_toSpec P gen privEnc hM hasOPK
  step_eq := recipient_step_toSpec P gen privEnc hM hkdfTotal hasOPK
  output_eq := recipient_output_toSpec P gen privEnc hasOPK

lemma exp_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A = UAKE.Exp ProbCompRuntime.probComp.toProbCompLift (A.toSpec gen privEnc) := by
  have hsetup : (uakeInitiator P msg hasOPK).setup
      = Prod.map (ukOfSpec privEnc) (tkOfSpec privEnc) <$>
        (_root_.PQXDH.uakeInitiator (specParams P F gen) msg hasOPK).setup :=
    setup_toSpec P gen privEnc hM msg
  exact (UAKE.Exp_transport ProbCompRuntime.probComp.toProbCompLift
    (proto₁ := _root_.PQXDH.uakeInitiator (specParams P F gen) msg hasOPK)
    (proto₂ := uakeInitiator P msg hasOPK)
    (initiator_sim P gen privEnc hM hencTotal hkdfTotal)
    (recipient_sim P gen privEnc hM hkdfTotal hasOPK) rfl hsetup A).trans rfl

lemma advantage_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.advantage ProbCompRuntime.probComp A = UAKE.advantage ProbCompRuntime.probComp (A.toSpec gen privEnc) := by
  unfold UAKE.advantage
  rw [exp_toSpec gen privEnc hM hencTotal hkdfTotal A]

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
lemma kdfPRF_specParams {P : Parameters SPK SSK S C Msg IdC IdK} :
    _root_.PQXDH.kdfPRF (specParams P F gen) = kdfPRF :=
  rfl

lemma kdfPRFDH_advantage_toSpec {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (D : PRFScheme.PRFAdversary (ECKey × ECKey × Option ECKey × SS) (Key × Key × Key)) :
    (_root_.PQXDH.kdfPRFDH (specParams P F gen)).prfAdvantage D
      = (kdfPRFDH P).prfAdvantage D := by
  have hreal : (_root_.PQXDH.kdfPRFDH (specParams P F gen)).prfRealExp D
      = (kdfPRFDH P).prfRealExp D := by
    unfold PRFScheme.prfRealExp
    rw [show (kdfPRFDH P).keygen = P.ecKeygen from rfl, hM.keygen_eq,
      show _root_.PQXDH.dhKeygen (F := F) gen
        = (do let a ← $ᵗ F; pure (a • gen, a)) from rfl]
    simp only [bind_map_left, bind_assoc, pure_bind]
    exact bind_congr fun c => rfl
  unfold PRFScheme.prfAdvantage
  rw [hreal]

lemma nominalDDHExpReal_toSpec (hM : ECGroupModel P gen privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECKey) :
    DiffieHellman.nominalDDHExpReal P.ecKeygen pqxdh.KeyPair.public_key x25519DH D
      = DiffieHellman.nominalDDHExpReal (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst (fun kp pk => kp.2 • pk) D := by
  unfold DiffieHellman.nominalDDHExpReal
  rw [hM.keygen_eq, show _root_.PQXDH.dhKeygen (F := F) gen
    = DiffieHellman.groupKeygen (F := F) gen from rfl]
  simp only [bind_map_left]
  refine bind_congr fun kpA => ?_
  refine bind_congr fun kpB => ?_
  simp [x25519DH, kpOfPair, hM.agree_eq, getOk, _root_.PQXDH.DH]

lemma nominalDDHExpRand_toSpec (hM : ECGroupModel P gen privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECKey) :
    DiffieHellman.nominalDDHExpRand P.ecKeygen pqxdh.KeyPair.public_key D
      = DiffieHellman.nominalDDHExpRand (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst D := by
  unfold DiffieHellman.nominalDDHExpRand
  rw [hM.keygen_eq, show _root_.PQXDH.dhKeygen (F := F) gen
    = DiffieHellman.groupKeygen (F := F) gen from rfl]
  simp only [bind_map_left]
  exact bind_congr fun kpA => bind_congr fun kpB => bind_congr fun kpC => rfl

lemma ddh_advantage_toSpec {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (D : _root_.DiffieHellman.DDHAdversary F ECKey) :
    _root_.DiffieHellman.ddhDistAdvantage gen D
      = DiffieHellman.nominalDDHDistAdvantage P.ecKeygen pqxdh.KeyPair.public_key
          x25519DH (D gen) := by
  rw [DiffieHellman.ddhDistAdvantage_eq_nominalDDHDistAdvantage]
  unfold DiffieHellman.nominalDDHDistAdvantage
  rw [nominalDDHExpReal_toSpec P gen privEnc hM (D gen),
    nominalDDHExpRand_toSpec P gen privEnc hM (D gen)]

end GroupModelBridge

end

end PQXDH.Aeneas.Simplified
