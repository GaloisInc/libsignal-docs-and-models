/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.Defs

/-!
# Correctness Lemmas for the Simplified Extraction

Supporting lemmas for `Correctness.lean`, characterizing the support of an
honest run of the extracted scheme. The proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

noncomputable section

variable {SPK SSK S C Msg IdC IdK : Type}

lemma probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := by
  rfl

lemma support_eq_singleton_true_of_evalDist {oa : ProbComp Bool}
    (h : Pr[= true | ProbCompRuntime.probComp.evalDist oa] = 1) :
    support oa = {true} := by
  rw [probOutput_probComp_evalDist, probOutput_eq_one_iff] at h
  exact h.2

lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : ECKey ⊕ PQPK) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
    {b : Bool} (hb : b ∈ support (P.sig.verify kp.1 m σ)) : b = true := by
  have h := support_eq_singleton_true_of_evalDist (hsig m)
  have hmem : b ∈ support (do
      let (pk, sk) ← P.sig.keygen
      let s ← P.sig.sign pk sk m
      P.sig.verify pk m s) := by
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨σ, hσ, hb⟩
  rw [h] at hmem
  exact hmem

lemma mlkem_decapsulate_eq_ok
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQPK × PQSK} (hkp : kp ∈ support P.pqKeygen)
    {coins : Coins} (hcoins : coins ∈ support P.encapsCoins)
    {ss : SS} {ct : CT} (henc : pqxdh.mlkem_encapsulate kp.1 coins = .ok (ss, ct)) :
    pqxdh.mlkem_decapsulate kp.2 ct = .ok ss := by
  have h := support_eq_singleton_true_of_evalDist hkem
  have hct : (ct, ss) ∈ support ((pqkem P).encaps kp.1) := by
    simp only [pqkem, mem_support_bind_iff]
    exact ⟨coins, hcoins, by simp [henc]⟩
  have key : ∀ r ∈ support ((pqkem P).decaps kp.2 ct), r = some ss := by
    intro r hr
    have hmem : decide (r = some ss) ∈ support ((pqkem P).CorrectExp) := by
      unfold KEMScheme.CorrectExp
      refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨(ct, ss), hct, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
      simp
    rw [h] at hmem
    simpa using hmem
  cases hdec : pqxdh.mlkem_decapsulate kp.2 ct with
  | ok ss' =>
      have := key (some ss') (by simp [pqkem, hdec])
      simp only [Option.some.injEq] at this
      rw [this]
  | fail e =>
      have := key none (by simp [pqkem, hdec])
      simp at this
  | div =>
      have := key none (by simp [pqkem, hdec])
      simp at this

lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : Key) (ad : ECKey × ECKey × PQPK) (m : Msg) {c : C}
    (hc : c ∈ support (P.aead.encrypt k ad m)) :
    P.aead.decrypt k ad c = some m := by
  have h := haead m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (P.aead.decrypt k ad c = some m) ∈
      support (AEAD.CorrectExp P.aead m ad) := by
    unfold AEAD.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample Key, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

lemma opkB_mem_of_genOPK {keygen : ProbComp pqxdh.KeyPair} {hasOPK : Bool}
    {opkB : Option pqxdh.KeyPair}
    (h : opkB ∈ support (genOPK keygen hasOPK)) :
    ∀ x ∈ opkB, x ∈ support keygen := by
  unfold genOPK at h
  cases hasOPK with
  | false =>
      simp only [Bool.false_eq_true, if_false, support_pure, Set.mem_singleton_iff] at h
      subst h; simp
  | true =>
      simp only [if_true, support_map, Set.mem_image] at h
      obtain ⟨opk, hopk, rfl⟩ := h
      intro x hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ hopk

lemma pqxdh_accept_eq_of_initiate_eq_ok
    (ikA ekA ikB spkB : pqxdh.KeyPair) (opkB : Option pqxdh.KeyPair)
    (pqpk : PQPK) (pqsk : PQSK) (coins : Coins) (ag : pqxdh.InitiatorAgreement)
    (hdh1 : pqxdh.x25519_agree spkB.private_key ikA.public_key
      = pqxdh.x25519_agree ikA.private_key spkB.public_key)
    (hdh2 : pqxdh.x25519_agree ikB.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key ikB.public_key)
    (hdh3 : pqxdh.x25519_agree spkB.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key spkB.public_key)
    (hdh4 : ∀ opk ∈ opkB, pqxdh.x25519_agree opk.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key opk.public_key)
    (hkem : ∀ ss ct, pqxdh.mlkem_encapsulate pqpk coins = .ok (ss, ct) →
      pqxdh.mlkem_decapsulate pqsk ct = .ok ss)
    (hcanon : pqxdh.ec_is_canonical ekA.public_key = .ok true)
    (hI : pqxdh.pqxdh_initiate
      { our_identity_key_pair := ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := ikB.public_key
        their_signed_pre_key := spkB.public_key
        their_one_time_pre_key := opkB.map pqxdh.KeyPair.public_key
        their_kyber_pre_key := pqpk } coins = .ok ag) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := ikB
        our_signed_pre_key_pair := spkB
        our_one_time_pre_key_pair := opkB
        our_kyber_secret_key := pqsk
        their_identity_key := ikA.public_key
        their_ephemeral_key := ekA.public_key
        their_kyber_ciphertext := ag.kyber_ciphertext } = .ok (some ag.keys) := by
  unfold pqxdh.pqxdh_initiate at hI
  unfold pqxdh.pqxdh_accept
  simp only [Aeneas.Std.lift] at hI ⊢
  cases h1 : pqxdh.x25519_agree ikA.private_key spkB.public_key with
  | fail e => simp [h1] at hI
  | div => simp [h1] at hI
  | ok dh1 =>
  cases h2 : pqxdh.x25519_agree ekA.private_key ikB.public_key with
  | fail e => simp [h1, h2] at hI
  | div => simp [h1, h2] at hI
  | ok dh2 =>
  cases h3 : pqxdh.x25519_agree ekA.private_key spkB.public_key with
  | fail e => simp [h1, h2, h3] at hI
  | div => simp [h1, h2, h3] at hI
  | ok dh3 =>
  cases henc : pqxdh.mlkem_encapsulate pqpk coins with
  | fail e => simp [h1, h2, h3, henc] at hI
  | div => simp [h1, h2, h3, henc] at hI
  | ok ssct =>
  obtain ⟨ss, ct⟩ := ssct
  have hdec := hkem ss ct henc
  cases opkB with
  | none =>
      cases hsi : pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss with
      | fail e => simp [h1, h2, h3, henc, hsi] at hI
      | div => simp [h1, h2, h3, henc, hsi] at hI
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [h1, h2, h3, henc, hsi, hokm] at hI
      | div => simp [h1, h2, h3, henc, hsi, hokm] at hI
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      | div => simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      subst hI
      simp [hcanon, hdh1, hdh2, hdh3, h1, h2, h3, hdec, hsi, hokm, hsplit]
  | some opk =>
      cases h4 : pqxdh.x25519_agree ekA.private_key opk.public_key with
      | fail e => simp [h1, h2, h3, henc, h4] at hI
      | div => simp [h1, h2, h3, henc, h4] at hI
      | ok dh4 =>
      cases hsi : pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss with
      | fail e => simp [h1, h2, h3, henc, h4, hsi] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi] at hI
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [h1, h2, h3, henc, h4, hsi, hokm] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi, hokm] at hI
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      subst hI
      simp [hcanon, hdh1, hdh2, hdh3, hdh4 opk rfl, h1, h2, h3, h4, hdec, hsi, hokm, hsplit]

lemma mem_support_initiate
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : InitiatorParameters SPK Msg} {bundle : PreKeyBundle ECKey PQPK S IdC IdK}
    {r : Option (InitialMessage ECKey CT C IdC IdK × SessionContext ECKey PQPK Msg Key)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    r = none ∨
      ∃ ekA ∈ support P.ecKeygen, ∃ coins ∈ support P.encapsCoins,
      ∃ ag : pqxdh.InitiatorAgreement,
        pqxdh.pqxdh_initiate
          { our_identity_key_pair := p.ikA
            our_ephemeral_key_pair := ekA
            their_identity_key := p.ikB
            their_signed_pre_key := bundle.spkB.1
            their_one_time_pre_key := bundle.opkB.map Prod.fst
            their_kyber_pre_key := bundle.pqpkB.1 } coins = .ok ag ∧
      ∃ ctxt ∈ support (P.aead.encrypt ag.keys.chain_key
          (p.ikA.public_key, p.ikB, bundle.pqpkB.1) p.msg),
        r = some (⟨p.ikA.public_key, ekA.public_key, ag.kyber_ciphertext,
            bundle.spkB.2, bundle.pqpkB.2, bundle.opkB.map Prod.snd, ctxt⟩,
          ⟨ag.keys.root_key, ag.keys.pqr_key,
            (p.ikA.public_key, p.ikB, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, ekA, hekA, coins, hcoins, hr⟩ := hr
  cases hI : pqxdh.pqxdh_initiate
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := p.ikB
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_kyber_pre_key := bundle.pqpkB.1 } coins with
  | ok ag =>
      rw [hI] at hr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨ctxt, hctxt, rfl⟩ := hr
      exact Or.inr ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  | fail e =>
      rw [hI] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr
  | div =>
      rw [hI] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr

lemma accept_eq_pure_some
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECKey CT C IdC IdK}
    {keys : pqxdh.HandshakeKeys} {m₀ : Msg}
    (hid₁ : im.idSPK = P.idEC p.spkB.public_key)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = p.opkB.map (fun opk => P.idEC opk.public_key))
    (hacc : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } = .ok (some keys))
    (hdec : P.aead.decrypt keys.chain_key (im.ikA, p.ikB.public_key, p.pqpkB.1) im.ctxt
      = some m₀) :
    accept P p im = pure (some ⟨keys.root_key, keys.pqr_key,
      (im.ikA, p.ikB.public_key, p.pqpkB.1), m₀⟩) := by
  simp [accept, hid₁, hid₂, hid₃, hacc, hdec]

lemma accept_eq_pure_none
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECKey CT C IdC IdK}
    (hacc : ∀ keys, pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } ≠ .ok (some keys)) :
    accept P p im = pure none := by
  cases hr : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } with
  | ok o =>
      cases o with
      | none => simp [accept, hr]
      | some keys => exact absurd hr (hacc keys)
  | fail e => simp [accept, hr]
  | div => simp [accept, hr]

lemma pqxdh_accept_ne_ok_some
    {rp : pqxdh.RecipientParameters} {res : Aeneas.Std.Result Bool}
    (hc : pqxdh.ec_is_canonical rp.their_ephemeral_key = res) (hres : res ≠ .ok true) :
    ∀ keys, pqxdh.pqxdh_accept rp ≠ .ok (some keys) := by
  intro keys h
  unfold pqxdh.pqxdh_accept at h
  rw [hc] at h
  cases res with
  | ok b =>
      cases b with
      | true => exact hres rfl
      | false => simp at h
  | fail e => simp at h
  | div => simp at h

lemma run_support_initiator
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : pqxdh.KeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)} {ms : List (Message ECKey PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.public_key, sigkB.1, msg⟩ ⟨ikB, sigkB, spkB, spkSigB⟩ (3 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.runHonestStart, Party.InitResult.opening, Party.InitResult.state,
    mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  rcases mem_support_initiate P rfl
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir with
    rfl | ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
    simp_all
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    dsimp only at hctxt hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
    have hmap : Option.map Prod.fst
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map pqxdh.KeyPair.public_key opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : pqxdh.ec_is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok ikA ekA ikB spkB opkB
          pqpkB.1 pqpkB.2 coins ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct h => mlkem_decapsulate_eq_ok P hkem hpqpkB hcoins h) hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
        obtain ⟨conf, hconf, rfl⟩ := hsr
        have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
        simp only [confirm, hconfirm, reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hy
        obtain ⟨x, rfl, hy⟩ := hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all
      | false =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all
    | fail e =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all
    | div =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all

lemma run_support_recipient
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : pqxdh.KeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)} {ms : List (Message ECKey PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (recipientNoConfirm P hasOPK)
      (initiatorNoConfirm P) ⟨ikB, sigkB, spkB, spkSigB⟩
      ⟨ikA, ikB.public_key, sigkB.1, msg⟩ (2 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiatorNoConfirm, recipientNoConfirm, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.runHonestStart, Party.InitResult.opening, Party.InitResult.state,
    mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  rcases mem_support_initiate P rfl
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir with
    rfl | ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
    simp_all
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    dsimp only at hctxt hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
    have hmap : Option.map Prod.fst
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map pqxdh.KeyPair.public_key opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : pqxdh.ec_is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok ikA ekA ikB spkB opkB
          pqpkB.1 pqpkB.2 coins ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct h => mlkem_decapsulate_eq_ok P hkem hpqpkB hcoins h) hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all
      | false =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all
    | fail e =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all
    | div =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        simp_all

end

end PQXDH.Aeneas.Simplified
