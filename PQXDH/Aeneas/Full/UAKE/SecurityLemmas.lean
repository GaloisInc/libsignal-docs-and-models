/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.SecurityDefs

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

variable {F : Type}

lemma bind_pure_left {α β : Type} (x : α) (f : α → Aeneas.Std.Result β) :
    (pure x : Aeneas.Std.Result α) >>= f = f x := rfl

lemma kdfInput_chain {γ : Type}
    (a1 a2 a3 : Aeneas.Std.Slice Aeneas.Std.U8)
    (a4 : Option (Aeneas.Std.Slice Aeneas.Std.U8))
    (sss : Aeneas.Std.Slice Aeneas.Std.U8) {hk : pqxdh.HandshakeKeys}
    (g : pqxdh.HandshakeKeys → Aeneas.Std.Result γ)
    (h : (do
        let inp ← kdfInput a1 a2 a3 a4 sss
        pqxdh.HandshakeKeys.derive inp) = Aeneas.Std.Result.ok hk) :
    ((do
      let i ← 32#usize * 6#usize
      let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice
        (Aeneas.Std.Array.repeat 32#usize 255#u8))
      let secrets1 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice
        Aeneas.Std.core.clone.CloneU8
        (Aeneas.Std.alloc.vec.Vec.with_capacity Aeneas.Std.U8 i) s
      let secrets2 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice
        Aeneas.Std.core.clone.CloneU8 secrets1 a1
      let secrets3 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice
        Aeneas.Std.core.clone.CloneU8 secrets2 a2
      let secrets4 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice
        Aeneas.Std.core.clone.CloneU8 secrets3 a3
      let secrets5 ← match a4 with
        | none => pure secrets4
        | some d => (Aeneas.Std.alloc.vec.Vec.extend_from_slice
            Aeneas.Std.core.clone.CloneU8 secrets4 d)
      let secrets6 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice
        Aeneas.Std.core.clone.CloneU8 secrets5 sss
      let k ← pqxdh.HandshakeKeys.derive
        (Aeneas.Std.alloc.vec.Vec.deref secrets6)
      g k) : Aeneas.Std.Result γ) = g hk := by
  simp only [kdfInput, Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at h
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  cases hmul : 32#usize * 6#usize with
  | fail e => simp [hmul] at h
  | div => simp [hmul] at h
  | ok i =>
  cases hex1 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
      (Aeneas.Std.alloc.vec.Vec.with_capacity Aeneas.Std.U8 i)
      (Aeneas.Std.Array.to_slice (Aeneas.Std.Array.repeat 32#usize 255#u8)) with
  | fail e => simp [hmul, hex1] at h
  | div => simp [hmul, hex1] at h
  | ok secrets1 =>
  cases hex2 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
      secrets1 a1 with
  | fail e => simp [hmul, hex1, hex2] at h
  | div => simp [hmul, hex1, hex2] at h
  | ok secrets2 =>
  cases hex3 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
      secrets2 a2 with
  | fail e => simp [hmul, hex1, hex2, hex3] at h
  | div => simp [hmul, hex1, hex2, hex3] at h
  | ok secrets3 =>
  cases hex4 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
      secrets3 a3 with
  | fail e => simp [hmul, hex1, hex2, hex3, hex4] at h
  | div => simp [hmul, hex1, hex2, hex3, hex4] at h
  | ok secrets4 =>
  cases a4 with
  | none =>
    cases hex6 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
        secrets4 sss with
    | fail e => simp [hmul, hex1, hex2, hex3, hex4, hex6] at h
    | div => simp [hmul, hex1, hex2, hex3, hex4, hex6] at h
    | ok secrets6 =>
      cases hdv : pqxdh.HandshakeKeys.derive (Aeneas.Std.alloc.vec.Vec.deref secrets6) with
      | fail e => simp [hmul, hex1, hex2, hex3, hex4, hex6, hdv] at h
      | div => simp [hmul, hex1, hex2, hex3, hex4, hex6, hdv] at h
      | ok k =>
        simp only [hmul, hex1, hex2, hex3, hex4, hex6, hdv, Aeneas.Std.bind_tc_ok,
          bind_pure_left, Aeneas.Std.Result.ok.injEq] at h
        subst h
        simp only [hex1, hex2, hex3, hex4, hex6, hdv, Aeneas.Std.bind_tc_ok,
          bind_pure_left]
  | some d =>
    cases hex5 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
        secrets4 d with
    | fail e => simp [hmul, hex1, hex2, hex3, hex4, hex5] at h
    | div => simp [hmul, hex1, hex2, hex3, hex4, hex5] at h
    | ok secrets5 =>
      cases hex6 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
          secrets5 sss with
      | fail e => simp [hmul, hex1, hex2, hex3, hex4, hex5, hex6] at h
      | div => simp [hmul, hex1, hex2, hex3, hex4, hex5, hex6] at h
      | ok secrets6 =>
        cases hdv : pqxdh.HandshakeKeys.derive (Aeneas.Std.alloc.vec.Vec.deref secrets6) with
        | fail e => simp [hmul, hex1, hex2, hex3, hex4, hex5, hex6, hdv] at h
        | div => simp [hmul, hex1, hex2, hex3, hex4, hex5, hex6, hdv] at h
        | ok k =>
          simp only [hmul, hex1, hex2, hex3, hex4, hex5, hex6, hdv, Aeneas.Std.bind_tc_ok,
            bind_pure_left, Aeneas.Std.Result.ok.injEq] at h
          subst h
          simp only [hex1, hex2, hex3, hex4, hex5, hex6, hdv, Aeneas.Std.bind_tc_ok]

section GroupModelBridge

variable [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub]
  (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub) (privEnc : F → ECPriv)

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma pubOfBytes_pubBytes (p : ECPub) : pubOfBytes (pubBytes p) = p := by
  cases p with | mk k => cases k with | DjbPublicKey _ => rfl

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma pubOfSlice_pubSlice (p : ECPub) : pubOfSlice (getOk (pubSlice p)) = p := by
  simp [pubOfSlice, pubSlice, sliceOfKey, Aeneas.Std.lift, getOk, toKey,
    Aeneas.Std.Array.to_slice, pubOfBytes_pubBytes]

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma kpOfPair_public (p : ECPub × F) : (kpOfPair privEnc p).public_key = p.1 := rfl

omit [SampleableType F] in
lemma ecAgree_toSpec (hagree : ECAgreeSpec privEnc) (p : ECPub × F) (pk : ECPub) :
    ecAgree (kpOfPair privEnc p) pk = PQXDH.DH p.2 pk := by
  simp only [ecAgree, kpOfPair, hagree p.2 pk, pubOfSlice_pubSlice]

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma to_slice_of_toKey {s : Aeneas.Std.Slice Aeneas.Std.U8} {k : Key}
    (h : toKey s = some k) : Aeneas.Std.Array.to_slice k = s := by
  unfold toKey at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact absurd h (by simp)

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma getOk_pubSlice (p : ECPub) :
    getOk (pubSlice p) = Aeneas.Std.Array.to_slice (pubBytes p) := rfl

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
private lemma idPub_kpOfPair (p : ECPub × F) :
    (identityKeyPairOf (kpOfPair privEnc p)).identity_key.public_key = p.1 := rfl

lemma pqxdh_initiate_toKdf (hagree : ECAgreeSpec privEnc)
    (p₁ p₂ : ECPub × F) (ikB spk : ECPub) (opk : Option ECPub) (pqpk : PQPub)
    (r : Rand) {ss ct : Aeneas.Std.Slice Aeneas.Std.U8} {rest : Rand}
    {ssK : Key} {hk : pqxdh.HandshakeKeys}
    (henc : kem.KeyPublic.encapsulate P.cryptoRngInst pqpk r = .ok (.Ok (ss, ct), rest))
    (hssK : toKey ss = some ssK)
    (hhk : deriveHK (PQXDH.DH p₁.2 spk) (PQXDH.DH p₂.2 ikB) (PQXDH.DH p₂.2 spk)
      (Option.map (fun o => PQXDH.DH p₂.2 o) opk) ssK = .ok hk) :
    pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst
      { our_identity_key_pair := identityKeyPairOf (kpOfPair privEnc p₁)
        our_ephemeral_key_pair := kpOfPair privEnc p₂
        their_identity_key := { public_key := ikB }
        their_signed_pre_key := spk
        their_one_time_pre_key := opk
        their_ratchet_key := spk
        their_kyber_pre_key := pqpk
        self_session := false } r
      = .ok (.Ok { keys := hk, kyber_ciphertext := ct }, rest) := by
  have hd1 := hagree p₁.2 spk
  have hd2 := hagree p₂.2 ikB
  have hd3 := hagree p₂.2 spk
  have hssEq := to_slice_of_toKey hssK
  cases opk with
  | none =>
    have hhk' : (do
        let inp ← kdfInput
          (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₁.2 spk)))
          (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₂.2 ikB)))
          (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₂.2 spk))) none ss
        pqxdh.HandshakeKeys.derive inp) = Aeneas.Std.Result.ok hk := by
      rw [← hssEq]
      exact hhk
    simp only [pqxdh.pqxdh_initiate, identityKeyPairOf, identityKeyOf, kpOfPair,
      identity_key.IdentityKeyPair.impl.private_key,
      identity_key.IdentityKey.impl.public_key,
      core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      hd1, hd2, hd3, henc, getOk_pubSlice, as_ref_eq_ok, Aeneas.Std.bind_tc_ok]
    simp only [Aeneas.Std.uncurry_apply_pair, Aeneas.Std.bind_tc_ok]
    exact kdfInput_chain
      (γ := Aeneas.Std.core.result.Result pqxdh.InitiatorAgreement
        error.SignalProtocolError × Rand) _ _ _ none ss
      (fun k => Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Ok { keys := k, kyber_ciphertext := ct }, rest)) hhk'
  | some o =>
    have hd4 := hagree p₂.2 o
    have hhk' : (do
        let inp ← kdfInput
          (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₁.2 spk)))
          (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₂.2 ikB)))
          (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₂.2 spk)))
          (some (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₂.2 o)))) ss
        pqxdh.HandshakeKeys.derive inp) = Aeneas.Std.Result.ok hk := by
      rw [← hssEq]
      exact hhk
    simp only [pqxdh.pqxdh_initiate, identityKeyPairOf, identityKeyOf, kpOfPair,
      identity_key.IdentityKeyPair.impl.private_key,
      identity_key.IdentityKey.impl.public_key,
      core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      hd1, hd2, hd3, hd4, henc, getOk_pubSlice, as_ref_eq_ok, Aeneas.Std.bind_tc_ok]
    simp only [Aeneas.Std.uncurry_apply_pair, Aeneas.Std.bind_tc_ok]
    exact kdfInput_chain
      (γ := Aeneas.Std.core.result.Result pqxdh.InitiatorAgreement
        error.SignalProtocolError × Rand) _ _ _
      (some (Aeneas.Std.Array.to_slice (pubBytes (PQXDH.DH p₂.2 o)))) ss
      (fun k => Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Ok { keys := k, kyber_ciphertext := ct }, rest)) hhk'

omit [SampleableType F] in
lemma agree_pubSlice (hagree : ECAgreeSpec privEnc) (a : F) (pk : ECPub) :
    ∃ s, libsignal_core.curve.PrivateKey.calculate_agreement (privEnc a) pk = .ok (.Ok s) ∧
      pubSlice (PQXDH.DH a pk) = .ok s :=
  ⟨_, hagree a pk, rfl⟩

omit [SampleableType F] in
lemma pqxdh_accept_toKdf (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec)
    (q₁ q₂ : ECPub × F) (opkq : Option (ECPub × F)) (pqpk : PQKeyPair)
    (ikA ekA : ECPub) (ct : Aeneas.Std.Slice Aeneas.Std.U8)
    {ss : Aeneas.Std.Slice Aeneas.Std.U8} {ssK : Key} {hk : pqxdh.HandshakeKeys}
    (hdec : kem.KeySecret.decapsulate pqpk.secret_key ct = .ok (.Ok ss))
    (hssK : toKey ss = some ssK)
    (hhk : deriveHK (PQXDH.DH q₂.2 ikA) (PQXDH.DH q₁.2 ekA) (PQXDH.DH q₂.2 ekA)
      (Option.map (fun o => PQXDH.DH o.2 ekA) opkq) ssK = .ok hk) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := identityKeyPairOf (kpOfPair privEnc q₁)
        our_signed_pre_key_pair := kpOfPair privEnc q₂
        our_one_time_pre_key_pair := opkq.map (kpOfPair privEnc)
        our_kyber_pre_key_pair := pqpk
        their_identity_key := { public_key := ikA }
        their_ephemeral_key := ekA
        their_kyber_ciphertext := ct
        self_session := false }
      = .ok (.Ok hk) := by
  have hsk : sliceOfKey ssK = .ok ss := by
    unfold toKey at hssK
    split at hssK
    · simp only [Option.some.injEq] at hssK
      subst hssK
      rfl
    · exact absurd hssK (by simp)
  obtain ⟨s1, hg1, h1⟩ := agree_pubSlice privEnc hagree q₂.2 ikA
  obtain ⟨s2, hg2, h2⟩ := agree_pubSlice privEnc hagree q₁.2 ekA
  obtain ⟨s3, hg3, h3⟩ := agree_pubSlice privEnc hagree q₂.2 ekA
  cases opkq with
  | none =>
    simp only [Option.map_none, deriveHK, h1, h2, h3, hsk,
      Aeneas.Std.bind_tc_ok, pure] at hhk
    simp only [pqxdh.pqxdh_accept, hcanon ekA, identityKeyPairOf, identityKeyOf, kpOfPair,
      identity_key.IdentityKey.impl.public_key, identity_key.IdentityKeyPair.impl.private_key,
      core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      Option.map_none, if_true, Aeneas.Std.bind_tc_ok, hg1, hg2, hg3, hdec]
    trans ((kdfInput s1 s2 s3 none ss >>= pqxdh.HandshakeKeys.derive) >>=
      fun h => Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok h))
    · simp only [kdfInput, bind_assoc, Aeneas.Std.bind_tc_ok, pure]
    · rw [hhk]
      rfl
  | some o =>
    obtain ⟨s4, hg4, h4⟩ := agree_pubSlice privEnc hagree o.2 ekA
    simp only [Option.map_some, deriveHK, h1, h2, h3, h4, hsk,
      Aeneas.Std.bind_tc_ok, pure] at hhk
    simp only [pqxdh.pqxdh_accept, hcanon ekA, identityKeyPairOf, identityKeyOf, kpOfPair,
      identity_key.IdentityKey.impl.public_key, identity_key.IdentityKeyPair.impl.private_key,
      core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      Option.map_some, if_true, Aeneas.Std.bind_tc_ok, hg1, hg2, hg3, hg4, hdec]
    trans ((kdfInput s1 s2 s3 (some s4) ss >>= pqxdh.HandshakeKeys.derive) >>=
      fun h => Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok h))
    · simp only [kdfInput, bind_assoc, Aeneas.Std.bind_tc_ok, pure]
    · rw [hhk]
      rfl

lemma genOPK_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (hasOPK : Bool) :
    genOPK P hasOPK
      = Option.map (kpOfPair privEnc) <$> PQXDH.genOPK (F := F) gen hasOPK := by
  unfold ECKeygenSpec at hkeygen
  cases hasOPK <;> simp [genOPK, PQXDH.genOPK, hkeygen, Functor.map_map]

lemma setup_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (msg : Msg) :
    setup P msg
      = Prod.map (ukOfSpec privEnc) (tkOfSpec privEnc) <$>
          PQXDH.setup (specParams P F gen) msg := by
  unfold ECKeygenSpec at hkeygen
  simp only [setup, PQXDH.setup, hkeygen, specParams, map_bind, bind_map_left]
  rfl

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma publish_toSpec
    (rp : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S) :
    publish P (rpOfSpec privEnc rp) = PQXDH.publish (specParams P F gen) rp := by
  refine bind_congr fun σ => ?_
  rcases hopk : rp.opkB with _ | opk <;>
    simp [rpOfSpec, kpOfPair, kpOfKem, identityKeyPairOf, identityKeyOf, hopk, specParams]

lemma initiate_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal)
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg)
    (bundle : PreKeyBundle ECPub PQPub S IdC IdK) :
    initiate P (ukOfSpec privEnc uk) bundle
      = PQXDH.initiate (specParams P F gen) uk bundle := by
  have hkg : P.ecKeygen = kpOfPair privEnc <$> PQXDH.dhKeygen (F := F) gen := hkeygen
  simp only [initiate, PQXDH.initiate, ukOfSpec, specParams, hkg, bind_map_left,
    idPub_kpOfPair]
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
    simp only [runInitiate, runRes, pqkem, bind_assoc]
    refine bind_congr fun coins => ?_
    obtain ⟨ss, ct, rest, henc⟩ := hencTotal bundle.pqpkB.1 coins
    obtain ⟨ssK, hssK⟩ := Option.isSome_iff_exists.mp
      (encaps_toKey_isSome P.cryptoRngInst bundle.pqpkB.1 coins henc)
    obtain ⟨hk, hhk⟩ := hkdfTotal (PQXDH.DH uk.ikA.2 bundle.spkB.1)
      (PQXDH.DH a.2 uk.ikB) (PQXDH.DH a.2 bundle.spkB.1)
      (Option.map (fun o => PQXDH.DH a.2 o) (bundle.opkB.map Prod.fst)) ssK
    rw [pqxdh_initiate_toKdf P privEnc hagree uk.ikA a uk.ikB bundle.spkB.1
      (bundle.opkB.map Prod.fst) bundle.pqpkB.1 coins henc hssK hhk]
    have hmap : Option.map (fun o => PQXDH.DH a.2 o) (bundle.opkB.map Prod.fst)
        = bundle.opkB.map fun opk => PQXDH.DH a.2 opk.1 := by
      cases bundle.opkB <;> rfl
    rw [hmap] at hhk
    have hks : deriveKeys (PQXDH.DH uk.ikA.2 bundle.spkB.1) (PQXDH.DH a.2 uk.ikB)
        (PQXDH.DH a.2 bundle.spkB.1) (bundle.opkB.map fun opk => PQXDH.DH a.2 opk.1) ssK
        = .ok (rootKeyBytes hk, chainKeyBytes hk, pqrKeyBytes hk) := by
      simp only [deriveKeys, hhk, Aeneas.Std.bind_tc_ok]
      rfl
    simp [henc, hssK, hks, getOk, kpOfPair]
  · simp [hpin]

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
private lemma kpOfKem_public (pq : PQPub × PQPriv) : (kpOfKem pq).public_key = pq.1 := rfl

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
private lemma getRes_eq_none {α : Type}
    {r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α error.SignalProtocolError)}
    (h : ∀ x, r ≠ .ok (.Ok x)) : getRes r = none := by
  cases hr : r with
  | ok o =>
      cases o with
      | Ok x => exact absurd hr (h x)
      | Err e => simp [getRes]
  | fail e => simp [getRes]
  | div => simp [getRes]

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
private lemma bind_ne_ok {α β : Type} {x : Aeneas.Std.Result α}
    {f : α → Aeneas.Std.Result β} {y : β}
    (hf : ∀ a, x = .ok a → f a ≠ .ok y) : (x >>= f) ≠ .ok y := by
  cases hx : x with
  | ok a => simpa using hf a hx
  | fail e => simp
  | div => simp

omit [SampleableType F] in
private lemma pqxdh_accept_ne_ok_of_decaps (hagree : ECAgreeSpec privEnc)
    (hcanon : ECCanonicalSpec) (q₁ q₂ : ECPub × F) (opkq : Option (ECPub × F))
    (pqpk : PQKeyPair) (ikA ekA : ECPub) (ct : Aeneas.Std.Slice Aeneas.Std.U8)
    (hdec : ∀ ss, kem.KeySecret.decapsulate pqpk.secret_key ct ≠ .ok (.Ok ss))
    (hk : pqxdh.HandshakeKeys) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := identityKeyPairOf (kpOfPair privEnc q₁)
        our_signed_pre_key_pair := kpOfPair privEnc q₂
        our_one_time_pre_key_pair := opkq.map (kpOfPair privEnc)
        our_kyber_pre_key_pair := pqpk
        their_identity_key := { public_key := ikA }
        their_ephemeral_key := ekA
        their_kyber_ciphertext := ct
        self_session := false } ≠ .ok (.Ok hk) := by
  have hag : ∀ (a : F) (pk : ECPub),
      libsignal_core.curve.PrivateKey.calculate_agreement (privEnc a) pk
        = .ok (.Ok (getOk (pubSlice (PQXDH.DH a pk)))) := hagree
  have hcn : ∀ pk : ECPub,
      libsignal_core.curve.PublicKey.is_canonical pk = .ok true := hcanon
  simp only [pqxdh.pqxdh_accept, hcn, hag, kpOfPair, identityKeyPairOf, identityKeyOf,
    identity_key.IdentityKeyPair.impl.private_key,
    identity_key.IdentityKey.impl.public_key,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    Aeneas.Std.bind_tc_ok, if_true]
  refine bind_ne_ok fun i _ => ?_
  refine bind_ne_ok fun s _ => ?_
  refine bind_ne_ok fun secrets1 _ => ?_
  refine bind_ne_ok fun secrets2 _ => ?_
  refine bind_ne_ok fun secrets3 _ => ?_
  refine bind_ne_ok fun secrets4 _ => ?_
  cases opkq with
  | none =>
      simp only [Option.map_none]
      refine bind_ne_ok fun r3 hr3 => ?_
      cases r3 with
      | Ok ss => exact absurd hr3 (hdec ss)
      | Err e => simp
  | some o =>
      simp only [Option.map_some]
      refine bind_ne_ok fun r3 _ => ?_
      cases r3 with
      | Ok v =>
          simp only [Aeneas.Std.bind_tc_ok]
          refine bind_ne_ok fun secrets5 _ => ?_
          refine bind_ne_ok fun r4 hr4 => ?_
          cases r4 with
          | Ok ss => exact absurd hr4 (hdec ss)
          | Err e => simp
      | Err e =>
          simp only [Aeneas.Std.bind_tc_ok]
          cases hf : error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e <;>
            simp_all

lemma accept_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hkdfTotal : DeriveKeysTotal)
    (rp : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S)
    (im : InitialMessage ECPub CT C IdC IdK) :
    accept P (rpOfSpec privEnc rp) im = PQXDH.accept (specParams P F gen) rp im := by
  simp only [accept, PQXDH.accept, rpOfSpec, specParams, kpOfPair_public, kpOfKem_public,
    idPub_kpOfPair, Option.map_map, Function.comp_def]
  by_cases hguard : im.idSPK ≠ P.idEC rp.spkB.1 ∨ im.idPQPK ≠ P.idKEM rp.pqpkB.1 ∨
      im.idOPK ≠ Option.map (fun x => P.idEC x.1) rp.opkB
  · simp [hguard]
  · simp only [hguard, if_false]
    refine bind_congr fun _ => ?_
    simp only [pqkem, pure_bind]
    cases hdec : kem.KeySecret.decapsulate rp.pqpkB.2 im.ct with
    | ok dr =>
        cases dr with
        | Ok ss =>
            obtain ⟨ssK, hssK⟩ := Option.isSome_iff_exists.mp
              (decaps_toKey_isSome rp.pqpkB.2 im.ct hdec)
            obtain ⟨hk, hhk⟩ := hkdfTotal (PQXDH.DH rp.spkB.2 im.ikA)
              (PQXDH.DH rp.ikB.2 im.ekA) (PQXDH.DH rp.spkB.2 im.ekA)
              (Option.map (fun o => PQXDH.DH o.2 im.ekA) rp.opkB) ssK
            have hacc := pqxdh_accept_toKdf privEnc hagree hcanon rp.ikB rp.spkB rp.opkB
              (kpOfKem rp.pqpkB) im.ikA im.ekA im.ct hdec hssK hhk
            have hks : deriveKeys (PQXDH.DH rp.spkB.2 im.ikA) (PQXDH.DH rp.ikB.2 im.ekA)
                (PQXDH.DH rp.spkB.2 im.ekA)
                (Option.map (fun o => PQXDH.DH o.2 im.ekA) rp.opkB) ssK
                = .ok (rootKeyBytes hk, chainKeyBytes hk, pqrKeyBytes hk) := by
              simp only [deriveKeys, hhk, Aeneas.Std.bind_tc_ok]
              rfl
            simp only [runAccept, getRes, hacc, hssK, hks, getOk, Option.bind]
            rfl
        | Err e =>
            rw [runAccept, getRes_eq_none fun keys =>
              pqxdh_accept_ne_ok_of_decaps privEnc hagree hcanon rp.ikB rp.spkB rp.opkB
                (kpOfKem rp.pqpkB) im.ikA im.ekA im.ct (by simp [kpOfKem, hdec]) keys]
            simp [getRes]
    | fail e =>
        rw [runAccept, getRes_eq_none fun keys =>
          pqxdh_accept_ne_ok_of_decaps privEnc hagree hcanon rp.ikB rp.spkB rp.opkB
            (kpOfKem rp.pqpkB) im.ikA im.ekA im.ct (by simp [kpOfKem, hdec]) keys]
        simp [getRes]
    | div =>
        rw [runAccept, getRes_eq_none fun keys =>
          pqxdh_accept_ne_ok_of_decaps privEnc hagree hcanon rp.ikB rp.spkB rp.opkB
            (kpOfKem rp.pqpkB) im.ikA im.ekA im.ct (by simp [kpOfKem, hdec]) keys]
        simp [getRes]

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma confirm_toSpec [DecidableEq Msg]
    (ctx : SessionContext ECPub PQPub Msg Key) (conf : C) :
    confirm P ctx conf = PQXDH.confirm (specParams P F gen) ctx conf := rfl

lemma initiator_init_toSpec [DecidableEq Msg]
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg) :
    (initiator P).init (ukOfSpec privEnc uk)
      = Party.InitResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (PQXDH.initiator (specParams P F gen)).init uk := by
  simp only [initiator, PQXDH.initiator, map_pure, Party.InitResult.map, Sum.map_inl]

lemma initiator_step_toSpec [DecidableEq Msg]
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal)
    (st : PQXDH.InitiatorParameters F ECPub SPK Msg ⊕
      SessionContext ECPub PQPub Msg Key ⊕ Key)
    (w : Message ECPub PQPub CT S C IdC IdK) :
    (initiator P).step (Sum.map (ukOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (PQXDH.initiator (specParams P F gen)).step st w := by
  rcases st with p | ctx | k
  · cases w with
    | bundle b =>
        simp only [initiator, PQXDH.initiator, Sum.map_inl,
          initiate_toSpec P gen privEnc hkeygen hagree hencTotal hkdfTotal p b, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ⟨im, ctx⟩ <;> simp [Party.StepResult.map]
    | initial im => simp [initiator, PQXDH.initiator, Party.StepResult.map]
    | confirmation c => simp [initiator, PQXDH.initiator, Party.StepResult.map]
  · cases w with
    | bundle b => simp [initiator, PQXDH.initiator, Party.StepResult.map]
    | initial im => simp [initiator, PQXDH.initiator, Party.StepResult.map]
    | confirmation conf =>
        simp only [initiator, PQXDH.initiator, Sum.map_inr, id_eq]
        rw [confirm_toSpec (F := F) P gen ctx conf]
        cases PQXDH.confirm (specParams P F gen) ctx conf <;> simp [Party.StepResult.map]
  · cases w <;> simp [initiator, PQXDH.initiator, Party.StepResult.map]

lemma initiator_output_toSpec [DecidableEq Msg]
    (st : PQXDH.InitiatorParameters F ECPub SPK Msg ⊕
      SessionContext ECPub PQPub Msg Key ⊕ Key) :
    (initiator P).output (Sum.map (ukOfSpec privEnc) id st)
      = (PQXDH.initiator (specParams P F gen)).output st := by
  rcases st with p | ctx | k <;> rfl

lemma recipient_init_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hkeygen : ECKeygenSpec P gen privEnc) (hK : PQKeygenSpec P) (hasOPK : Bool)
    (tk : PQXDH.RecipientIdentity F ECPub SPK SSK S) :
    (recipient P hasOPK).init (tkOfSpec privEnc tk)
      = Party.InitResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (PQXDH.recipient (specParams P F gen) hasOPK).init tk := by
  unfold PQKeygenSpec at hK
  simp only [recipient, PQXDH.recipient, genOPK_toSpec P gen privEnc hkeygen hasOPK,
    specParams, tkOfSpec, map_bind, bind_map_left]
  rw [hK]
  simp only [bind_map_left]
  refine bind_congr fun opkB => ?_
  refine bind_congr fun pqpkB => ?_
  have hrp : (⟨identityKeyPairOf (kpOfPair privEnc tk.ikB), tk.sigkB,
      kpOfPair privEnc tk.spkB, tk.spkSigB, Option.map (kpOfPair privEnc) opkB,
      kpOfKem pqpkB⟩ : RecipientParameters SPK SSK S)
      = rpOfSpec privEnc ⟨tk.ikB, tk.sigkB, tk.spkB, tk.spkSigB, opkB, pqpkB⟩ := rfl
  rw [hrp, publish_toSpec]
  refine bind_congr fun bundle => ?_
  simp [Party.InitResult.map, rpOfSpec]

lemma recipient_step_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool)
    (st : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S ⊕ Key)
    (w : Message ECPub PQPub CT S C IdC IdK) :
    (recipient P hasOPK).step (Sum.map (rpOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (PQXDH.recipient (specParams P F gen) hasOPK).step st w := by
  rcases st with rp | k
  · cases w with
    | bundle b => simp [recipient, PQXDH.recipient, Party.StepResult.map]
    | initial im =>
        simp only [recipient, PQXDH.recipient, Sum.map_inl,
          accept_toSpec P gen privEnc hagree hcanon hkdfTotal rp im, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ctx <;> simp [Party.StepResult.map, specParams]
    | confirmation c => simp [recipient, PQXDH.recipient, Party.StepResult.map]
  · cases w <;> simp [recipient, PQXDH.recipient, Party.StepResult.map]

lemma recipient_output_toSpec [DecidableEq IdC] [DecidableEq IdK] (hasOPK : Bool)
    (st : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S ⊕ Key) :
    (recipient P hasOPK).output (Sum.map (rpOfSpec privEnc) id st)
      = (PQXDH.recipient (specParams P F gen) hasOPK).output st := by
  rcases st with rp | k <;> rfl

variable {msg : Msg} {hasOPK : Bool}

def _root_.AKE.UAKE.Adversary.toSpecFull
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (gen : ECPub) (privEnc : F → ECPriv)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (PQXDH.uakeInitiator (specParams P F gen) msg hasOPK) where
  State := A.State
  challenge := fun uk w => A.challenge (ukOfSpec privEnc uk) w
  post := A.post

lemma opensAtMost_toSpec
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) {q : ℕ}
    (hq : A.OpensAtMost q) : (A.toSpecFull gen privEnc).OpensAtMost q :=
  ⟨fun uk w => hq.1 (ukOfSpec privEnc uk) w, hq.2⟩

lemma initiator_sim [DecidableEq Msg]
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal) :
    Party.Sim (PQXDH.initiator (specParams P F gen)) (initiator P)
      (ukOfSpec privEnc) (Sum.map (ukOfSpec privEnc) id) where
  init_eq := initiator_init_toSpec P gen privEnc
  step_eq := initiator_step_toSpec P gen privEnc hkeygen hagree hencTotal hkdfTotal
  output_eq := initiator_output_toSpec P gen privEnc

lemma recipient_sim [DecidableEq IdC] [DecidableEq IdK]
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hK : PQKeygenSpec P)
    (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool) :
    Party.Sim (PQXDH.recipient (specParams P F gen) hasOPK) (recipient P hasOPK)
      (tkOfSpec privEnc) (Sum.map (rpOfSpec privEnc) id) where
  init_eq := recipient_init_toSpec P gen privEnc hkeygen hK hasOPK
  step_eq := recipient_step_toSpec P gen privEnc hagree hcanon hkdfTotal hasOPK
  output_eq := recipient_output_toSpec P gen privEnc hasOPK

lemma exp_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hK : PQKeygenSpec P)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A = UAKE.Exp ProbCompRuntime.probComp.toProbCompLift (A.toSpecFull gen privEnc) := by
  have hsetup : (uakeInitiator P msg hasOPK).setup
      = Prod.map (ukOfSpec privEnc) (tkOfSpec privEnc) <$>
        (PQXDH.uakeInitiator (specParams P F gen) msg hasOPK).setup :=
    setup_toSpec P gen privEnc hkeygen msg
  exact (UAKE.Exp_transport ProbCompRuntime.probComp.toProbCompLift
    (proto₁ := PQXDH.uakeInitiator (specParams P F gen) msg hasOPK)
    (proto₂ := uakeInitiator P msg hasOPK)
    (initiator_sim P gen privEnc hkeygen hagree hencTotal hkdfTotal)
    (recipient_sim P gen privEnc hkeygen hagree hcanon hK hkdfTotal hasOPK) rfl hsetup A).trans rfl

lemma advantage_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hK : PQKeygenSpec P)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.advantage ProbCompRuntime.probComp A = UAKE.advantage ProbCompRuntime.probComp (A.toSpecFull gen privEnc) := by
  unfold UAKE.advantage
  rw [exp_toSpec gen privEnc hkeygen hagree hcanon hK hencTotal hkdfTotal A]

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma kdfPRF_specParams {P : Parameters Rand SPK SSK S C Msg IdC IdK} :
    PQXDH.kdfPRF (specParams P F gen) = kdfPRF := rfl

lemma kdfPRFDH_advantage_toSpec {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc)
    (D : PRFScheme.PRFAdversary (ECPub × ECPub × Option ECPub × Key) (Key × Key × Key)) :
    (PQXDH.kdfPRFDH (specParams P F gen)).prfAdvantage D
      = (kdfPRFDH P).prfAdvantage D := by
  have hkg : P.ecKeygen = kpOfPair privEnc <$> PQXDH.dhKeygen (F := F) gen := hkeygen
  have hreal : (PQXDH.kdfPRFDH (specParams P F gen)).prfRealExp D
      = (kdfPRFDH P).prfRealExp D := by
    unfold PRFScheme.prfRealExp
    rw [show (kdfPRFDH P).keygen = P.ecKeygen from rfl, hkg,
      show PQXDH.dhKeygen (F := F) gen = (do let a ← $ᵗ F; pure (a • gen, a)) from rfl]
    simp only [bind_map_left, bind_assoc, pure_bind]
    exact bind_congr fun c => rfl
  unfold PRFScheme.prfAdvantage
  rw [hreal]

lemma nominalDDHExpReal_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECPub) :
    DiffieHellman.nominalDDHExpReal P.ecKeygen
        (fun kp : ECKeyPair => kp.public_key) ecAgree D
      = DiffieHellman.nominalDDHExpReal (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst (fun kp pk => kp.2 • pk) D := by
  have hkg : P.ecKeygen = kpOfPair privEnc <$> PQXDH.dhKeygen (F := F) gen := hkeygen
  unfold DiffieHellman.nominalDDHExpReal
  rw [hkg, show PQXDH.dhKeygen (F := F) gen
    = DiffieHellman.groupKeygen (F := F) gen from rfl]
  simp only [bind_map_left]
  refine bind_congr fun kpA => ?_
  refine bind_congr fun kpB => ?_
  simp only [kpOfPair_public, ecAgree_toSpec privEnc hagree, PQXDH.DH]

lemma nominalDDHExpRand_toSpec (hkeygen : ECKeygenSpec P gen privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECPub) :
    DiffieHellman.nominalDDHExpRand P.ecKeygen
        (fun kp : ECKeyPair => kp.public_key) D
      = DiffieHellman.nominalDDHExpRand (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst D := by
  have hkg : P.ecKeygen = kpOfPair privEnc <$> PQXDH.dhKeygen (F := F) gen := hkeygen
  unfold DiffieHellman.nominalDDHExpRand
  rw [hkg, show PQXDH.dhKeygen (F := F) gen
    = DiffieHellman.groupKeygen (F := F) gen from rfl]
  simp only [bind_map_left]
  exact bind_congr fun kpA => bind_congr fun kpB => bind_congr fun kpC => rfl

lemma ddh_advantage_toSpec {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (D : _root_.DiffieHellman.DDHAdversary F ECPub) :
    _root_.DiffieHellman.ddhDistAdvantage gen D
      = DiffieHellman.nominalDDHDistAdvantage P.ecKeygen
          (fun kp : ECKeyPair => kp.public_key) ecAgree (D gen) := by
  rw [DiffieHellman.ddhDistAdvantage_eq_nominalDDHDistAdvantage]
  unfold DiffieHellman.nominalDDHDistAdvantage
  rw [nominalDDHExpReal_toSpec P gen privEnc hkeygen hagree (D gen),
    nominalDDHExpRand_toSpec P gen privEnc hkeygen (D gen)]

end GroupModelBridge

end

end PQXDH.Aeneas.Full
