/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.SecurityLemmas
import PQXDH.Aeneas.Simplified.UAKE.Assumptions
import PQXDH.Spec.UAKE.Security

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

noncomputable section

variable {SPK SSK S C Msg IdC IdK : Type}

theorem uakeInitiator_secure_pq
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECKey) (_ : Module F ECKey)
      (gen : ECKey) (privEnc : F → Bytes 32#usize),
      ECGroupModel P gen privEnc)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hkemCorrect : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : (pqkem P).IND_CCA_Adversary,
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × ECKey × Option ECKey)
        (Key × Key × Key),
      kdfPRF.prfAdvantage D ≤ εkdf) :
    UAKE.advantage ProbCompRuntime.probComp A ≤ 3 * εsig + q * (εkem + 3 * εaead + εkdf) := by
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  rw [advantage_toSpec gen privEnc hM encapsTotalAll hkdfTotal A]
  exact _root_.PQXDH.uakeInitiator_secure_pq (specParams P F gen) msg hasOPK hidKEM
    (A.toSpec gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εkem εaead εkdf hverifyDet hkemCorrect hsig hkem haead
    (fun D => by rw [kdfPRF_specParams]; exact hkdf D)

theorem uakeInitiator_secure_dh
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECKey) (_ : Module F ECKey)
      (gen : ECKey) (privEnc : F → Bytes 32#usize),
      ECGroupModel P gen privEnc)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.NominalDDHAdversary ECKey,
      DiffieHellman.nominalDDHDistAdvantage P.ecKeygen pqxdh.KeyPair.public_key
        x25519DH D ≤ εddh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × Option ECKey × SS)
        (Key × Key × Key),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage ProbCompRuntime.probComp A ≤ εsig + q * (εddh + εaead + εkdf) := by
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  rw [advantage_toSpec gen privEnc hM encapsTotalAll hkdfTotal A]
  exact _root_.PQXDH.uakeInitiator_secure_dh (specParams P F gen) msg hasOPK hidKEM
    (A.toSpec gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εddh εaead εkdf hverifyDet hsig
    (fun D => by
      have h := hddh (D gen)
      rw [← ddh_advantage_toSpec gen privEnc hM D] at h
      exact h)
    haead
    (fun D => by rw [kdfPRFDH_advantage_toSpec gen privEnc hM D]; exact hkdf D)

end

end PQXDH.Aeneas.Simplified
