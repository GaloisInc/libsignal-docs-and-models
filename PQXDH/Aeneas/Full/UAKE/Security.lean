/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.SecurityLemmas
import PQXDH.Spec.UAKE.Security

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

theorem uakeInitiator_secure_pq
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECPub) (_ : Module F ECPub)
      (gen : ECPub) (privEnc : F → ECPriv),
      ECGroupModel P gen privEnc)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECPub ⊕ PQPub) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hkemCorrect : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : (pqkem P).IND_CCA_Adversary,
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hK : KemPairModel P)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECPub × ECPub × ECPub × Option ECPub)
        (Key × Key × Key),
      kdfPRF.prfAdvantage D ≤ εkdf) :
    UAKE.advantage ProbCompRuntime.probComp A ≤ 3 * εsig + q * (εkem + 3 * εaead + εkdf) := by
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  rw [advantage_toSpec gen privEnc hM.keygen_eq hM.agree_eq hM.canonical_eq hK.keygen_eq
    hencTotal hkdfTotal A]
  exact PQXDH.uakeInitiator_secure_pq (specParams P F gen) msg hasOPK hidKEM
    (A.toSpecFull gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εkem εaead εkdf hverifyDet hkemCorrect hsig hkem haead
    (fun D => by rw [kdfPRF_specParams]; exact hkdf D)

theorem uakeInitiator_secure_dh
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECPub) (_ : Module F ECPub)
      (gen : ECPub) (privEnc : F → ECPriv),
      ECGroupModel P gen privEnc)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECPub ⊕ PQPub) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.NominalDDHAdversary ECPub,
      DiffieHellman.nominalDDHDistAdvantage P.ecKeygen
        (fun kp : ECKeyPair => kp.public_key) ecAgree D ≤ εddh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hK : KemPairModel P)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECPub × ECPub × Option ECPub × Key)
        (Key × Key × Key),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage ProbCompRuntime.probComp A ≤ εsig + q * (εddh + εaead + εkdf) := by
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  rw [advantage_toSpec gen privEnc hM.keygen_eq hM.agree_eq hM.canonical_eq hK.keygen_eq
    hencTotal hkdfTotal A]
  exact PQXDH.uakeInitiator_secure_dh (specParams P F gen) msg hasOPK hidKEM
    (A.toSpecFull gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εddh εaead εkdf hverifyDet hsig
    (fun D => by
      have h := hddh (D gen)
      rw [← ddh_advantage_toSpec gen privEnc hM.keygen_eq hM.agree_eq D] at h
      exact h)
    haead
    (fun D => by rw [kdfPRFDH_advantage_toSpec gen privEnc hM.keygen_eq D]; exact hkdf D)

end

end PQXDH.Aeneas.Full
