/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.SecurityLemmas
import PQXDH.Spec.UAKE.Security

/-!
# Security Theorems for the High-fidelity Aeneas Extraction

UAKE security of the extracted scheme, by reduction to the Spec theorems:
under the group and KEM-pairing models, the extracted scheme's advantage
equals that of the Spec scheme instantiated with the extracted primitives, so
the Spec bounds apply.

Deviations from a pure "extracted code as UAKE" statement
* **Clean-group model:** both theorems assume some clean-group model for the
  opaque curve25519 primitives (the `hGroupModel` hypothesis). This is a model
  idealization, not a believed-true fact; see `SecurityDefs.lean`.
* **KEM pairing:** the `hK` hypothesis assumes the KEM key generator is the
  paired form of the extracted KEM's key generation.
* **Totality hypotheses:** `hencTotal` assumes the extracted encapsulation
  never fails, and `hkdfTotal` assumes the extracted KDF never fails.
* **Inherited Spec simplifications:** the Spec theorems this reduces to are
  still sorry-backed and carry their own simplifications (SUF-CMA signatures,
  the KDF as a PRF); see `PQXDH.Spec.UAKE.Security`. In particular, the PQ
  theorem inherits the modeling of PQ security as "UAKE security with
  compromised DH key exchange," which assumes a PQ-secure signature scheme;
  see the "PQ security as UAKE with PQ signature" bullet there. The
  KDF-as-a-PRF modeling may also change: the previous CryptoVerif analysis
  models the KDF as a random oracle in the non-PQ case, and completing the
  Spec proofs may require the same; see the "KDF modeled as a PRF in non-PQ
  security" bullet there.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

/-- Top-level UAKE security theorem for the high-fidelity extraction, making no
  assumptions about the underlying DH key exchange, but assuming the KEM is
  secure. This models UAKE security in the PQ setting.
  * MODEL GAP: We model PQ security as "UAKE security with compromised DH key
    exchange," which is not the HNDL resistance PQXDH actually targets in the
    PQ setting and requires assuming a PQ-secure signature scheme. See the
    MODEL GAP caveat on `PQXDH.uakeInitiator_secure_pq` in
    `PQXDH.Spec.UAKE.Security` for details. -/
theorem uakeInitiator_secure_pq
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- We assume the function mapping KEM keys to key identifiers is injective. -/
    (hidKEM : Function.Injective P.idKEM)
    /- MODEL IDEALIZATION: some clean-group model relates the opaque curve25519
      primitives to the Spec model's group operations. See `SecurityDefs.lean`
      for why this is an idealization rather than a believed-true fact. -/
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECPub) (_ : Module F ECPub)
      (gen : ECPub) (privEnc : F → ECPriv),
      ECGroupModel P gen privEnc)
    /- Any UAKE adversary who starts at most q sessions with its T oracle. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εkem εaead εkdf εpk : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : SPK) (m : ECPub ⊕ PQPub) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- We assume the KEM is perfectly correct. -/
    (hkemCorrect : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    /- Bound on an adversary's advantage in forging a signature.
      * DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
        just EUF-CMA. This is required to avoid (harmless) LS'17-style
        "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    /- Bound on an adversary's advantage in the IND-CCA game for the KEM. -/
    (hkem : ∀ B : (pqkem P).IND_CCA_Adversary,
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    /- Bound on the adversary's advantage forging an AEAD ciphertext. -/
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- The KEM key generator is the paired form of the extracted KEM's key
      generation. -/
    (hK : KemPairModel P)
    /- The extracted ML-KEM encapsulation succeeds on every input. This depends
      on the parameters' RNG instance, so it is a hypothesis rather than a
      global assumption. -/
    (hencTotal : EncapsTotalAll P)
    /- The extracted KDF is total. The reduction needs this to identify the
      extracted KDF with the Spec model's KDF function. -/
    (hkdfTotal : DeriveKeysTotal)
    /- Bound on an adversary's distinguishing advantage for the KDF, modeled as
      a PRF.
      * MODEL SIMPLIFICATION: We model the KDF as a PRF keyed by the KEM
        secret. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECPub × ECPub × ECPub × Option ECPub)
        (Key × Key × Key),
      kdfPRF.prfAdvantage D ≤ εkdf)
    /- Bound on the probability of guessing the public key output by the KEM's
      key generation. This bounds KEM public-key collisions and predictions
      across T-oracle sessions, which otherwise seem to break UAKE security. -/
    (hpk : ∀ pk : PQPub, (Pr[= pk | Prod.fst <$> (pqkem P).keygen]).toReal ≤ εpk) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    UAKE.advantage ProbCompRuntime.probComp A ≤
      εsig + 2 * q * (εkem + εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk := by
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  rw [advantage_toSpec gen privEnc hM.keygen_eq hM.agree_eq hM.canonical_eq hK.keygen_eq
    hencTotal hkdfTotal A]
  exact PQXDH.uakeInitiator_secure_pq (specParams P F gen) msg hasOPK hidKEM
    (A.toSpecFull gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εkem εaead εkdf εpk hverifyDet hkemCorrect hsig hkem haead
    (fun D => by rw [kdfPRF_specParams]; exact hkdf D)
    hpk

/-- Top-level UAKE security theorem for the high-fidelity extraction, assuming
  the underlying DH key exchange is hard to break. This models UAKE security
  in the non-PQ setting. -/
theorem uakeInitiator_secure_dh
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- We assume the function mapping KEM keys to key identifiers is injective. -/
    (hidKEM : Function.Injective P.idKEM)
    /- MODEL IDEALIZATION: some clean-group model relates the opaque curve25519
      primitives to the Spec model's group operations. See `SecurityDefs.lean`
      for why this is an idealization rather than a believed-true fact. -/
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECPub) (_ : Module F ECPub)
      (gen : ECPub) (privEnc : F → ECPriv),
      ECGroupModel P gen privEnc)
    /- Any UAKE adversary who starts at most q sessions with its T oracle. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εgap εaead εkdf εpk : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : SPK) (m : ECPub ⊕ PQPub) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- Bound on an adversary's advantage in forging a signature.
      * DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
        just EUF-CMA. This is required to avoid (harmless) LS'17-style
        "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    /- Bound on an adversary's advantage in the GapDH security game, stated
      over any field and group structure realizing the clean-group model
      (the witnesses of `hGroupModel` are not in scope for this hypothesis,
      so it quantifies over all of them). -/
    (hgap : ∀ (F : Type) [Field F] [SampleableType F]
        [AddCommGroup ECPub] [Module F ECPub]
        (gen : ECPub) (privEnc : F → ECPriv), ECGroupModel P gen privEnc →
      ∀ D : DiffieHellman.GapDHAdversary F ECPub,
        DiffieHellman.gapDHAdvantage gen D ≤ εgap)
    /- Bound on the adversary's advantage forging an AEAD ciphertext. -/
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- The KEM key generator is the paired form of the extracted KEM's key
      generation. -/
    (hK : KemPairModel P)
    /- The extracted ML-KEM encapsulation succeeds on every input. This depends
      on the parameters' RNG instance, so it is a hypothesis rather than a
      global assumption. -/
    (hencTotal : EncapsTotalAll P)
    /- The extracted KDF is total. The reduction needs this to identify the
      extracted KDF with the Spec model's KDF function. -/
    (hkdfTotal : DeriveKeysTotal)
    /- Bound on an adversary's distinguishing advantage for the KDF, modeled as
      a PRF.
      * MODEL SIMPLIFICATION: We model the KDF as a PRF. Since we key our KDF
        using DH values, we must also assume that the KDF is secure when keyed
        with one of these, rather than a random bit string.
      * NOTE: It may be necessary to model this as a random oracle instead of
        a PRF; see the NOTE on the `hkdf` hypothesis of
        `PQXDH.uakeInitiator_secure_dh` in `PQXDH.Spec.UAKE.Security`. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECPub × ECPub × Option ECPub × Key)
        (Key × Key × Key),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf)
    /- Bound on the probability of guessing the public key output by the KEM's
      key generation. This bounds KEM public-key collisions and predictions
      across T-oracle sessions, which otherwise seem to break UAKE security. -/
    (hpk : ∀ pk : PQPub, (Pr[= pk | Prod.fst <$> (pqkem P).keygen]).toReal ≤ εpk) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    UAKE.advantage ProbCompRuntime.probComp A ≤
      εsig + 2 * q * (εgap + 2 * εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk := by
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  rw [advantage_toSpec gen privEnc hM.keygen_eq hM.agree_eq hM.canonical_eq hK.keygen_eq
    hencTotal hkdfTotal A]
  exact PQXDH.uakeInitiator_secure_dh (specParams P F gen) msg hasOPK hidKEM
    (A.toSpecFull gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εgap εaead εkdf εpk hverifyDet hsig
    (hgap F gen privEnc hM)
    haead
    (fun D => by rw [kdfPRFDH_advantage_toSpec gen privEnc hM.keygen_eq D]; exact hkdf D)
    hpk

end

end PQXDH.Aeneas.Full
