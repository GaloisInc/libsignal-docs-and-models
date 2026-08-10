/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.UAKE.SecurityLemmas

/-!
# Security Theorems for PQXDH Spec-based Implementation

We model UAKE security of the spec by bounding the adversary's advantage in the
UAKE game based on its advantage in the security games of the underlying
cryptographic primitives.

Model simplifications
* **Unilateral authentication:** UAKE is unilaterally authenticated. In
  principle, it should be possible to model a protocol in both directions to
  show multilateral authentication. However, we model security only for the
  "Bob authenticates to Alice" direction. This is because UAKE security
  requires explicit authentication, and Alice's authentication to Bob is
  implicit via the adversary being unable to compute the DH output, rather than
  relying on Alice's signature (she signs nothing).
* **SUF-CMA signature (not EUF-CMA):** Since UAKE is a
  transcript-matching-style definition, our security theorems are subject to
  harmless but definition-breaking "no-match" attacks on the signature scheme.
  See Li & Schäge, "No-Match Attacks and Robust Partnering Definitions" (ACM CCS
  2017) for a reference on attacks of this kind.
* **PQ-secure signature scheme:** In order to re-use our AKE definition in the
  post-quantum case, we assume here that the signature scheme is *still
  secure*, even in the post-quantum setting. In reality, PQXDH uses an EC-based
  signature scheme, which is insecure against a quantum adversary. This is not
  a problem for the protocol, since the desired PQ security is security against
  HNDL attacks, which requires only secrecy, not integrity. However, UAKE
  cannot capture secrecy alone. A better way to model this kind of security
  would be to use a secrecy-only definition.
* **Injective key→ID maps:** We assume that the function mapping KEM keys to
  identifiers is injective. Section 4.13 of the spec contains the weaker
  requirement that "collisions are unlikely". Modeling the maps as collision
  resistant would be an improvement, since it would allow a hash of the key to
  be used, but we leave that as a future improvement.
* **DH assumption:** We currently state our DH assumption in the non-PQ theorem
  as DDH, whereas the spec assumes GapDH. The security proof probably won't go
  through without moving to GapDH, so we should switch this, but GapDH is not
  currently in VCV-io. We formalize it in the `ToVCVio` module, but haven't
  incorporated it here, yet.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

/-- Top-level UAKE security theorem for spec-based PQXDH, assuming the
  underlying DH key exchange is hard to break. This models UAKE security in the
  non-PQ setting. -/
theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq SS] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- We assume the function mapping KEM keys to key identifiers is injective. -/
    (hidKEM : Function.Injective P.idKEM)
    /- Any UAKE adversary who starts at most q sessions with its T oracle. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εddh εaead εkdf : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- Bound on an adversary's advantage in forging a signature.
      * DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
        just EUF-CMA. This is required to avoid (harmless) LS'17-style
        "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    /- Bound on an adversary's advantage in the DH security game. -/
    (hddh : ∀ D : DiffieHellman.DDHAdversary F G,
      DiffieHellman.ddhDistAdvantage P.gen D ≤ εddh)
    /- Bound on the adversary's advantage forging an AEAD ciphertext. -/
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- Bound on an adversary's distinguishing advantage for the KDF, modeled as
      a PRF.
      * MODEL SIMPLIFICATION: We model the KDF as a PRF. Since we key our KDF
        using DH group elements, we must also assume that the KDF is secure
        when keyed with one of these, rather than a random bit string. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    UAKE.advantage ProbCompRuntime.probComp A ≤ εsig + q * (εddh + εaead + εkdf) := sorry

/-- Top-level UAKE security theorem for spec-based PQXDH, making no assumptions
  about the underlying DH key exchange, but assuming the KEM is secure. This
  models UAKE security in the PQ setting. -/
theorem uakeInitiator_secure_pq
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS] [DecidableEq SS]
    [Inhabited S] [Inhabited SSK] [Inhabited PQSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- We assume the function mapping KEM keys to key identifiers is injective. -/
    (hidKEM : Function.Injective P.idKEM)
    /- Any UAKE adversary who starts at most q sessions with its T oracle. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εkem εaead εkdf : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- We assume the KEM is perfectly correct. -/
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    /- Bound on an adversary's advantage in forging a signature.
      * DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
        just EUF-CMA. This is required to avoid (harmless) LS'17-style
        "no-match" attacks because we use a transcript-matching AKE definition.
      * MODEL SIMPLIFICATION: In order to re-use our AKE definition, we assume
        here that the signature scheme is *still secure*, even in the
        post-quantum setting. In reality, PQXDH uses an EC-based signature
        scheme, which is insecure against a quantum adversary. This is not a
        problem for the protocol, since the desired PQ security is security
        against HNDL attacks, which requires only secrecy, not integrity.
        However, UAKE cannot capture secrecy alone. A better way to model this
        kind of security would be to use a secrecy-only definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    /- Bound on an adversary's advantage in the IND-CCA game for the KEM. -/
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    /- Bound on the adversary's advantage forging an AEAD ciphertext. -/
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- Bound on an adversary's distinguishing advantage for the KDF, modeled as
      a PRF.
      * MODEL SIMPLIFICATION: We model the KDF as a PRF keyed by the KEM
        secret. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      (kdfPRF P).prfAdvantage D ≤ εkdf) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    UAKE.advantage ProbCompRuntime.probComp A ≤
      3 * εsig + q * (εkem + 3 * εaead + εkdf) := sorry

end PQXDH
