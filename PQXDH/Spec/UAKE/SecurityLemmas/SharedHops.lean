/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.UAKE.SecurityLemmas.Games

/-!
# Shared Security Hops

Hops 1 through 4 of the security proofs, used by both the DH and the PQ
security theorems in `Security.lean`: the forgery/indistinguishability
split, the union bound over forgery causes, the SUF-CMA reduction, and the
KEM public-key guessing bound. See `SecurityLemmas.lean` for the overall
map.

The lemma statements and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- Hop 1: `UAKE.Exp` and `indistExp` agree except on the forgery branch,
  where the former returns `true` and the latter flips a fair coin, so their
  output distributions differ by at most (half) the forgery probability, and
  the UAKE advantage is bounded by `forgeProb` plus `indistAdvantage`.
  Purely probabilistic; uses no cryptographic hypotheses. -/
lemma advantage_le_forgeProb_add_indistAdvantage
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.advantage ProbCompRuntime.probComp A ≤
      forgeProb P msg hasOPK A + indistAdvantage P msg hasOPK A := by
  sorry

/-- Hop 2 (union bound): on any completed challenge run, either some signed
  pair of the accepted bundle was never produced by the challenger
  (`sigForgeExp`), or the KEM-key bad event occurred (`pqpkGuessedExp`), or
  the forgery happened with an honest bundle and separated KEM keys
  (`forgeHonestGoodExp`). Purely probabilistic; uses no cryptographic
  hypotheses. -/
lemma forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    forgeProb P msg hasOPK A ≤ sigForgeProb P msg hasOPK A +
      pqpkGuessedProb P msg hasOPK A + forgeHonestGoodProb P msg hasOPK A := by
  sorry

omit [DecidableEq CT] [DecidableEq C] in
/-- Hop 3 (SUF-CMA): a signature forgery in the challenge phase yields a
  strong existential forgery against `P.sig`.

  Intended reduction: the SUF-CMA adversary simulates the challenge phase,
  substituting its challenge public key for `sigkB.1` and its signing oracle
  for the two uses of `P.sig.sign` (setup's pre-key signature and each
  session's KEM-key signature; the signing key is used nowhere else, and the
  adversary never sees it). When the challenge session completes, it stops
  and outputs the accepted bundle's signed pair that `honestBundle` fails,
  so the pair was not returned by any signing query. Determinism of
  verification (`hverifyDet`) transfers the initiator's successful
  verification of that pair to the SUF-CMA experiment's final check.
  Strong unforgeability (rather than EUF-CMA) is needed because `setup` and
  `publish` sign only two message forms, so a dishonest bundle may reuse an
  honestly signed message with a fresh signature. -/
lemma sigForgeProb_le_sig [Inhabited S] [Inhabited SSK]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (εsig : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig) :
    sigForgeProb P msg hasOPK A ≤ εsig := by
  sorry

omit [DecidableEq CT] [DecidableEq S] [DecidableEq C] in
/-- Hop 4 (KEM-key guessing): the bad event `pqpkGuessed` is a union of
  pairwise guessing events on `P.pqkem.keygen`, so its probability is
  bounded by the number of pairs times the per-pair guessing bound `εpk`.

  Intended proof: with at most `q` sessions, the collision part is a union
  over at most `q * (q - 1) / 2` unordered session pairs; conditioning on
  the earlier key generation, the later one hits it with probability at most
  `εpk` by `hpk`. The prediction part is a union over at most `q` pairs of
  the accepted bundle and a later-opened session; the accepted bundle's key
  is determined strictly before that session's key generation, so `hpk`
  applies again. In total `q * (q + 1) / 2 ≤ q ^ 2` pairs (for `q = 0` both
  sides vanish). -/
lemma pqpkGuessedProb_le
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εpk : ℝ)
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk := by
  sorry

end PQXDH
