/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.UAKE.WellFormedLemmas
import ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Security Lemmas for Spec-based PQXDH

Game hops scaffolding the proof of the top-level DH security theorem
`PQXDH.uakeInitiator_secure_dh` in `Security.lean`. The UAKE experiment is
split into a forgery branch (the challenge session completes on a transcript
that matches no T-oracle session) and an indistinguishability branch (the
adversary distinguishes the accepted session key from random), and each
branch is bounded against the component primitives:

* Hop 1 (`advantage_le_forgeProb_add_indistAdvantage`): replace the outright
  win awarded for a forgery with a fair coin flip; the UAKE advantage is
  bounded by the forgery probability plus the modified experiment's
  advantage.
* Hop 2 (`forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood`): a
  forgery is a signature forgery, a KEM public-key collision or prediction,
  or a forgery on an honestly signed bundle with separated KEM keys.
* Hop 3 (`sigForgeProb_le_sig`): the SUF-CMA reduction for dishonest
  bundles.
* Hop 4 (`pqpkGuessedProb_le`): KEM public-key collisions and predictions
  reduce to guessing the public key output by `P.pqkem.keygen`.
* Hop 5 (`forgeHonestGoodProb_le`): the forgery core, against GapDH, the
  KDF, and the AEAD.
* Hop 6 (`indistAdvantage_le`): the indistinguishability core, against
  GapDH, the KDF, the AEAD, and KEM public-key guessing.

Hops 5 and 6 idealize the KDF outputs on the challenge session's key
material. Their statements are believed true in the current model (the KDF
as a plain parameter function, plus a PRF hypothesis), but the standard
reductions require the KDF to be a programmable random oracle, so their
proofs are deferred to that planned model change; the intended sub-hops are
recorded in their doc comments. The well-formedness lemmas in
`WellFormedLemmas.lean` (parties output exactly at completion, honest runs
transfer exactly `rounds` messages) are expected to discharge the
bookkeeping relating `K0` to challenge-session completion.

The definitions, lemma statements, and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace PQXDH

noncomputable section

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- The pre-key bundle carried by a transcript's first message, if any. In
  the T=Bob scheme, a T-oracle session transcript begins with the bundle Bob
  published, and a completed challenge transcript begins with the bundle the
  initiator accepted (rejected messages are dropped from transcripts). -/
def transcriptBundle (tr : Transcript (Message G PQPK CT S C IdC IdK)) :
    Option (PreKeyBundle G PQPK S IdC IdK) :=
  match tr.entries.head? with
  | some (Message.bundle b, _) => some b
  | _ => none

/-- The global-clock timestamp of a transcript's first entry, if any. For a
  T-oracle session this is the time the session was opened; for the
  challenge transcript it is the time the initiator accepted a bundle. -/
def transcriptStart (tr : Transcript (Message G PQPK CT S C IdC IdK)) : Option ℕ :=
  tr.entries.head?.map Prod.snd

/-- The bundles published by the T-oracle sessions, in session order. -/
def oracleBundles (cr : ChallengeResult (uakeInitiator P msg hasOPK)) :
    List (PreKeyBundle G PQPK S IdC IdK) :=
  cr.oracleTrs.filterMap transcriptBundle

/-- The bundle accepted by the challenge session, if it accepted one. -/
def challengeBundle (cr : ChallengeResult (uakeInitiator P msg hasOPK)) :
    Option (PreKeyBundle G PQPK S IdC IdK) :=
  transcriptBundle cr.challengeTr

/-- True if every signed pair the initiator verifies in the bundle `b` was
  honestly produced by the challenger: the signed pre-key pair is the one
  created by `setup`, and the KEM pair was published by some T-oracle
  session. A completed challenge session whose accepted bundle fails this
  predicate yields a strong (SUF-CMA) signature forgery. -/
def honestBundle (tk : RecipientIdentity F G SPK SSK S)
    (cr : ChallengeResult (uakeInitiator P msg hasOPK))
    (b : PreKeyBundle G PQPK S IdC IdK) : Bool :=
  decide (b.spkB.1 = tk.spkB.1) && decide (b.spkSigB = tk.spkSigB) &&
    (oracleBundles P msg hasOPK cr).any fun b' =>
      decide (b.pqpkB.1 = b'.pqpkB.1) && decide (b.pqpkSigB = b'.pqpkSigB)

/-- The KEM-key bad event of the forgery branch: either two T-oracle
  sessions published the same KEM public key, or the challenge session
  accepted its bundle strictly before some T-oracle session carrying the
  same KEM public key was opened (i.e., the adversary predicted an honest
  KEM key before it was generated). Both are guessing events on
  `P.pqkem.keygen`. No cryptographic hypothesis of the DH theorem excludes
  them, and a KEM with colliding or predictable public keys genuinely
  breaks UAKE security: a second session holding the same KEM key accepts a
  replay of the challenge session's initial message, derives the same
  session key, and can be revealed without matching the challenge
  transcript. -/
def pqpkGuessed (cr : ChallengeResult (uakeInitiator P msg hasOPK)) : Bool :=
  !decide ((oracleBundles P msg hasOPK cr).map (·.pqpkB.1)).Nodup ||
    ((challengeBundle P msg hasOPK cr).any fun b =>
      (transcriptStart cr.challengeTr).any fun tc =>
        cr.oracleTrs.any fun tr =>
          ((transcriptBundle tr).any fun b' => decide (b.pqpkB.1 = b'.pqpkB.1)) &&
            (transcriptStart tr).any fun ti => decide (tc < ti))

/-- The challenge phase of the UAKE experiment against the T=Bob scheme: run
  `setup`, then the adversary's challenge stage with oracle access to copies
  of T. The challenge bit is independent of this phase, so the experiments
  below sample it themselves where needed; this matches `UAKE.Exp` up to
  commuting independent samples. -/
def challengePhase (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    ProbComp (ChallengeResult (uakeInitiator P msg hasOPK) ×
      (A.State × Env (uakeInitiator P msg hasOPK) × RecipientIdentity F G SPK SSK S)) := do
  let (uk, tk) ← setup P msg
  challengeSession ProbCompRuntime.probComp.toProbCompLift A uk tk

/-- Forgery experiment: the challenge session completed, but its transcript
  matches no T-oracle session, so the adversary spoofed a message from T. -/
def forgeExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, _) ← challengePhase P msg hasOPK A
  return cr.K0.isSome && !isPingPong cr

/-- Probability of the forgery event. -/
def forgeProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | forgeExp P msg hasOPK A]).toReal

/-- Signature-forgery experiment: the challenge session completed, and some
  signed pair in the bundle it accepted was never produced by the
  challenger. -/
def sigForgeExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, st) ← challengePhase P msg hasOPK A
  return cr.K0.isSome &&
    (challengeBundle P msg hasOPK cr).any fun b => !honestBundle P msg hasOPK st.2.2 cr b

/-- Probability of the signature-forgery event. -/
def sigForgeProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | sigForgeExp P msg hasOPK A]).toReal

/-- KEM-key guessing experiment: the bad event `pqpkGuessed` occurred during
  the challenge phase. -/
def pqpkGuessedExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, _) ← challengePhase P msg hasOPK A
  return pqpkGuessed P msg hasOPK cr

/-- Probability of the KEM-key guessing event. -/
def pqpkGuessedProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | pqpkGuessedExp P msg hasOPK A]).toReal

/-- Residual forgery experiment: a forgery on an honestly signed bundle,
  with pairwise-distinct and unpredicted KEM keys. This is the event bounded
  by the forgery core (Hop 5). -/
def forgeHonestGoodExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, st) ← challengePhase P msg hasOPK A
  return cr.K0.isSome && !isPingPong cr &&
    ((challengeBundle P msg hasOPK cr).all fun b => honestBundle P msg hasOPK st.2.2 cr b) &&
    !pqpkGuessed P msg hasOPK cr

/-- Probability of the residual forgery event. -/
def forgeHonestGoodProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | forgeHonestGoodExp P msg hasOPK A]).toReal

/-- The UAKE experiment with the forgery branch's outright win replaced by a
  fair coin flip. Identical to `UAKE.Exp` on the other two branches. -/
def indistExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (uk, tk) ← setup P msg
  let b ← $ᵗ Bool
  let (cr, st) ← challengeSession ProbCompRuntime.probComp.toProbCompLift A uk tk
  if cr.K0.isNone then
    finalize ProbCompRuntime.probComp.toProbCompLift A st cr b none
  else if !isPingPong cr then
    $ᵗ Bool
  else do
    let K1 ← some <$> ($ᵗ K)
    finalize ProbCompRuntime.probComp.toProbCompLift A st cr b K1

/-- The adversary's advantage over a fair coin in `indistExp`. -/
def indistAdvantage (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  |(Pr[= true | indistExp P msg hasOPK A]).toReal - 1 / 2|

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

/-- Hop 5 (forgery core): with an honest bundle and separated KEM keys, a
  forgery requires breaking GapDH, the KDF, or the AEAD.

  Intended proof, as further hops once the KDF is modeled as a random oracle
  (see the module comment):
  1. Identify the unique T-oracle session that can share the challenge
     session's key material: the accepted bundle pins `ikB` (checked by the
     initiator), `spkB` (the only EC key `setup` signs), and `pqpkB`
     (published by exactly one session, by `hidKEM` and the excluded
     collision event).
  2. Replace the KDF output triple `(SK, KA, KB)` on the challenge session's
     key material with a fresh uniform triple, shared with any T-oracle
     session that derives identical key material. A distinguisher must query
     the KDF on the challenge key material, whose third DH component is
     `DH ekA.2 spkB.1` for the challenge session's fresh ephemeral `ekA`;
     embedding the GapDH challenge in `ekA` and `spkB`, recognizing the
     query with the DDH oracle, and answering the T oracle's other KDF
     queries consistently (again via the DDH oracle) yields a GapDH
     adversary. This step consumes `εgap` and, under the current PRF
     modeling of the KDF, `εkdf`.
  3. With `KA` uniform, an initial message accepted by the paired session
     with a modified AEAD ciphertext is a forgery against `KA` (first
     `εaead`, via the INT-CTXT-D game whose encryption oracle produces the
     challenge session's ciphertext).
  4. With `KB` uniform, the confirmation the initiator accepts must have
     been produced under `KB` by the paired session (second `εaead`); a
     verbatim relay of honestly produced messages forces the global-clock
     interleaving of `Matching`, so the transcripts match, contradicting
     the forgery event.

  The factor `q` is generous (the reduction handles all sessions at once),
  but stating the bound with it makes the composed bound collapse to `εsig`
  when the adversary opens no sessions, in which case completing the
  challenge session already requires a signature forgery. -/
lemma forgeHonestGoodProb_le [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf : ℝ)
    (hidKEM : Function.Injective P.idKEM)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ q * (εgap + 2 * εaead + εkdf) := by
  sorry

/-- Hop 6 (indistinguishability core): in `indistExp`, the adversary's guess
  is better than a fair coin only by breaking GapDH, the KDF, or the AEAD,
  or by a KEM public-key collision.

  Intended proof, as further hops once the KDF is modeled as a random oracle
  (see the module comment):
  1. If the challenge session outputs no key, both finalizations hand the
     adversary `none` and the guess is independent of the challenge bit, so
     it wins with probability exactly `1 / 2`; the coined forgery branch
     likewise. Only the ping-pong branch remains.
  2. In the ping-pong branch, the accepted bundle equals a T-oracle
     session's published bundle (their transcripts match message by
     message), so the bundle is honest without a signature hypothesis.
  3. Replace the KDF output triple on the challenge session's key material
     with a fresh uniform triple, as in the forgery core (`εgap` plus, under
     the current PRF modeling, `εkdf`).
  4. If the matching session derived different key material (a KEM
     decapsulation mismatch), the confirmation the initiator accepted
     decrypts under the now-uniform `KB` without having been produced under
     it: an AEAD forgery (`εaead`).
  5. A reveal query returns the challenge key only for a session with
     identical key material. For a session whose transcript matches the
     challenge, `fullPingPong` flips a fair coin instead; any other such
     session requires two T-oracle sessions sharing a KEM public key.
     Both adversary stages together open at most `2 * q` sessions, giving
     at most `2 * q ^ 2` pairs and the `2 * q ^ 2 * εpk` term by the
     guessing bound (this term also absorbs prediction events in the post
     phase, as in Hop 4).
  6. Otherwise the challenge key is uniform, independent of the adversary's
     view, and unrevealed, so the real and random finalizations are
     identically distributed and the guess wins with probability exactly
     `1 / 2`. -/
lemma indistAdvantage_le [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf εpk : ℝ)
    (hidKEM : Function.Injective P.idKEM)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      q * (εgap + εaead + εkdf) + 2 * (q : ℝ) ^ 2 * εpk := by
  sorry

end

end PQXDH
