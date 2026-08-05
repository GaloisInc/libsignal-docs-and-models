/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import ToVCVio.CryptoFoundations.AKE.UAKE.Party

/-!
# Trace-free view of an honest protocol run

`Party.runHonest` returns the sequence of messages exchanged, which the
correctness experiment discards. Reasoning about the honest run by unfolding
`runHonest` therefore forces every proof to walk past the binds that build that
sequence, and any change to how it is accumulated shifts every destructuring
layer downstream.

This module gives the trace-free view its own definition,
`Party.runHonestPair`, and relates it to `Party.runHonest` once. Correctness
proofs consume `runHonestPair` and are insulated from the trace plumbing.

`runHonestPair_eq` is also a guard: it holds only while the two definitions
agree on the protocol semantics, so a change upstream that is not merely
bookkeeping will break the lemma rather than the proofs that depend on it.
-/

open OracleSpec OracleComp

namespace AKE.UAKE.Party

variable {m : Type → Type} [Monad m] [LawfulMonad m] {W : Type}
  {InP OutP InQ OutQ : Type}

/-- `runHonestLoop` with the message trace dropped. -/
def runHonestPairLoop (P : Party m InP W OutP) (Q : Party m InQ W OutQ) :
    ℕ → P.State → Q.State → W → Bool → m (P.State × Q.State)
  | 0, pState, qState, _, _ => pure (pState, qState)
  | fuel + 1, pState, qState, w, true => do
      match ← Q.step qState w with
      | .acceptAndSend qState' w' _ => runHonestPairLoop P Q fuel pState qState' w' false
      | .complete qState' => pure (pState, qState')
      | .reject => pure (pState, qState)
  | fuel + 1, pState, qState, w, false => do
      match ← P.step pState w with
      | .acceptAndSend pState' w' _ => runHonestPairLoop P Q fuel pState' qState w' true
      | .complete pState' => pure (pState', qState)
      | .reject => pure (pState, qState)

/-- `runHonest` with the message trace dropped. -/
def runHonestPair (P : Party m InP W OutP) (Q : Party m InQ W OutQ)
    (inP : InP) (inQ : InQ) (fuel : ℕ) : m (Option OutP × Option OutQ) := do
  let pInit ← P.init inP
  let qInit ← Q.init inQ
  let (pState', qState') ← match pInit.opening, qInit.opening with
    | some w, _ => runHonestPairLoop P Q fuel pInit.state qInit.state w true
    | none, some w => runHonestPairLoop P Q fuel pInit.state qInit.state w false
    | none, none => pure (pInit.state, qInit.state)
  let pOut ← P.output pState'
  let qOut ← Q.output qState'
  pure (pOut, qOut)

lemma runHonestPairLoop_eq (P : Party m InP W OutP) (Q : Party m InQ W OutQ) :
    ∀ (fuel : ℕ) (pState : P.State) (qState : Q.State) (w : W) (pTurn : Bool),
      (fun r => (r.1, r.2.1)) <$> runHonestLoop P Q fuel pState qState w pTurn
        = runHonestPairLoop P Q fuel pState qState w pTurn
  | 0, _, _, _, _ => by simp [runHonestLoop, runHonestPairLoop]
  | fuel + 1, pState, qState, w, true => by
      simp only [runHonestLoop, runHonestPairLoop, map_bind]
      refine bind_congr fun sr => ?_
      cases sr with
      | acceptAndSend qState' w' _ =>
          simp only [map_bind, map_pure]
          rw [← runHonestPairLoop_eq P Q fuel pState qState' w' false]
          simp only [map_eq_bind_pure_comp, Function.comp_def]
      | complete qState' => simp
      | reject => simp
  | fuel + 1, pState, qState, w, false => by
      simp only [runHonestLoop, runHonestPairLoop, map_bind]
      refine bind_congr fun sr => ?_
      cases sr with
      | acceptAndSend pState' w' _ =>
          simp only [map_bind, map_pure]
          rw [← runHonestPairLoop_eq P Q fuel pState' qState w' true]
          simp only [map_eq_bind_pure_comp, Function.comp_def]
      | complete pState' => simp
      | reject => simp

lemma runHonestPair_eq (P : Party m InP W OutP) (Q : Party m InQ W OutQ)
    (inP : InP) (inQ : InQ) (fuel : ℕ) :
    (fun r => (r.1, r.2.1)) <$> runHonest P Q inP inQ fuel
      = runHonestPair P Q inP inQ fuel := by
  simp only [runHonest, runHonestPair, map_bind]
  refine bind_congr fun pInit => ?_
  refine bind_congr fun qInit => ?_
  rcases hp : pInit.opening with _ | w
  · rcases hq : qInit.opening with _ | w
    · simp
    · simp only [map_bind, map_pure]
      rw [← runHonestPairLoop_eq P Q fuel pInit.state qInit.state w false]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  · simp only [map_bind, map_pure]
    rw [← runHonestPairLoop_eq P Q fuel pInit.state qInit.state w true]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

lemma mem_support_runHonestPair [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    {P : Party m InP W OutP} {Q : Party m InQ W OutQ} {inP : InP} {inQ : InQ} {fuel : ℕ}
    {uOut : Option OutP} {tOut : Option OutQ} {ms : List W}
    (h : (uOut, tOut, ms) ∈ support (runHonest P Q inP inQ fuel)) :
    (uOut, tOut) ∈ support (runHonestPair P Q inP inQ fuel) := by
  rw [← runHonestPair_eq, support_map]
  exact ⟨_, h, rfl⟩

end AKE.UAKE.Party
