/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.UAKE.Defs

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

lemma finalize_true_add_false_eq_one {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (K1 : Option K)
    (hKb : cr.K0 = K1) :
    Pr[= true | UAKE.finalize ProbCompLift.id A st cr true K1] +
      Pr[= true | UAKE.finalize ProbCompLift.id A st cr false K1] = 1 := by
  obtain ⟨aSt, env, tk⟩ := st
  simp only [UAKE.finalize, hKb, ite_self]
  generalize (simulateQ (UAKE.oracleImpl ProbCompLift.id proto tk) (A.post aSt K1)).run
    { env with challengeDone := true } = run
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add,
    ← tsum_probOutput_of_liftM_PMF run]
  refine tsum_congr fun x => ?_
  simp only [ProbCompLift.id, MonadHom.id]
  have hsum : Pr[= true | if UAKE.fullPingPong x.2.tSessions cr = true then ($ᵗ Bool)
        else pure (x.1 == true)] +
      Pr[= true | if UAKE.fullPingPong x.2.tSessions cr = true then ($ᵗ Bool)
        else pure (x.1 == false)] = 1 := by
    cases hfpp : UAKE.fullPingPong x.2.tSessions cr
    · cases hx : x.1 <;> simp
    · simp [probOutput_uniformSample, Fintype.card_bool, ENNReal.inv_two_add_inv_two]
  rw [← mul_add, hsum, mul_one]

lemma finalize_none_half {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (hK0 : cr.K0 = none) :
    Pr[= true | do let b ← $ᵗ Bool; UAKE.finalize ProbCompLift.id A st cr b none] = 1 / 2 := by
  rw [probOutput_bind_uniformBool (fun b => UAKE.finalize ProbCompLift.id A st cr b none) true,
    finalize_true_add_false_eq_one A st cr none hK0]

lemma probOutput_bind_if_true_uniformBool {α : Type} (m : ProbComp α) (c : α → Bool) :
    Pr[= true | do let x ← m; if c x then (pure true : ProbComp Bool) else $ᵗ Bool] =
      1 / 2 + Pr[= true | do let x ← m; pure (c x)] / 2 := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  conv_rhs => rw [show (1 : ℝ≥0∞) / 2 = (∑' x, Pr[= x | m]) / 2 from by
    rw [tsum_probOutput_of_liftM_PMF]]
  simp only [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  cases hcx : c x
  · simp [probOutput_uniformSample, Fintype.card_bool]
  · have hp : Pr[= x | m] = Pr[= x | m] * 2⁻¹ + Pr[= x | m] * 2⁻¹ := by
      rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    simpa [probOutput_uniformSample, Fintype.card_bool] using hp

def initiateIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, _SS) ← P.pqkem.encaps bundle.pqpkB.1
  let (SK, KA, KB) ← ($ᵗ (K × K × K) : ProbComp _)
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt KA AD p.msg
  return some ({ ikA := p.ikA.1, ekA := ekA.1, ct := CT, idSPK := bundle.spkB.2,
                 idPQPK := bundle.pqpkB.2, idOPK := bundle.opkB.map Prod.snd, ctxt := ctxt },
    { sk := SK, kb := KB, ad := AD, msg := p.msg })

lemma initiateIdeal_verify_of_accept [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg) (bundle : PreKeyBundle G PQPK S IdC IdK)
    {r : InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K}
    (hr : some r ∈ support (initiateIdeal P p bundle)) :
    true ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB) ∧
      true ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB) := by
  simp only [initiateIdeal] at hr
  split at hr
  · simp at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨okSPK, hSPK, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨okPQPK, hPQPK, hr⟩ := hr
    split at hr
    · simp at hr
    · rename_i hcond
      cases okSPK <;> cases okPQPK <;> simp_all

def initiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiateIdeal P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr _) => do let SK ← $ᵗ K; pure (some (some SK))
    | _ => pure none

lemma initiatorIdeal_step_bundle_verify [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg) (b : PreKeyBundle G PQPK S IdC IdK)
    {st' : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K}
    {w' : Message G PQPK CT S C IdC IdK} {done : Bool}
    (hst : Party.StepResult.acceptAndSend st' w' done ∈
      support ((initiatorIdeal P).step (Sum.inl p) (Message.bundle b))) :
    true ∈ support (P.sig.verify p.sigpkB (EncodeEC b.spkB.1) b.spkSigB) ∧
      true ∈ support (P.sig.verify p.sigpkB (EncodeKEM b.pqpkB.1) b.pqpkSigB) := by
  simp only [initiatorIdeal] at hst
  obtain ⟨r, hr, hst⟩ := (mem_support_bind_iff _ _ _).1 hst
  cases r with
  | none => simp at hst
  | some imctx => exact initiateIdeal_verify_of_accept P p b hr

lemma initiatorIdeal_output_completed [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    {y : Option (Option K)} (hy : y ∈ support ((initiatorIdeal P).output st))
    (hjoin : y.join.isSome) :
    ∃ SK, st = Sum.inr (Sum.inr SK) := by
  cases st with
  | inl _ => simp only [initiatorIdeal, support_pure, Set.mem_singleton_iff] at hy
             subst hy; simp at hjoin
  | inr st2 =>
    cases st2 with
    | inl _ => simp only [initiatorIdeal, support_pure, Set.mem_singleton_iff] at hy
               subst hy; simp at hjoin
    | inr SK => exact ⟨SK, rfl⟩

def uakeInitiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiatorIdeal P
  T := recipient P hasOPK

def _root_.AKE.UAKE.Adversary.toIdeal
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (uakeInitiatorIdeal P msg hasOPK) where
  State := A.State
  challenge := A.challenge
  post := A.post

end PQXDH
