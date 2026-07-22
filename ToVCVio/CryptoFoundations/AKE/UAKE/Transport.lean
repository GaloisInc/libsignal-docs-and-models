/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs

/-!
# Transport of UAKE games along party simulations
-/

open OracleSpec OracleComp

namespace AKE.UAKE

namespace Party

def InitResult.map {St₁ St₂ W : Type} (σ : St₁ → St₂) :
    InitResult St₁ W → InitResult St₂ W
  | .speakFirst st w => .speakFirst (σ st) w
  | .waitForMsg st => .waitForMsg (σ st)

@[simp] lemma InitResult.map_state {St₁ St₂ W : Type} (σ : St₁ → St₂)
    (r : InitResult St₁ W) : (InitResult.map σ r).state = σ r.state := by
  cases r <;> rfl

@[simp] lemma InitResult.map_opening {St₁ St₂ W : Type} (σ : St₁ → St₂)
    (r : InitResult St₁ W) : (InitResult.map σ r).opening = r.opening := by
  cases r <;> rfl

def StepResult.map {St₁ St₂ W : Type} (σ : St₁ → St₂) :
    StepResult St₁ W → StepResult St₂ W
  | .acceptAndSend st w done => .acceptAndSend (σ st) w done
  | .complete st => .complete (σ st)
  | .reject => .reject

structure Sim {m : Type → Type} [Functor m] {In₁ In₂ W Out : Type}
    (P₁ : Party m In₁ W Out) (P₂ : Party m In₂ W Out)
    (fIn : In₁ → In₂) (σ : P₁.State → P₂.State) : Prop where
  init_eq : ∀ i, P₂.init (fIn i) = InitResult.map σ <$> P₁.init i
  step_eq : ∀ st w, P₂.step (σ st) w = StepResult.map σ <$> P₁.step st w
  output_eq : ∀ st, P₂.output (σ st) = P₁.output st

end Party

section Transport

variable {K UK₁ TK₁ UK₂ TK₂ W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  {proto₁ : Scheme m K UK₁ TK₁ W} {proto₂ : Scheme m K UK₂ TK₂ W}

def Env.transport (σU : proto₁.U.State → proto₂.U.State)
    (σT : proto₁.T.State → proto₂.T.State) (e : Env proto₁) : Env proto₂ where
  clock := e.clock
  challenge := ⟨σU e.challenge.state, e.challenge.transcript⟩
  challengeDone := e.challengeDone
  tSessions := e.tSessions.map fun t => ⟨σT t.state, t.transcript, t.key, t.revealed⟩

def ChallengeResult.transport (cr : ChallengeResult proto₁) : ChallengeResult proto₂ :=
  ⟨cr.K0, cr.challengeTr, cr.oracleTrs⟩

omit [Monad m] [LawfulMonad m] in
@[simp] lemma ChallengeResult.transport_K0 (cr : ChallengeResult proto₁) :
    (ChallengeResult.transport cr : ChallengeResult proto₂).K0 = cr.K0 :=
  rfl

@[reducible] def Adversary.transport (fU : UK₁ → UK₂) (A : Adversary proto₂) :
    Adversary proto₁ where
  State := A.State
  challenge := fun uk w => A.challenge (fU uk) w
  post := A.post

variable {fU : UK₁ → UK₂} {fT : TK₁ → TK₂}
  {σU : proto₁.U.State → proto₂.U.State} {σT : proto₁.T.State → proto₂.T.State}

lemma opImpl_transport
    (hU : Party.Sim proto₁.U proto₂.U fU σU) (hT : Party.Sim proto₁.T proto₂.T fT σT)
    (tk : TK₁) (op : Op W) (e : Env proto₁) :
    (opImpl proto₂ (fT tk) op).run (Env.transport σU σT e)
      = Prod.map id (Env.transport σU σT) <$> (opImpl proto₁ tk op).run e := by
  cases op with
  | revealT sid =>
      simp only [opImpl, StateT.run_bind, StateT.run_get, pure_bind,
        Env.transport, List.getElem?_map]
      cases hs : e.tSessions[sid]? with
      | none => simp [Env.transport]
      | some t =>
          simp only [Option.map_some, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, map_pure]
          exact congrArg pure (Prod.ext rfl (by simp [Env.transport, List.map_set]))
  | openT =>
      simp only [opImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_get,
        StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc, pure_bind,
        hT.init_eq tk, bind_map_left, map_bind, map_pure]
      refine bind_congr fun r => ?_
      cases r <;> simp [Party.InitResult.map, Env.transport, List.map_append]
  | stepT sid w =>
      simp only [opImpl, StateT.run_bind, StateT.run_get, pure_bind,
        Env.transport, List.getElem?_map]
      cases hs : e.tSessions[sid]? with
      | none => simp [Env.transport]
      | some t =>
        simp only [Option.map_some]
        cases hk : t.key with
        | some k => simp [Env.transport]
        | none =>
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind, hT.step_eq t.state w, bind_map_left, map_bind]
          refine bind_congr fun sr => ?_
          cases sr with
          | reject => simp [Party.StepResult.map, Env.transport]
          | acceptAndSend st' w' done =>
              cases done with
              | false =>
                  simp only [Party.StepResult.map, reduceCtorEq, reduceIte,
                    StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                    map_pure]
                  exact congrArg pure (Prod.ext rfl (by simp [Env.transport,
                    List.map_set]))
              | true =>
                  simp only [Party.StepResult.map, reduceIte, StateT.run_bind,
                    StateT.run_monadLift, StateT.run_set, StateT.run_pure,
                    monadLift_self, bind_assoc, pure_bind, hT.output_eq st',
                    map_bind, map_pure]
                  refine bind_congr fun key => ?_
                  exact congrArg pure (Prod.ext rfl (by simp [Env.transport,
                    List.map_set]))
          | complete st' =>
              simp only [Party.StepResult.map, StateT.run_bind, StateT.run_monadLift,
                StateT.run_set, StateT.run_pure, monadLift_self, bind_assoc,
                pure_bind, hT.output_eq st', map_bind, map_pure]
              refine bind_congr fun key => ?_
              exact congrArg pure (Prod.ext rfl (by simp [Env.transport,
                List.map_set]))
  | stepChallenge w =>
      simp only [opImpl, StateT.run_bind, StateT.run_get, pure_bind, Env.transport]
      cases hd : e.challengeDone with
      | true => simp [hd, Env.transport]
      | false =>
          simp only [Bool.false_eq_true, if_false, StateT.run_bind,
            StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
            hU.step_eq e.challenge.state w, bind_map_left, map_bind]
          refine bind_congr fun sr => ?_
          cases sr with
          | reject => simp [Party.StepResult.map, Env.transport, hd]
          | acceptAndSend st' w' done =>
              simp only [Party.StepResult.map, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, map_pure]
              exact congrArg pure (Prod.ext rfl (by simp [Env.transport]))
          | complete st' =>
              simp only [Party.StepResult.map, StateT.run_bind, StateT.run_set,
                StateT.run_pure, pure_bind, map_pure]
              exact congrArg pure (Prod.ext rfl (by simp [Env.transport]))

variable [MonadLiftT ProbComp m]

omit [LawfulMonad m] in
private lemma run_liftM_lift {σ α : Type} (x : ProbComp α) (s : σ) :
    (liftM x : StateT σ m α).run s = (do let a ← (liftM x : m α); pure (a, s)) :=
  rfl

lemma simulateQ_oracleImpl_transport {α : Type}
    (hU : Party.Sim proto₁.U proto₂.U fU σU) (hT : Party.Sim proto₁.T proto₂.T fT σT)
    (tk : TK₁) (oa : OracleComp (unifSpec + oracleSpec K W) α) (e : Env proto₁) :
    (simulateQ (oracleImpl proto₂ (fT tk)) oa).run (Env.transport σU σT e)
      = Prod.map id (Env.transport σU σT) <$>
          (simulateQ (oracleImpl proto₁ tk) oa).run e := by
  induction oa using OracleComp.inductionOn generalizing e with
  | pure x => simp [StateT.run_pure]
  | query_bind t oa ih =>
      rcases t with i | op
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, oracleImpl, QueryImpl.add_apply_inl,
          QueryImpl.liftTarget_apply, StateT.run_bind, map_bind]
        erw [run_liftM_lift, run_liftM_lift]
        simp only [bind_assoc, pure_bind]
        exact bind_congr fun a => ih a e
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, oracleImpl, QueryImpl.add_apply_inr,
          StateT.run_bind, map_bind]
        refine Eq.trans (congrArg (· >>= _) (opImpl_transport hU hT tk op e)) ?_
        beta_reduce
        erw [bind_map_left]
        exact bind_congr fun p => ih p.1 p.2

lemma challengeSession_transport
    (hU : Party.Sim proto₁.U proto₂.U fU σU) (hT : Party.Sim proto₁.T proto₂.T fT σT)
    (A : Adversary proto₂) (uk : UK₁) (tk : TK₁) :
    challengeSession A (fU uk) (fT tk)
      = (fun r => (ChallengeResult.transport r.1,
          (r.2.1, Env.transport σU σT r.2.2.1, fT r.2.2.2))) <$>
          challengeSession (A.transport fU) uk tk := by
  unfold challengeSession
  simp only [hU.init_eq uk, bind_map_left, map_bind, Adversary.transport]
  refine bind_congr fun u0 => ?_
  simp only [Party.InitResult.map_opening, Party.InitResult.map_state]
  rw [show (⟨(recordOpt ⟨[]⟩ u0.opening 0).2, ⟨σU u0.state, (recordOpt ⟨[]⟩ u0.opening 0).1⟩,
      false, []⟩ : Env proto₂)
    = Env.transport σU σT ⟨(recordOpt ⟨[]⟩ u0.opening 0).2,
        ⟨u0.state, (recordOpt ⟨[]⟩ u0.opening 0).1⟩, false, []⟩ from by
      simp [Env.transport]]
  rw [simulateQ_oracleImpl_transport hU hT tk]
  simp only [bind_map_left]
  refine bind_congr fun p => ?_
  simp only [Prod.map_fst, Prod.map_snd, id_eq]
  rw [show (Env.transport σU σT p.2).challenge.state = σU p.2.challenge.state from rfl,
    hU.output_eq]
  refine bind_congr fun k0 => ?_
  simp [ChallengeResult.transport, Env.transport, List.map_map, Function.comp_def]

variable [DecidableEq W]

omit [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m] in
lemma isPingPong_transport (hrounds : proto₂.rounds = proto₁.rounds)
    (cr : ChallengeResult proto₁) :
    isPingPong (ChallengeResult.transport cr : ChallengeResult proto₂)
      = isPingPong cr := by
  simp [isPingPong, ChallengeResult.transport, hrounds]

omit [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m] in
lemma fullPingPong_transport (hrounds : proto₂.rounds = proto₁.rounds)
    (e : Env proto₁) (cr : ChallengeResult proto₁) :
    fullPingPong (Env.transport σU σT e) (ChallengeResult.transport cr)
      = fullPingPong e cr := by
  simp [fullPingPong, Env.transport, ChallengeResult.transport, hrounds,
    List.filter_map, Function.comp_def, List.map_map]

lemma finalize_transport
    (hU : Party.Sim proto₁.U proto₂.U fU σU) (hT : Party.Sim proto₁.T proto₂.T fT σT)
    (hrounds : proto₂.rounds = proto₁.rounds)
    (A : Adversary proto₂) (aSt : A.State) (e : Env proto₁) (tk : TK₁)
    (cr : ChallengeResult proto₁) (b : Bool) (K1 : Option K) :
    finalize A (aSt, Env.transport σU σT e, fT tk) (ChallengeResult.transport cr) b K1
      = finalize (A.transport fU) (aSt, e, tk) cr b K1 := by
  unfold finalize
  have hK0 : (ChallengeResult.transport cr : ChallengeResult proto₂).K0 = cr.K0 := rfl
  simp only [hK0]
  rw [simulateQ_oracleImpl_transport hU hT tk (A.post aSt (if b then K1 else cr.K0)) e]
  simp only [bind_map_left]
  refine bind_congr fun p => ?_
  simp only [Prod.map_fst, Prod.map_snd, id_eq]
  rw [fullPingPong_transport (σU := σU) (σT := σT) hrounds]

theorem Exp_transport [SampleableType K]
    (hU : Party.Sim proto₁.U proto₂.U fU σU) (hT : Party.Sim proto₁.T proto₂.T fT σT)
    (hrounds : proto₂.rounds = proto₁.rounds)
    (hsetup : proto₂.setup = Prod.map fU fT <$> proto₁.setup)
    (A : Adversary proto₂) :
    Exp A = Exp (A.transport (proto₁ := proto₁) fU) := by
  unfold Exp
  rw [hsetup]
  erw [bind_map_left]
  refine bind_congr fun x => ?_
  obtain ⟨uk, tk⟩ := x
  refine bind_congr fun b => ?_
  rw [challengeSession_transport hU hT A uk tk]
  erw [bind_map_left]
  refine bind_congr fun r => ?_
  simp only [isPingPong_transport (proto₂ := proto₂) hrounds,
    finalize_transport hU hT hrounds A, ChallengeResult.transport_K0]

end Transport

end AKE.UAKE
