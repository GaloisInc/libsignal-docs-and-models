/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.MTP.Basic

open OracleSpec OracleComp

namespace AKE.ICMA

variable {Msg SendK RecvK W : Type}

structure Env (proto : MTP.Scheme ProbComp Msg SendK RecvK W) where
  clock : ℕ
  challenge : Session proto.receiver.State W
  challengeOutput : Option (Option Msg)
  senders : List (Session proto.sender.State W)

inductive Op (Msg W : Type) where
  | openSender : Msg → Op Msg W
  | stepSender : ℕ → W → Op Msg W
  | stepChallenge : W → Op Msg W

def oracleSpec (Msg W : Type) : OracleSpec (Op Msg W)
  | .openSender _ => ℕ × Option W
  | .stepSender _ _ => W ⊕ Unit
  | .stepChallenge _ => W ⊕ Option Msg

def oracleImpl (proto : MTP.Scheme ProbComp Msg SendK RecvK W) (sendk : SendK) :
    QueryImpl (oracleSpec Msg W) (StateT (Env proto) ProbComp) := fun op =>
  match op with
  | .openSender m => do
      let r ← (proto.sender.init (sendk, m) : ProbComp _)
      let env ← get
      let (tr, c') := recordOpt ⟨[]⟩ r.opening env.clock
      let sid := env.senders.length
      let s0 : Session proto.sender.State W := ⟨r.state, tr⟩
      set { env with clock := c', senders := env.senders ++ [s0] }
      pure (sid, r.opening)
  | .stepSender sid w => do
      let env ← get
      match env.senders[sid]? with
      | none => pure (.inr ())
      | some s =>
        match ← (proto.sender.step s.state w : ProbComp _) with
        | .reject => pure (.inr ())
        | .acceptAndSend st' w' _ =>
            let (tr1, c1) := recordOne s.transcript w env.clock
            let (tr2, c2) := recordOne tr1 w' c1
            set { env with clock := c2, senders := env.senders.set sid ⟨st', tr2⟩ }
            pure (.inl w')
        | .complete st' =>
            let (tr1, c1) := recordOne s.transcript w env.clock
            set { env with clock := c1, senders := env.senders.set sid ⟨st', tr1⟩ }
            pure (.inr ())
  | .stepChallenge w => do
      let env ← get
      match env.challengeOutput with
      | some m => pure (.inr m)
      | none => do
          match ← (proto.receiver.step env.challenge.state w : ProbComp _) with
          | .reject => pure (.inr none)
          | .acceptAndSend st' w' _ =>
              let (tr1, c1) := recordOne env.challenge.transcript w env.clock
              let (tr2, c2) := recordOne tr1 w' c1
              set { env with clock := c2, challenge := ⟨st', tr2⟩ }
              pure (.inl w')
          | .complete st' =>
              let (tr1, c1) := recordOne env.challenge.transcript w env.clock
              let o ← (proto.receiver.output st' : ProbComp _)
              set { env with clock := c1, challenge := ⟨st', tr1⟩, challengeOutput := some o.join }
              pure (.inr o.join)

structure Adversary (proto : MTP.Scheme ProbComp Msg SendK RecvK W) where
  run : RecvK → OracleComp (unifSpec + oracleSpec Msg W) Unit

structure Result (proto : MTP.Scheme ProbComp Msg SendK RecvK W) where
  mstar : Option Msg
  challengeTr : Transcript W
  oracleTrs : List (Transcript W)

def challengeSession {proto : MTP.Scheme ProbComp Msg SendK RecvK W} (A : Adversary proto)
    (sendk : SendK) (recvk : RecvK) : ProbComp (Result proto) := do
  let r0 ← (proto.receiver.init recvk : ProbComp _)
  let init : Env proto := ⟨0, ⟨r0.state, ⟨[]⟩⟩, none, []⟩
  let (_, env) ← (simulateQ (withUnif (oracleImpl proto sendk)) (A.run recvk)).run init
  pure ⟨env.challengeOutput.join, env.challenge.transcript, env.senders.map (·.transcript)⟩

def isPingPong [DecidableEq W] {proto : MTP.Scheme ProbComp Msg SendK RecvK W}
    (r : Result proto) : Bool :=
  pingPong (proto.rounds % 2 == 1) r.oracleTrs r.challengeTr

def Exp [DecidableEq W] {proto : MTP.Scheme ProbComp Msg SendK RecvK W} (A : Adversary proto) :
    ProbComp Bool := do
  let (sendk, recvk) ← proto.setup
  let r ← challengeSession A sendk recvk
  if r.mstar.isSome && !isPingPong r then return true
  else return false

noncomputable def advantage [DecidableEq W] {proto : MTP.Scheme ProbComp Msg SendK RecvK W}
    (A : Adversary proto) : ℝ :=
  (Pr[= true | Exp A]).toReal

end AKE.ICMA
