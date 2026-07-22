/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleSpec OracleComp ENNReal

namespace PQXDH.DiffieHellman

variable {F : Type} [Field F]
variable {G : Type} [AddCommGroup G] [Module F G]

def IsDH (g X Y Z : G) : Prop := ∃ x y : F, X = x • g ∧ Y = y • g ∧ Z = (x * y) • g

def GapDHAdversary (_F G : Type) :=
  G → G → G → OracleComp (unifSpec + ((G × G × G) →ₒ Bool)) G

open Classical in
noncomputable def ddhOracle (g : G) :
    QueryImpl (unifSpec + ((G × G × G) →ₒ Bool)) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    fun q : G × G × G => (pure (decide (IsDH (F := F) g q.1 q.2.1 q.2.2)) : ProbComp Bool)

variable [SampleableType F] [DecidableEq G]

noncomputable def gapDHExp (g : G) (adversary : GapDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let h ← simulateQ (ddhOracle (F := F) g) (adversary g (a • g) (b • g))
  return decide (h = (a * b) • g)

noncomputable def gapDHAdvantage (g : G) (adversary : GapDHAdversary F G) : ℝ :=
  (Pr[= true | gapDHExp g adversary]).toReal

end PQXDH.DiffieHellman
