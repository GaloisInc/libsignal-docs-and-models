/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Nominal-group DDH assumptions
-/

open OracleSpec OracleComp ENNReal

namespace PQXDH.DiffieHellman

def NominalDDHAdversary (PK : Type) := PK → PK → PK → ProbComp Bool

def nominalDDHExpReal {KP PK : Type} (keygen : ProbComp KP) (pk : KP → PK)
    (dh : KP → PK → PK) (adversary : NominalDDHAdversary PK) : ProbComp Bool := do
  let kpA ← keygen
  let kpB ← keygen
  adversary (pk kpA) (pk kpB) (dh kpA (pk kpB))

def nominalDDHExpRand {KP PK : Type} (keygen : ProbComp KP) (pk : KP → PK)
    (adversary : NominalDDHAdversary PK) : ProbComp Bool := do
  let kpA ← keygen
  let kpB ← keygen
  let kpC ← keygen
  adversary (pk kpA) (pk kpB) (pk kpC)

noncomputable def nominalDDHDistAdvantage {KP PK : Type} (keygen : ProbComp KP)
    (pk : KP → PK) (dh : KP → PK → PK) (adversary : NominalDDHAdversary PK) : ℝ :=
  |(Pr[= true | nominalDDHExpReal keygen pk dh adversary]).toReal -
    (Pr[= true | nominalDDHExpRand keygen pk adversary]).toReal|

variable {F : Type} [Field F]
variable {G : Type} [AddCommGroup G] [Module F G]
variable [SampleableType F]

def groupKeygen (g : G) : ProbComp (G × F) := do
  let a ← $ᵗ F
  return (a • g, a)

lemma ddhExpReal_eq_nominalDDHExpReal (g : G) (A : _root_.DiffieHellman.DDHAdversary F G) :
    _root_.DiffieHellman.ddhExpReal g A
      = nominalDDHExpReal (groupKeygen (F := F) g) Prod.fst
        (fun kp pk => kp.2 • pk) (A g) := by
  simp [_root_.DiffieHellman.ddhExpReal, nominalDDHExpReal, groupKeygen, smul_smul]

lemma ddhExpRand_eq_nominalDDHExpRand (g : G) (A : _root_.DiffieHellman.DDHAdversary F G) :
    _root_.DiffieHellman.ddhExpRand g A
      = nominalDDHExpRand (groupKeygen (F := F) g) Prod.fst (A g) := by
  simp [_root_.DiffieHellman.ddhExpRand, nominalDDHExpRand, groupKeygen]

lemma ddhDistAdvantage_eq_nominalDDHDistAdvantage (g : G)
    (A : _root_.DiffieHellman.DDHAdversary F G) :
    _root_.DiffieHellman.ddhDistAdvantage g A
      = nominalDDHDistAdvantage (groupKeygen (F := F) g) Prod.fst
        (fun kp pk => kp.2 • pk) (A g) := by
  unfold _root_.DiffieHellman.ddhDistAdvantage nominalDDHDistAdvantage
  rw [ddhExpReal_eq_nominalDDHExpReal, ddhExpRand_eq_nominalDDHExpRand]

end PQXDH.DiffieHellman
