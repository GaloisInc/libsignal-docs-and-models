/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.Basic
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import PQXDH.ToMathlib
import ToVCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.ProgramLogic.Relational.Quantitative

/-!
# PQXDH modeled as a DF'17-style UAKE

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
* **Bob's extra message:** In the PQXDH spec, the exchange ends at Alice's
  first message to Bob, but UAKE requires that the last message be sent by the
  keyed party (Bob). Therefore we add an extra message from Bob under the AEAD
  at the end of the protocol. This would represent the second message in the
  conversation between Alice and Bob.
* **Medium-term secrets as long-term:** The spec describes SPK and PQSPK as
  "changed periodically", but the UAKE security game only allows for permanent
  (via setup) and per-session (via init) keys. We model SPK (and its signature)
  as permanent, along with IK{A|B}.
* **No fallback KEM key:** We do not (currently) model the spec's last-resort
  KEM key (PQSPK). We generate a one-time KEM key (PQOPKᵢ) every time. This is
  a pure simplification, and we plan to extend the model to include the
  last-resort KEM key in the future.

Protocol questions:
* **Key reuse between DH and SignatureAlg:** We assume that Bob's identity key
  contains separate keys for DH exchange and signing. This matches the "no key
  reuse" simplification mentioned in Sec. 4 of the spec that other formal
  analyses required.
* **Separate AEAD key:** The PQXDH spec uses the same KDF output for both
  Alice's AEAD key and the final result of the key exchange, but this seems to
  preclude key indistinguishability. This is because the adversary can try
  using the candidate key to decrypt Alice's message. This will fail for a
  random key (with high likelihood) but succeed for the real key, thus
  distinguishing them. The spec allows KA to be SK or PRF(SK, ·), but both
  variants break key indistinguishability. This could be easily fixed by using
  the KDF output as the key to a PRF that generates **both** SK and KA, but
  the spec **only describes a PRF-derived KA**, which is insufficient. We
  sidestep this and model the final key and Alice's AEAD (and Bob's AEAD key;
  see bullet 3 of "Model simplifications") as separate KDF outputs.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}


inductive Message (G PQPK CT S C IdC IdK : Type) where
  | bundle : PreKeyBundle G PQPK S IdC IdK → Message G PQPK CT S C IdC IdK
  | initial : InitialMessage G CT C IdC IdK → Message G PQPK CT S C IdC IdK
  | confirmation : C → Message G PQPK CT S C IdC IdK
  deriving DecidableEq

def initiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

def recipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            /- DEVIATION FROM SPEC: UAKE requires T to speak last, sending an
              authenticated message if the exchange was accepted. This prevents
              a trivial attack where the attacker simply refrains from sending
              Alice's last message, so that ping-pong is vacuously false. We
              have Bob send the final message of the exchange here in order to
              satisfy this, whereas the spec stops at Bob receiving the
              message. -/
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (RecipientIdentity F G SPK SSK S)
      (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg
  U := recipient P hasOPK
  T := initiator P

def _root_.AKE.UAKE.Adversary.OpensAtMost {K UK TK W : Type}
    {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (q : ℕ) : Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

def kdfPRF [SampleableType SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme SS (G × G × G × Option G) (K × K × K) where
  keygen := $ᵗ SS
  eval := fun ss q => P.kdf (q.1, q.2.1, q.2.2.1, q.2.2.2, ss)

def kdfPRFDH [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme F (G × G × Option G × SS) (K × K × K) where
  keygen := $ᵗ F
  eval := fun c q => P.kdf (q.1, q.2.1, c • P.gen, q.2.2.1, q.2.2.2)

end PQXDH
