/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import ToVCVio.CryptoFoundations.AEAD
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.SignatureAlg

open OracleSpec OracleComp

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

def EncodeEC {G PQPK : Type} (pk : G) : G ⊕ PQPK := Sum.inl pk

def EncodeKEM {G PQPK : Type} (pk : PQPK) : G ⊕ PQPK := Sum.inr pk

abbrev KeyMaterial (G SS : Type) : Type := G × G × G × Option G × SS

structure Parameters (F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type) where
  gen : G
  pqkem : KEMScheme ProbComp SS PQPK PQSK CT
  sig : SignatureAlg ProbComp (G ⊕ PQPK) SPK SSK S
  aead : AEAD.Scheme ProbComp Msg K (G × G × PQPK) C
  kdf : KeyMaterial G SS → K × K × K
  idEC : G → IdC
  idKEM : PQPK → IdK

def dhKeygen [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (gen : G) : ProbComp (G × F) := do
  let sk ← $ᵗ F
  return (sk • gen, sk)

def DH [Field F] [AddCommGroup G] [Module F G] (sk : F) (pk : G) : G := sk • pk

def genOPK [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (gen : G) (hasOPK : Bool) : ProbComp (Option (G × F)) :=
  if hasOPK then some <$> dhKeygen gen else pure none

structure InitiatorParameters (F G SPK Msg : Type) where
  ikA : G × F
  /- We include Bob's identity public key here in order to pin Bob's
    identity to Alice. This models the out-of-band key fingerprinting from Sec.
    4.1 of the spec. -/
  ikB : G
  /- DEVIATION FROM SPEC: We make a simplifying assumption that Bob's identity
  key contains independently chosen values for DH and signature scheme keys.
  This conflicts with the verbatim wording of the spec, but it is mentioned in
  Sec. 4 as a simplifying assumption used in previous analyses. -/
  sigpkB : SPK
  msg : Msg

structure RecipientIdentity (F G SPK SSK S : Type) where
  ikB : G × F
  sigkB : SPK × SSK
  spkB : G × F
  spkSigB : S

structure RecipientParameters (F G PQPK PQSK SPK SSK S : Type) where
  ikB : G × F
  sigkB : SPK × SSK
  spkB : G × F
  spkSigB : S
  opkB : Option (G × F)
  pqpkB : PQPK × PQSK

structure PreKeyBundle (G PQPK S IdC IdK : Type) where
  ikB : G
  spkB : G × IdC
  spkSigB : S
  pqpkB : PQPK × IdK
  pqpkSigB : S
  opkB : Option (G × IdC)
  deriving DecidableEq

structure InitialMessage (G CT C IdC IdK : Type) where
  ikA : G
  ekA : G
  ct : CT
  idSPK : IdC
  idPQPK : IdK
  idOPK : Option IdC
  ctxt : C
  deriving DecidableEq

structure SessionContext (G PQPK Msg K : Type) where
  sk : K
  kb : K
  ad : G × G × PQPK
  msg : Msg

def setup [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters F G SPK Msg ×
      RecipientIdentity F G SPK SSK S) := do
  let ikA ← dhKeygen P.gen
  let ikB ← dhKeygen P.gen
  let sigkB ← P.sig.keygen
  let spkB ← dhKeygen P.gen
  let spkSigB ← P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.1)
  return ({ ikA := ikA, ikB := ikB.1, sigpkB := sigkB.1, msg := msg },
    { ikB := ikB, sigkB := sigkB, spkB := spkB, spkSigB := spkSigB })

def publish (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : RecipientParameters F G PQPK PQSK SPK SSK S) :
    ProbComp (PreKeyBundle G PQPK S IdC IdK) := do
  let pqpkSigB ← P.sig.sign p.sigkB.1 p.sigkB.2 (EncodeKEM p.pqpkB.1)
  return { ikB := p.ikB.1
           spkB := (p.spkB.1, P.idEC p.spkB.1)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }

def initiate [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, SS) ← P.pqkem.encaps bundle.pqpkB.1
  let DH1 := DH p.ikA.2 bundle.spkB.1
  let DH2 := DH ekA.2 bundle.ikB
  let DH3 := DH ekA.2 bundle.spkB.1
  let DH4 := bundle.opkB.map fun opk => DH ekA.2 opk.1
  /- DEVIATION FROM SPEC: It seems necessary to assume that the keys used for
    the AEAD encrypted ciphertexts are independent of SK and of each other.
    Here, we make them distinct outputs of the KDF. Using SK to key the AEAD
    and revealing the message appears to be incompatible with key
    indistinguishability, since an attacker can distinguish the key from random
    by using the candidate key to decrypt the initial message and checking
    whether it succeeds. -/
  let (SK, KA, KB) := P.kdf (DH1, DH2, DH3, DH4, SS)
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt KA AD p.msg
  return some ({ ikA := p.ikA.1
                 ekA := ekA.1
                 ct := CT
                 idSPK := bundle.spkB.2
                 idPQPK := bundle.pqpkB.2
                 idOPK := bundle.opkB.map Prod.snd
                 ctxt := ctxt },
    { sk := SK, kb := KB, ad := AD, msg := p.msg })

def accept [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : RecipientParameters F G PQPK PQSK SPK SSK S)
    (msg : InitialMessage G CT C IdC IdK) :
    ProbComp (Option (SessionContext G PQPK Msg K)) := do
  if msg.idSPK ≠ P.idEC p.spkB.1 ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.1) then return none
  let some SS ← P.pqkem.decaps p.pqpkB.2 msg.ct | return none
  let DH1 := DH p.spkB.2 msg.ikA
  let DH2 := DH p.ikB.2 msg.ekA
  let DH3 := DH p.spkB.2 msg.ekA
  let DH4 := p.opkB.map fun opk => DH opk.2 msg.ekA
  let (SK, KA, KB) := P.kdf (DH1, DH2, DH3, DH4, SS)
  let AD := (msg.ikA, p.ikB.1, p.pqpkB.1)
  match P.aead.decrypt KA AD msg.ctxt with
  | some m => return some { sk := SK, kb := KB, ad := AD, msg := m }
  | none => return none

def confirm [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (ctx : SessionContext G PQPK Msg K) (conf : C) : Option K :=
  if P.aead.decrypt ctx.kb ctx.ad conf = some ctx.msg then some ctx.sk
  else none

end PQXDH
