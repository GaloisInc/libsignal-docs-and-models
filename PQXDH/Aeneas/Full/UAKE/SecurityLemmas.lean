/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.Defs

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

def getOk {α : Type} [Inhabited α] : Aeneas.Std.Result α → α
  | .ok x => x
  | _ => default

def pubBytes (p : ECPub) : Key :=
  match p.key with
  | .DjbPublicKey a => a

def pubOfBytes (b : Key) : ECPub := { key := .DjbPublicKey b }

scoped instance : Inhabited ECPub := ⟨pubOfBytes default⟩

def sliceOfKey (k : Key) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  Aeneas.Std.lift (Aeneas.Std.Array.to_slice k)

def pubSlice (p : ECPub) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  sliceOfKey (pubBytes p)

def pubOfSlice (s : Aeneas.Std.Slice Aeneas.Std.U8) : ECPub :=
  pubOfBytes ((toKey s).getD default)

def kdfInput (dh1 dh2 dh3 : Aeneas.Std.Slice Aeneas.Std.U8)
    (dh4 : Option (Aeneas.Std.Slice Aeneas.Std.U8))
    (ss : Aeneas.Std.Slice Aeneas.Std.U8) :
    Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) := do
  let i ← 32#usize * 6#usize
  let secrets := Aeneas.Std.alloc.vec.Vec.with_capacity Aeneas.Std.U8 i
  let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice
    (Aeneas.Std.Array.repeat 32#usize 255#u8))
  let secrets1 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets s
  let secrets2 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets1 dh1
  let secrets3 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets2 dh2
  let secrets4 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets3 dh3
  let secrets5 ← match dh4 with
    | none => pure secrets4
    | some d => Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets4 d
  let secrets6 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets5 ss
  pure (Aeneas.Std.alloc.vec.Vec.deref secrets6)

def deriveHK (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key) :
    Aeneas.Std.Result pqxdh.HandshakeKeys := do
  let s1 ← pubSlice dh1
  let s2 ← pubSlice dh2
  let s3 ← pubSlice dh3
  let s4 ← match dh4 with
    | none => pure none
    | some d => do let x ← pubSlice d; pure (some x)
  let ssS ← sliceOfKey ss
  let inp ← kdfInput s1 s2 s3 s4 ssS
  pqxdh.HandshakeKeys.derive inp

def deriveKeys (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key) :
    Aeneas.Std.Result (Key × Key × Key) := do
  let hk ← deriveHK dh1 dh2 dh3 dh4 ss
  pure (rootKeyBytes hk, chainKeyBytes hk, pqrKeyBytes hk)

def DeriveKeysTotal : Prop :=
  ∀ (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key),
    ∃ hk, deriveHK dh1 dh2 dh3 dh4 ss = .ok hk

def EncapsTotalAll (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ (pk : PQPub) (r : Rand),
    ∃ ss ct rest, kem.KeyPublic.encapsulate P.cryptoRngInst pk r = .ok (.Ok (ss, ct), rest)

def EncapsLengthOK (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ (pk : PQPub) (r : Rand) (ss ct : Aeneas.Std.Slice Aeneas.Std.U8) (rest : Rand),
    kem.KeyPublic.encapsulate P.cryptoRngInst pk r = .ok (.Ok (ss, ct), rest) →
      (toKey ss).isSome

def ecAgree (kp : ECKeyPair) (pk : ECPub) : ECPub :=
  match libsignal_core.curve.PrivateKey.calculate_agreement kp.private_key pk with
  | .ok (.Ok z) => pubOfSlice z
  | _ => default

def specParams (P : Parameters Rand SPK SSK S C Msg IdC IdK) (F : Type) (gen : ECPub) :
    PQXDH.Parameters F ECPub Key PQPub PQPriv CT SPK SSK S C Msg Key IdC IdK where
  gen := gen
  pqkem := pqkem P
  sig := P.sig
  aead := P.aead
  kdf := fun km => getOk (deriveKeys km.1 km.2.1 km.2.2.1 km.2.2.2.1 km.2.2.2.2)
  idEC := P.idEC
  idKEM := P.idKEM

def kdfPRF : PRFScheme Key (ECPub × ECPub × ECPub × Option ECPub) (Key × Key × Key) where
  keygen := $ᵗ Key
  eval := fun ss q => getOk (deriveKeys q.1 q.2.1 q.2.2.1 q.2.2.2 ss)

variable {F : Type}

def kpOfPair (privEnc : F → ECPriv) (p : ECPub × F) : ECKeyPair where
  public_key := p.1
  private_key := privEnc p.2

def kdfPRFDH [Field F] [AddCommGroup ECPub] [Module F ECPub] [SampleableType F]
    (gen : ECPub) :
    PRFScheme F (ECPub × ECPub × Option ECPub × Key) (Key × Key × Key) where
  keygen := $ᵗ F
  eval := fun c q => getOk (deriveKeys q.1 q.2.1 (c • gen) q.2.2.1 q.2.2.2)

def kpOfKem (pq : PQPub × PQPriv) : PQKeyPair where
  public_key := pq.1
  secret_key := pq.2

def ukOfSpec (privEnc : F → ECPriv)
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg) :
    InitiatorParameters SPK Msg where
  ikA := identityKeyPairOf (kpOfPair privEnc uk.ikA)
  ikB := { public_key := uk.ikB }
  sigpkB := uk.sigpkB
  msg := uk.msg

def tkOfSpec (privEnc : F → ECPriv)
    (tk : PQXDH.RecipientIdentity F ECPub SPK SSK S) :
    RecipientIdentity SPK SSK S where
  ikB := identityKeyPairOf (kpOfPair privEnc tk.ikB)
  sigkB := tk.sigkB
  spkB := kpOfPair privEnc tk.spkB
  spkSigB := tk.spkSigB

def rpOfSpec (privEnc : F → ECPriv)
    (rp : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S) :
    RecipientParameters SPK SSK S where
  ikB := identityKeyPairOf (kpOfPair privEnc rp.ikB)
  sigkB := rp.sigkB
  spkB := kpOfPair privEnc rp.spkB
  spkSigB := rp.spkSigB
  opkB := rp.opkB.map (kpOfPair privEnc)
  pqpkB := kpOfKem rp.pqpkB

def ECKeygenSpec [Field F] [SampleableType F]
    [AddCommGroup ECPub] [Module F ECPub]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub)
    (privEnc : F → ECPriv) : Prop :=
  P.ecKeygen = kpOfPair privEnc <$> PQXDH.dhKeygen (F := F) gen

def ECAgreeSpec [Field F] [AddCommGroup ECPub] [Module F ECPub]
    (privEnc : F → ECPriv) : Prop :=
  ∀ (a : F) (pk : ECPub),
    libsignal_core.curve.PrivateKey.calculate_agreement (privEnc a) pk
      = .ok (.Ok (getOk (pubSlice (PQXDH.DH a pk))))

def ECCanonicalSpec : Prop :=
  ∀ pk : ECPub, libsignal_core.curve.PublicKey.is_canonical pk = .ok true

structure KemPairModel (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop where
  keygen_eq : P.pqKeygen = kpOfKem <$> (pqkem P).keygen

section GroupModelBridge

variable [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub]
  (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub) (privEnc : F → ECPriv)

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma pubOfBytes_pubBytes (p : ECPub) : pubOfBytes (pubBytes p) = p := by
  cases p with | mk k => cases k with | DjbPublicKey _ => rfl

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma pubOfSlice_pubSlice (p : ECPub) : pubOfSlice (getOk (pubSlice p)) = p := by
  sorry

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma kpOfPair_public (p : ECPub × F) : (kpOfPair privEnc p).public_key = p.1 := rfl

lemma ecAgree_toSpec (hagree : ECAgreeSpec privEnc) (p : ECPub × F) (pk : ECPub) :
    ecAgree (kpOfPair privEnc p) pk = PQXDH.DH p.2 pk := by
  sorry

lemma pqxdh_initiate_toKdf (hagree : ECAgreeSpec privEnc)
    (p₁ p₂ : ECPub × F) (ikB spk : ECPub) (opk : Option ECPub) (pqpk : PQPub)
    (r : Rand) {ss ct : Aeneas.Std.Slice Aeneas.Std.U8} {rest : Rand}
    {ssK : Key} {hk : pqxdh.HandshakeKeys}
    (henc : kem.KeyPublic.encapsulate P.cryptoRngInst pqpk r = .ok (.Ok (ss, ct), rest))
    (hssK : toKey ss = some ssK)
    (hhk : deriveHK (PQXDH.DH p₁.2 spk) (PQXDH.DH p₂.2 ikB) (PQXDH.DH p₂.2 spk)
      (Option.map (fun o => PQXDH.DH p₂.2 o) opk) ssK = .ok hk) :
    pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst
      { our_identity_key_pair := identityKeyPairOf (kpOfPair privEnc p₁)
        our_ephemeral_key_pair := kpOfPair privEnc p₂
        their_identity_key := { public_key := ikB }
        their_signed_pre_key := spk
        their_one_time_pre_key := opk
        their_ratchet_key := spk
        their_kyber_pre_key := pqpk
        self_session := false } r
      = .ok (.Ok { keys := hk, kyber_ciphertext := ct }, rest) := by
  sorry

lemma pqxdh_accept_toKdf (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec)
    (q₁ q₂ : ECPub × F) (opkq : Option (ECPub × F)) (pqpk : PQKeyPair)
    (ikA ekA : ECPub) (ct : Aeneas.Std.Slice Aeneas.Std.U8)
    {ss : Aeneas.Std.Slice Aeneas.Std.U8} {ssK : Key} {hk : pqxdh.HandshakeKeys}
    (hdec : kem.KeySecret.decapsulate pqpk.secret_key ct = .ok (.Ok ss))
    (hssK : toKey ss = some ssK)
    (hhk : deriveHK (PQXDH.DH q₂.2 ikA) (PQXDH.DH q₁.2 ekA) (PQXDH.DH q₂.2 ekA)
      (Option.map (fun o => PQXDH.DH o.2 ekA) opkq) ssK = .ok hk) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := identityKeyPairOf (kpOfPair privEnc q₁)
        our_signed_pre_key_pair := kpOfPair privEnc q₂
        our_one_time_pre_key_pair := opkq.map (kpOfPair privEnc)
        our_kyber_pre_key_pair := pqpk
        their_identity_key := { public_key := ikA }
        their_ephemeral_key := ekA
        their_kyber_ciphertext := ct
        self_session := false }
      = .ok (.Ok hk) := by
  sorry

lemma genOPK_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (hasOPK : Bool) :
    genOPK P hasOPK
      = Option.map (kpOfPair privEnc) <$> PQXDH.genOPK (F := F) gen hasOPK := by
  sorry

lemma setup_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (msg : Msg) :
    setup P msg
      = Prod.map (ukOfSpec privEnc) (tkOfSpec privEnc) <$>
          PQXDH.setup (specParams P F gen) msg := by
  sorry

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma publish_toSpec
    (rp : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S) :
    publish P (rpOfSpec privEnc rp) = PQXDH.publish (specParams P F gen) rp := by
  sorry

lemma initiate_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P) (hencLen : EncapsLengthOK P)
    (hkdfTotal : DeriveKeysTotal)
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg)
    (bundle : PreKeyBundle ECPub PQPub S IdC IdK) :
    initiate P (ukOfSpec privEnc uk) bundle
      = PQXDH.initiate (specParams P F gen) uk bundle := by
  sorry

lemma accept_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hkdfTotal : DeriveKeysTotal)
    (rp : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S)
    (im : InitialMessage ECPub CT C IdC IdK) :
    accept P (rpOfSpec privEnc rp) im = PQXDH.accept (specParams P F gen) rp im := by
  sorry

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma confirm_toSpec [DecidableEq Msg]
    (ctx : SessionContext ECPub PQPub Msg Key) (conf : C) :
    confirm P ctx conf = PQXDH.confirm (specParams P F gen) ctx conf := rfl

lemma initiator_init_toSpec [DecidableEq Msg]
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg) :
    (initiator P).init (ukOfSpec privEnc uk)
      = Party.InitResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (PQXDH.initiator (specParams P F gen)).init uk := by
  sorry

lemma initiator_step_toSpec [DecidableEq Msg]
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P) (hencLen : EncapsLengthOK P)
    (hkdfTotal : DeriveKeysTotal)
    (st : PQXDH.InitiatorParameters F ECPub SPK Msg ⊕
      SessionContext ECPub PQPub Msg Key ⊕ Key)
    (w : Message ECPub PQPub CT S C IdC IdK) :
    (initiator P).step (Sum.map (ukOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (PQXDH.initiator (specParams P F gen)).step st w := by
  sorry

lemma initiator_output_toSpec [DecidableEq Msg]
    (st : PQXDH.InitiatorParameters F ECPub SPK Msg ⊕
      SessionContext ECPub PQPub Msg Key ⊕ Key) :
    (initiator P).output (Sum.map (ukOfSpec privEnc) id st)
      = (PQXDH.initiator (specParams P F gen)).output st := by
  rcases st with p | ctx | k <;> rfl

lemma recipient_init_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hkeygen : ECKeygenSpec P gen privEnc) (hK : KemPairModel P) (hasOPK : Bool)
    (tk : PQXDH.RecipientIdentity F ECPub SPK SSK S) :
    (recipient P hasOPK).init (tkOfSpec privEnc tk)
      = Party.InitResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (PQXDH.recipient (specParams P F gen) hasOPK).init tk := by
  sorry

lemma recipient_step_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool)
    (st : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S ⊕ Key)
    (w : Message ECPub PQPub CT S C IdC IdK) :
    (recipient P hasOPK).step (Sum.map (rpOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (PQXDH.recipient (specParams P F gen) hasOPK).step st w := by
  sorry

lemma recipient_output_toSpec [DecidableEq IdC] [DecidableEq IdK] (hasOPK : Bool)
    (st : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S ⊕ Key) :
    (recipient P hasOPK).output (Sum.map (rpOfSpec privEnc) id st)
      = (PQXDH.recipient (specParams P F gen) hasOPK).output st := by
  rcases st with rp | k <;> rfl

variable {msg : Msg} {hasOPK : Bool}

def _root_.AKE.UAKE.Adversary.toSpecFull
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (gen : ECPub) (privEnc : F → ECPriv)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (PQXDH.uakeInitiator (specParams P F gen) msg hasOPK) where
  State := A.State
  challenge := fun uk w => A.challenge (ukOfSpec privEnc uk) w
  post := A.post

lemma opensAtMost_toSpec
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) {q : ℕ}
    (hq : A.OpensAtMost q) : (A.toSpecFull gen privEnc).OpensAtMost q :=
  ⟨fun uk w => hq.1 (ukOfSpec privEnc uk) w, hq.2⟩

lemma initiator_sim [DecidableEq Msg]
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P) (hencLen : EncapsLengthOK P)
    (hkdfTotal : DeriveKeysTotal) :
    Party.Sim (PQXDH.initiator (specParams P F gen)) (initiator P)
      (ukOfSpec privEnc) (Sum.map (ukOfSpec privEnc) id) where
  init_eq := initiator_init_toSpec P gen privEnc
  step_eq := initiator_step_toSpec P gen privEnc hkeygen hagree hencTotal hencLen hkdfTotal
  output_eq := initiator_output_toSpec P gen privEnc

lemma recipient_sim [DecidableEq IdC] [DecidableEq IdK]
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hK : KemPairModel P)
    (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool) :
    Party.Sim (PQXDH.recipient (specParams P F gen) hasOPK) (recipient P hasOPK)
      (tkOfSpec privEnc) (Sum.map (rpOfSpec privEnc) id) where
  init_eq := recipient_init_toSpec P gen privEnc hkeygen hK hasOPK
  step_eq := recipient_step_toSpec P gen privEnc hagree hcanon hkdfTotal hasOPK
  output_eq := recipient_output_toSpec P gen privEnc hasOPK

lemma exp_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hK : KemPairModel P)
    (hencTotal : EncapsTotalAll P) (hencLen : EncapsLengthOK P)
    (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Exp A = UAKE.Exp (A.toSpecFull gen privEnc) := by
  sorry

lemma advantage_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec) (hK : KemPairModel P)
    (hencTotal : EncapsTotalAll P) (hencLen : EncapsLengthOK P)
    (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.advantage A = UAKE.advantage (A.toSpecFull gen privEnc) := by
  unfold UAKE.advantage
  rw [exp_toSpec gen privEnc hkeygen hagree hcanon hK hencTotal hencLen hkdfTotal A]

omit [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub] in
lemma kdfPRF_specParams {P : Parameters Rand SPK SSK S C Msg IdC IdK} :
    PQXDH.kdfPRF (specParams P F gen) = kdfPRF := rfl

lemma kdfPRFDH_advantage_toSpec {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc)
    (D : PRFScheme.PRFAdversary (ECPub × ECPub × Option ECPub × Key) (Key × Key × Key)) :
    (PQXDH.kdfPRFDH (specParams P F gen)).prfAdvantage D
      = (kdfPRFDH (F := F) gen).prfAdvantage D := by
  sorry

lemma nominalDDHExpReal_toSpec (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECPub) :
    DiffieHellman.nominalDDHExpReal P.ecKeygen
        (fun kp : ECKeyPair => kp.public_key) ecAgree D
      = DiffieHellman.nominalDDHExpReal (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst (fun kp pk => kp.2 • pk) D := by
  sorry

lemma nominalDDHExpRand_toSpec (hkeygen : ECKeygenSpec P gen privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECPub) :
    DiffieHellman.nominalDDHExpRand P.ecKeygen
        (fun kp : ECKeyPair => kp.public_key) D
      = DiffieHellman.nominalDDHExpRand (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst D := by
  sorry

lemma ddh_advantage_toSpec {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (D : _root_.DiffieHellman.DDHAdversary F ECPub) :
    _root_.DiffieHellman.ddhDistAdvantage gen D
      = DiffieHellman.nominalDDHDistAdvantage P.ecKeygen
          (fun kp : ECKeyPair => kp.public_key) ecAgree (D gen) := by
  sorry

end GroupModelBridge

end

end PQXDH.Aeneas.Full
