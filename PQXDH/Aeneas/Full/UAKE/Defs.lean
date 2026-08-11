/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.Extracted.Protocol
import PQXDH.Spec.Basic
import PQXDH.Spec.UAKE.Defs
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import PQXDH.AKE.UAKE.Transport
import ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# PQXDH as a UAKE, Instantiated with the High-fidelity Aeneas Extraction

This module realizes the Spec UAKE construction with Signal's
`libsignal_protocol` crate, as extracted by Aeneas. The protocol orchestration
(`pqxdh_initiate`, `pqxdh_accept`, key derivation) is extracted Rust; the
cryptographic primitives (curve25519, ML-KEM, HKDF internals) remain opaque
axioms.

Deviations from a pure "extracted code as UAKE" instantiation
* **Abstract primitives in `Parameters`:** key generation, the randomness
  source, the signature scheme, and the AEAD are abstract parameters. The
  extracted signature scheme is packaged separately (`extractedSig`) and tied
  to `P.sig` by the correctness theorems' `SigModel` hypothesis.
* **Wrapper-level protocol steps:** Bob's identity pin, the pre-key signature
  checks, key identifiers, and both AEAD messages live in the Lean wrappers
  rather than the extracted Rust. See `initiate`, `accept`, `confirm`, and
  `recipient`.
* **Randomness threading:** the extracted functions take an explicit RNG; the
  wrappers sample it from `P.coins` and coerce failures to `none`. See
  `runRaw` and `runRes`.
* **Byte-length coercions:** the extraction does not track slice lengths, so
  32-byte keys are recovered with `toKey`; see `Assumptions.lean`.
* **Bob's extra message:** as in the Spec model, the T=Bob scheme adds a
  confirmation message from Bob so that T speaks last. See `recipient` and
  bullet 1 of "Model simplifications" in `PQXDH.Spec.Basic`.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

instance {α : Type} {n : Aeneas.Std.Usize} [DecidableEq α] :
    DecidableEq (Aeneas.Std.Array α n) :=
  inferInstanceAs (DecidableEq { l : List α // l.length = n.val })

instance : SampleableType Aeneas.Std.U8 :=
  SampleableType.ofEquiv (α := BitVec 8)
    ⟨fun bv => ⟨bv⟩, fun x => x.bv, fun _ => rfl, fun _ => rfl⟩

instance {α : Type} {n : Aeneas.Std.Usize} [SampleableType α] :
    SampleableType (Aeneas.Std.Array α n) :=
  inferInstanceAs (SampleableType (List.Vector α n.val))

instance : Fintype Aeneas.Std.U8 :=
  Fintype.ofEquiv (BitVec 8) ⟨fun bv => ⟨bv⟩, fun x => x.bv, fun _ => rfl, fun _ => rfl⟩

instance {α : Type} {n : Aeneas.Std.Usize} [Fintype α] :
    Fintype (Aeneas.Std.Array α n) :=
  inferInstanceAs (Fintype (List.Vector α n.val))

/-- Fixed-length byte arrays from the Aeneas extraction. -/
abbrev Bytes (n : Aeneas.Std.Usize) : Type := Aeneas.Std.Array Aeneas.Std.U8 n

/-- An extracted curve25519 public key. -/
abbrev ECPub : Type := libsignal_core.curve.PublicKey

/-- An extracted curve25519 private key. -/
abbrev ECPriv : Type := libsignal_core.curve.PrivateKey

/-- An extracted curve25519 key pair. A plain struct: the halves are not
  intrinsically related; see `ECKeyPairValid`. -/
abbrev ECKeyPair : Type := libsignal_core.curve.KeyPair

/-- An extracted identity key (a wrapped curve25519 public key). -/
abbrev IdKey : Type := identity_key.IdentityKey

/-- An extracted identity key pair. -/
abbrev IdKeyPair : Type := identity_key.IdentityKeyPair

/-- An extracted ML-KEM (Kyber1024) public key. -/
abbrev PQPub : Type := kem.Key kem.Public

/-- An extracted ML-KEM (Kyber1024) secret key. -/
abbrev PQPriv : Type := kem.Key kem.Secret

/-- An extracted ML-KEM key pair. -/
abbrev PQKeyPair : Type := kem.KeyPair

/-- A serialized KEM ciphertext. -/
abbrev CT : Type := Aeneas.Std.Slice Aeneas.Std.U8

/-- A 32-byte derived key. -/
abbrev Key : Type := Bytes 32#usize

/-- The extracted KDF output: root, chain, and post-quantum ratchet keys. -/
abbrev HandshakeKeys : Type := pqxdh.HandshakeKeys

/-- The extracted result of `pqxdh_initiate`: the handshake keys and the KEM
  ciphertext. -/
abbrev InitiatorAgreement : Type := pqxdh.InitiatorAgreement

scoped instance : DecidableEq ECPub := Classical.decEq _

scoped instance : DecidableEq PQPub := Classical.decEq _

scoped instance : DecidableEq (Aeneas.Std.Slice Aeneas.Std.U8) := Classical.decEq _

scoped instance : Inhabited (Aeneas.Std.Slice Aeneas.Std.U8) :=
  ⟨Aeneas.Std.Slice.new _⟩

scoped instance : Inhabited Key := ⟨Aeneas.Std.Array.repeat 32#usize 0#u8⟩

scoped instance : Inhabited kem.KeyType := ⟨kem.KeyType.Kyber1024⟩

scoped instance {T : Type} : Inhabited (kem.KeyMaterial T) :=
  ⟨{ data := default, kind := () }⟩

scoped instance {T : Type} : Inhabited (kem.Key T) :=
  ⟨{ key_type := default, key_data := default }⟩

/-- Coerce a byte slice to a 32-byte key, or `none` if the length differs.
  * NOT EXTRACTED: the extraction does not track slice lengths, so this check
    is wrapper-level; that it never fails on KEM outputs is assumed in
    `Assumptions.lean`. -/
def toKey (s : Aeneas.Std.Slice Aeneas.Std.U8) : Option Key :=
  if h : s.val.length = (32#usize : Aeneas.Std.Usize).val then some ⟨s.val, h⟩ else none

/-- Wrap a key pair's public half as an identity key. -/
def identityKeyOf (kp : ECKeyPair) : IdKey := { public_key := kp.public_key }

/-- Wrap a key pair as an identity key pair. -/
def identityKeyPairOf (kp : ECKeyPair) : IdKeyPair :=
  { identity_key := identityKeyOf kp, private_key := kp.private_key }

variable {Rand SPK SSK S C Msg IdC IdK : Type}

/-- Constants and primitive cryptographic operations used by the extracted
  PQXDH. Operations the extraction leaves abstract (randomness, key
  generation, signatures, AEAD, key identifiers) are parameters here, as in
  the Spec model. -/
structure Parameters (Rand SPK SSK S C Msg IdC IdK : Type) where
  /-- The extracted code's RNG instance. -/
  rngInst : rand.rng.Rng Rand
  /-- The extracted code's cryptographic RNG instance. -/
  cryptoRngInst : rand_core_1.CryptoRng Rand
  /-- Distribution of the explicit randomness threaded through extracted
    calls. -/
  coins : ProbComp Rand
  /-- Generator for curve25519 key pairs. -/
  ecKeygen : ProbComp ECKeyPair
  /-- Generator for ML-KEM key pairs. -/
  pqKeygen : ProbComp PQKeyPair
  /-- Signature scheme used for signing keys; instantiated with `extractedSig`
    by the `SigModel` hypothesis. -/
  sig : SignatureAlg ProbComp (ECPub ⊕ PQPub) SPK SSK S
  /-- AEAD used for the protocol's AEAD messages. -/
  aead : AEAD.Scheme ProbComp Msg Key (ECPub × ECPub × PQPub) C
  /-- Function that maps a DH public key to key identifiers. -/
  idEC : ECPub → IdC
  /-- Function that maps a KEM public key to key identifiers. -/
  idKEM : PQPub → IdK

/-- Run an extracted RNG-threading computation on randomness from `P.coins`,
  coercing failure to `none`. -/
def runRaw {α : Type} (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (f : Rand → Aeneas.Std.Result (α × Rand)) : ProbComp (Option α) := do
  let r ← P.coins
  match f r with
  | .ok (x, _) => return some x
  | _ => return none

/-- Like `runRaw`, additionally unwrapping the extracted error layer. -/
def runRes {α : Type} (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (f : Rand →
      Aeneas.Std.Result
        (Aeneas.Std.core.result.Result α error.SignalProtocolError × Rand)) :
    ProbComp (Option α) := do
  let r ← P.coins
  match f r with
  | .ok (.Ok x, _) => return some x
  | _ => return none

/-- The value of a successful extracted call, or `none` on either failure
  layer. -/
def getRes {α : Type}
    (r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α error.SignalProtocolError)) :
    Option α :=
  match r with
  | .ok (.Ok x) => some x
  | _ => none

/-- Curve25519 key generation via the extracted `KeyPair::generate`. -/
def genEC (P : Parameters Rand SPK SSK S C Msg IdC IdK) : ProbComp (Option ECKeyPair) :=
  runRaw P (libsignal_core.curve.KeyPair.generate P.rngInst P.cryptoRngInst)

/-- ML-KEM key generation via the extracted `KeyPair::generate`. -/
def genKem (P : Parameters Rand SPK SSK S C Msg IdC IdK) : ProbComp (Option PQKeyPair) :=
  runRaw P (kem.KeyPair.generate P.rngInst P.cryptoRngInst kem.KeyType.Kyber1024)

/-- Generate a DH OPK only if `hasOPK` is true. -/
def genOPK (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    ProbComp (Option ECKeyPair) :=
  if hasOPK then some <$> P.ecKeygen else pure none

/-- Run the extracted `pqxdh_initiate` on randomness from `P.coins`. -/
def runInitiate (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (ip : pqxdh.InitiatorParameters) : ProbComp (Option InitiatorAgreement) :=
  runRes P (pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst ip)

/-- Run the extracted `pqxdh_accept`. -/
def runAccept (rp : pqxdh.RecipientParameters) : Option HandshakeKeys :=
  getRes (pqxdh.pqxdh_accept rp)

/-- The root-key bytes of the extracted handshake keys. -/
def rootKeyBytes (hk : HandshakeKeys) : Key := hk.root_key.key

/-- The chain-key bytes of the extracted handshake keys. -/
def chainKeyBytes (hk : HandshakeKeys) : Key := hk.chain_key.key

/-- The post-quantum-ratchet-key bytes of the extracted handshake keys. -/
def pqrKeyBytes (hk : HandshakeKeys) : Key := hk.pqr_key

/-- The extracted ML-KEM operations packaged as a VCVio `KEMScheme`.
  * NOT EXTRACTED: encapsulation draws randomness from `P.coins`, shared
    secrets are coerced to 32-byte keys with `toKey`, and failures are coerced
    to `default` or `none`. -/
def pqkem (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    KEMScheme ProbComp Key PQPub PQPriv CT where
  keygen := do
    let kp ← P.pqKeygen
    return (kp.public_key, kp.secret_key)
  encaps := fun pk => do
    let r ← P.coins
    match kem.KeyPublic.encapsulate P.cryptoRngInst pk r with
    | .ok (.Ok (ss, ct), _) =>
      match toKey ss with
      | some k => return (ct, k)
      | none => return default
    | _ => return default
  decaps := fun sk ct =>
    return (getRes (kem.KeySecret.decapsulate sk ct)).bind toKey

/-- Package a message as the one-element multipart message the extracted
  verifier expects. -/
def sigMsgParts (m : Aeneas.Std.Slice Aeneas.Std.U8) :
    Aeneas.Std.Result (Aeneas.Std.Slice (Aeneas.Std.Slice Aeneas.Std.U8)) :=
  Aeneas.Std.lift (Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 1#usize [m]))

/-- The extracted XEd25519 signature scheme packaged as a VCVio
  `SignatureAlg`.
  * NOT EXTRACTED: signing draws randomness from `coins` and coerces failure
    to `default`; verification coerces failure to `false`. -/
def extractedSig (rngInst : rand.rng.Rng Rand) (cryptoRngInst : rand_core_1.CryptoRng Rand)
    (coins : ProbComp Rand) (keygen : ProbComp ECKeyPair)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8) :
    SignatureAlg ProbComp (ECPub ⊕ PQPub) ECPub ECPriv
      (Aeneas.Std.Slice Aeneas.Std.U8) where
  keygen := do
    let kp ← keygen
    return (kp.public_key, kp.private_key)
  sign := fun _pk sk m => do
    let r ← coins
    match libsignal_core.curve.PrivateKey.calculate_signature cryptoRngInst rngInst sk
        (encMsg m) r with
    | .ok (.Ok σ, _) => return σ
    | _ => return default
  verify := fun pk m σ =>
    match sigMsgParts (encMsg m) with
    | .ok parts =>
        match libsignal_core.curve.PublicKey.verify_signature_for_multipart_message pk
            parts σ with
        | .ok b => return b
        | _ => return false
    | _ => return false

/-- A key pair is valid when its public half is derived from its private half.
  `curve.KeyPair` is a plain struct, so this is not automatic; see
  `extractedSig_signVerify` in `Assumptions.lean`. -/
def ECKeyPairValid (kp : ECKeyPair) : Prop :=
  libsignal_core.curve.PrivateKey.public_key kp.private_key = .ok (.Ok kp.public_key)

/-- The parameters given to Alice on startup; the extracted counterpart of
  `PQXDH.InitiatorParameters`. -/
structure InitiatorParameters (SPK Msg : Type) where
  /-- Alice's long-term identity key pair. -/
  ikA : IdKeyPair
  /-- Bob's identity public key, pinning Bob's identity to Alice. -/
  ikB : IdKey
  /-- Bob's signature-scheme public key. -/
  sigpkB : SPK
  /-- The message Alice sends in the initial AEAD ciphertext. -/
  msg : Msg

/-- Bob's long- and medium-term key pairs; the extracted counterpart of
  `PQXDH.RecipientIdentity`. -/
structure RecipientIdentity (SPK SSK S : Type) where
  /-- Bob's identity key pair. -/
  ikB : IdKeyPair
  /-- Bob's signature key pair. -/
  sigkB : SPK × SSK
  /-- Bob's signed (medium-term) pre-key pair. -/
  spkB : ECKeyPair
  /-- Bob's signature for his SPK. -/
  spkSigB : S

/-- The parameters given to Bob on startup; the extracted counterpart of
  `PQXDH.RecipientParameters`. -/
structure RecipientParameters (SPK SSK S : Type) where
  /-- Bob's identity key pair. -/
  ikB : IdKeyPair
  /-- Bob's signature key pair. -/
  sigkB : SPK × SSK
  /-- Bob's signed (medium-term) pre-key pair. -/
  spkB : ECKeyPair
  /-- Bob's signature for his SPK. -/
  spkSigB : S
  /-- Bob's one-time key pair (which may be absent). -/
  opkB : Option ECKeyPair
  /-- Bob's (short-term) KEM key pair. -/
  pqpkB : PQKeyPair

/-- Create the long-term state used by Alice and Bob respectively for all
  sessions. -/
def setup (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters SPK Msg × RecipientIdentity SPK SSK S) := do
  let ikA ← P.ecKeygen
  let ikB ← P.ecKeygen
  let sigkB ← P.sig.keygen
  let spkB ← P.ecKeygen
  let spkSigB ← P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)
  return ({ ikA := identityKeyPairOf ikA, ikB := identityKeyOf ikB,
            sigpkB := sigkB.1, msg := msg },
    { ikB := identityKeyPairOf ikB, sigkB := sigkB, spkB := spkB, spkSigB := spkSigB })

/-- Compute Bob's key bundle to send to Alice.
  * DEVIATION FROM SPEC: In the spec, this is retrieved by Alice from a
    third-party server, however in UAKE, we have only two parties. Therefore,
    we make this a message from Bob. -/
def publish (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S) :
    ProbComp (PreKeyBundle ECPub PQPub S IdC IdK) := do
  let pqpkSigB ← P.sig.sign p.sigkB.1 p.sigkB.2 (EncodeKEM p.pqpkB.public_key)
  return { ikB := p.ikB.identity_key.public_key
           spkB := (p.spkB.public_key, P.idEC p.spkB.public_key)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.public_key, P.idKEM p.pqpkB.public_key)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.public_key, P.idEC opk.public_key) }

/-- Compute Alice's initial message to Bob around the extracted
  `pqxdh_initiate`.
  * NOT EXTRACTED: Bob's identity pin, the pre-key signature checks, and the
    AEAD encryption happen here in the wrapper; the key agreement itself is
    extracted code. -/
def initiate (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (p : InitiatorParameters SPK Msg)
    (bundle : PreKeyBundle ECPub PQPub S IdC IdK) :
    ProbComp (Option (InitialMessage ECPub CT C IdC IdK ×
      SessionContext ECPub PQPub Msg Key)) := do
  if bundle.ikB ≠ p.ikB.public_key then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA ← P.ecKeygen
  match ← runInitiate P
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := { public_key := bundle.ikB }
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_ratchet_key := bundle.spkB.1
        their_kyber_pre_key := bundle.pqpkB.1
        self_session := false } with
  | some agreement =>
      let SK := rootKeyBytes agreement.keys
      let KA := chainKeyBytes agreement.keys
      let KB := pqrKeyBytes agreement.keys
      let AD := (p.ikA.identity_key.public_key, bundle.ikB, bundle.pqpkB.1)
      let ctxt ← P.aead.encrypt KA AD p.msg
      return some ({ ikA := p.ikA.identity_key.public_key
                     ekA := ekA.public_key
                     ct := agreement.kyber_ciphertext
                     idSPK := bundle.spkB.2
                     idPQPK := bundle.pqpkB.2
                     idOPK := bundle.opkB.map Prod.snd
                     ctxt := ctxt },
        { sk := SK, kb := KB, ad := AD, msg := p.msg })
  | none => return none

/-- Bob's acceptance procedure around the extracted `pqxdh_accept`: check the
  key identifiers, run the extracted key agreement, and check that Alice's
  AEAD ciphertext decrypts. Also return the key, message, and AD for Bob's own
  AEAD ciphertext.
  * NOT EXTRACTED: the identifier checks and the AEAD decryption happen here
    in the wrapper.
  * DEVIATION FROM SPEC: Bob's AEAD ciphertext is not present in the spec; see
    bullet 1 of "Model simplifications" in `PQXDH.Spec.Basic`. -/
def accept [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S)
    (msg : InitialMessage ECPub CT C IdC IdK) :
    ProbComp (Option (SessionContext ECPub PQPub Msg Key)) := do
  if msg.idSPK ≠ P.idEC p.spkB.public_key ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.public_key ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.public_key) then return none
  match runAccept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_pre_key_pair := p.pqpkB
        their_identity_key := { public_key := msg.ikA }
        their_ephemeral_key := msg.ekA
        their_kyber_ciphertext := msg.ct
        self_session := false } with
  | some keys =>
      let AD := (msg.ikA, p.ikB.identity_key.public_key, p.pqpkB.public_key)
      match P.aead.decrypt (chainKeyBytes keys) AD msg.ctxt with
      | some m =>
          return some { sk := rootKeyBytes keys, kb := pqrKeyBytes keys, ad := AD, msg := m }
      | none => return none
  | none => return none

/-- Alice's confirmation procedure: Check if Bob's AEAD ciphertext decrypts
  with the correct message, AD, and KDF-derived key. Return the shared key, if
  so. -/
def confirm [DecidableEq Msg] (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (ctx : SessionContext ECPub PQPub Msg Key) (conf : C) : Option Key :=
  if P.aead.decrypt ctx.kb ctx.ad conf = some ctx.msg then some ctx.sk
  else none

/-- Alice's Party state machine, which internally uses the `initiate` function
  (wrapping the extracted `pqxdh_initiate`), followed by the `confirm`
  function, which checks Bob's AEAD ciphertext (not in the spec). -/
def initiator [DecidableEq Msg] (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) where
  State := InitiatorParameters SPK Msg ⊕ SessionContext ECPub PQPub Msg Key ⊕ Key
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

/-- Bob's Party state machine, which internally uses the `publish` and `accept`
  functions (wrapping the extracted `pqxdh_accept`), as well as sending a
  final AEAD message (not in the spec). -/
def recipient [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) where
  State := RecipientParameters SPK SSK S ⊕ Key
  init := fun idn => do
    let opkB ← genOPK P hasOPK
    let pqpkB ← P.pqKeygen
    let p : RecipientParameters SPK SSK S :=
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

/-- UAKE scheme in which Bob plays the part of the authenticated party T and
  sends a final AEAD ciphertext to match the "T speaks last" convention from
  DF'17. -/
def uakeInitiator [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (InitiatorParameters SPK Msg)
      (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) where
  /- 3 messages sent:
    Bob's pre-key bundle → Alice's initiate message → Bob's confirmation message -/
  rounds := 3
  /- Generate long-term state using `setup`. -/
  setup := setup P msg
  /- Alice is unkeyed party -/
  U := initiator P
  /- Bob is authenticated party -/
  T := recipient P hasOPK

/-- Alice's Party state machine for the 2-round scheme, which internally uses
  the `initiate` function (wrapping the extracted `pqxdh_initiate`). -/
def initiatorNoConfirm (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) where
  State := InitiatorParameters SPK Msg ⊕ Key
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr ctx.sk) (.initial im) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr SK => pure (some (some SK))
    | _ => pure none

/-- Bob's Party state machine for the 2-round scheme, which internally uses
  the `publish` and `accept` functions (wrapping the extracted
  `pqxdh_accept`). -/
def recipientNoConfirm [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) where
  State := RecipientParameters SPK SSK S ⊕ Key
  init := fun idn => do
    let opkB ← genOPK P hasOPK
    let pqpkB ← P.pqKeygen
    let p : RecipientParameters SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => pure (.complete (.inr ctx.sk))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

/-- UAKE scheme in which Alice plays the part of the authenticated party T. -/
def uakeRecipient [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (RecipientIdentity SPK SSK S)
      (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) where
  /- 2 messages sent: Bob's pre-key bundle → Alice's initiate message -/
  rounds := 2
  /- Generate long-term state using `setup`. -/
  setup := Prod.swap <$> setup P msg
  /- Bob is unkeyed party -/
  U := recipientNoConfirm P hasOPK
  /- Alice is authenticated party -/
  T := initiatorNoConfirm P

end

end PQXDH.Aeneas.Full
