/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.Extracted.Pqxdh
import PQXDH.Spec.Basic
import PQXDH.Spec.UAKE.Defs
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import PQXDH.AKE.UAKE.Transport
import ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# PQXDH as a UAKE, Instantiated with the Simplified Aeneas Extraction

This module realizes the Spec UAKE construction with the PQXDH demo crate, as
extracted by Aeneas. The key-agreement orchestration (`pqxdh_initiate`,
`pqxdh_accept`, and the KDF input layout) is extracted Rust; the cryptographic
primitives (X25519, ML-KEM, HKDF, canonicality checking) are opaque axioms.

Deviations from a pure "extracted code as UAKE" instantiation
* **Abstract primitives in `Parameters`:** key generation, encapsulation
  coins, the signature scheme, and the AEAD are abstract parameters; the demo
  crate does not implement them. See `Parameters`.
* **Wrapper-level protocol steps:** Bob's identity pin, the pre-key signature
  checks, key identifiers, and both AEAD messages live in the Lean wrappers
  rather than the extracted Rust. See `initiate`, `accept`, `confirm`, and
  `recipient`.
* **Defaults on failure:** wrappers coerce `Result` failures of opaque calls
  to rejections or default values. See `pqkem`, `x25519DH`, and `kdfPRF`;
  totality of the opaque calls is tracked by `DeriveKeysTotal` and
  `EncapsTotalAll`.
* **Bob's extra message:** as in the Spec model, the T=Bob scheme adds a
  confirmation message from Bob so that T speaks last. See `recipient` and
  bullet 1 of "Model simplifications" in `PQXDH.Spec.Basic`.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

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

/-- A 32-byte X25519 key (either half of a key pair). -/
abbrev ECKey : Type := Bytes 32#usize

/-- An ML-KEM-1024 public key (1568 bytes). -/
abbrev PQPK : Type := Bytes 1568#usize

/-- An ML-KEM-1024 secret key (3168 bytes). -/
abbrev PQSK : Type := Bytes 3168#usize

/-- An ML-KEM-1024 ciphertext plus its one-byte key-type tag (1569 bytes). -/
abbrev CT : Type := Bytes 1569#usize

/-- A 32-byte KEM shared secret. -/
abbrev SS : Type := Bytes 32#usize

/-- A 32-byte derived key. -/
abbrev Key : Type := Bytes 32#usize

/-- Explicit 32-byte randomness for derandomized encapsulation. -/
abbrev Coins : Type := Bytes 32#usize

/-- The value of a successful `Result`, or `default` on failure. -/
def getOk {α : Type} [Inhabited α] : Aeneas.Std.Result α → α
  | .ok x => x
  | _ => default

/-- The extracted key derivation: build the secret input from the DH outputs
  and the KEM secret (with or without the OPK), run HKDF, and split the
  96-byte output into `(root_key, chain_key, pqr_key)`. -/
def deriveKeys (dh1 dh2 dh3 : ECKey) (dh4 : Option ECKey) (ss : SS) :
    Aeneas.Std.Result (Key × Key × Key) := do
  let okm ← match dh4 with
    | none => do
        let secretInput ← pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice secretInput)
        let s1 ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice pqxdh.PQXDH_LABEL)
        pqxdh.hkdf_sha256_derive s s1
    | some dh4 => do
        let secretInput ← pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice secretInput)
        let s1 ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice pqxdh.PQXDH_LABEL)
        pqxdh.hkdf_sha256_derive s s1
  pqxdh.derive_split okm

/-- Totality of the extracted KDF: `deriveKeys` succeeds on every input. -/
def DeriveKeysTotal : Prop :=
  ∀ (dh1 dh2 dh3 : ECKey) (dh4 : Option ECKey) (ss : SS),
    ∃ ks, deriveKeys dh1 dh2 dh3 dh4 ss = .ok ks

variable {SPK SSK S C Msg IdC IdK : Type}

/-- Constants and primitive cryptographic operations used by the extracted
  PQXDH. The primitives the demo crate leaves abstract (key generation,
  encapsulation coins, signatures, AEAD, key identifiers) are parameters here,
  as in the Spec model. -/
structure Parameters (SPK SSK S C Msg IdC IdK : Type) where
  /-- Generator for X25519 key pairs. -/
  ecKeygen : ProbComp pqxdh.KeyPair
  /-- Generator for ML-KEM key pairs. -/
  pqKeygen : ProbComp (PQPK × PQSK)
  /-- Randomness source for derandomized encapsulation. -/
  encapsCoins : ProbComp Coins
  /-- Signature scheme used for signing keys. -/
  sig : SignatureAlg ProbComp (ECKey ⊕ PQPK) SPK SSK S
  /-- AEAD used for the protocol's AEAD messages. -/
  aead : AEAD.Scheme ProbComp Msg Key (ECKey × ECKey × PQPK) C
  /-- Function that maps a DH public key to key identifiers. -/
  idEC : ECKey → IdC
  /-- Function that maps a KEM public key to key identifiers. -/
  idKEM : PQPK → IdK

/-- The parameters given to Alice on startup; the extracted counterpart of
  `PQXDH.InitiatorParameters`. -/
structure InitiatorParameters (SPK Msg : Type) where
  /-- Alice's long-term identity X25519 key pair. -/
  ikA : pqxdh.KeyPair
  /-- Bob's identity public key, pinning Bob's identity to Alice. -/
  ikB : ECKey
  /-- Bob's signature-scheme public key. -/
  sigpkB : SPK
  /-- The message Alice sends in the initial AEAD ciphertext. -/
  msg : Msg

/-- Bob's long- and medium-term key pairs; the extracted counterpart of
  `PQXDH.RecipientIdentity`. -/
structure RecipientIdentity (SPK SSK S : Type) where
  /-- Bob's identity X25519 key pair. -/
  ikB : pqxdh.KeyPair
  /-- Bob's signature key pair. -/
  sigkB : SPK × SSK
  /-- Bob's signed (medium-term) pre-key pair. -/
  spkB : pqxdh.KeyPair
  /-- Bob's signature for his SPK. -/
  spkSigB : S

/-- The parameters given to Bob on startup; the extracted counterpart of
  `PQXDH.RecipientParameters`. -/
structure RecipientParameters (SPK SSK S : Type) where
  /-- Bob's identity X25519 key pair. -/
  ikB : pqxdh.KeyPair
  /-- Bob's signature key pair. -/
  sigkB : SPK × SSK
  /-- Bob's signed (medium-term) pre-key pair. -/
  spkB : pqxdh.KeyPair
  /-- Bob's signature for his SPK. -/
  spkSigB : S
  /-- Bob's one-time key pair (which may be absent). -/
  opkB : Option pqxdh.KeyPair
  /-- Bob's (short-term) KEM key pair. -/
  pqpkB : PQPK × PQSK

/-- The extracted ML-KEM operations packaged as a VCVio `KEMScheme`.
  * NOT EXTRACTED: encapsulation draws its coins from `P.encapsCoins`, and both
    operations coerce failures of the opaque calls to `default` or `none`. -/
def pqkem (P : Parameters SPK SSK S C Msg IdC IdK) :
    KEMScheme ProbComp SS PQPK PQSK CT where
  keygen := P.pqKeygen
  encaps := fun pk => do
    let coins ← P.encapsCoins
    match pqxdh.mlkem_encapsulate pk coins with
    | .ok (ss, ct) => return (ct, ss)
    | _ => return default
  decaps := fun sk ct =>
    match pqxdh.mlkem_decapsulate sk ct with
    | .ok ss => return some ss
    | _ => return none

/-- X25519 agreement commutes on key pairs drawn from `ecKeygen`: the shared
  secret is the same computed from either side. A hypothesis of the
  correctness theorems; it cannot be discharged for an abstract `ecKeygen`. -/
def AgreeComm (P : Parameters SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    pqxdh.x25519_agree kp₁.private_key kp₂.public_key
      = pqxdh.x25519_agree kp₂.private_key kp₁.public_key

/-- The extracted KDF modeled as a PRF keyed by the KEM shared secret.
  * MODEL SIMPLIFICATION: mirrors `PQXDH.kdfPRF` in the Spec model. -/
def kdfPRF : PRFScheme SS (ECKey × ECKey × ECKey × Option ECKey) (Key × Key × Key) where
  keygen := $ᵗ SS
  eval := fun ss q => getOk (deriveKeys q.1 q.2.1 q.2.2.1 q.2.2.2 ss)

/-- The extracted KDF modeled as a PRF keyed by the DH3 slot of the key
  material, with keys sampled as X25519 key pairs.
  * MODEL SIMPLIFICATION: mirrors `PQXDH.kdfPRFDH` in the Spec model. -/
def kdfPRFDH (P : Parameters SPK SSK S C Msg IdC IdK) :
    PRFScheme pqxdh.KeyPair (ECKey × ECKey × Option ECKey × SS) (Key × Key × Key) where
  keygen := P.ecKeygen
  eval := fun kp q => getOk (deriveKeys q.1 q.2.1 kp.public_key q.2.2.1 q.2.2.2)

/-- X25519 agreement as a total function, coercing failure to `default`. -/
def x25519DH (kp : pqxdh.KeyPair) (pk : ECKey) : ECKey :=
  getOk (pqxdh.x25519_agree kp.private_key pk)

/-- Generate a DH OPK only if `hasOPK` is true. -/
def genOPK (keygen : ProbComp pqxdh.KeyPair) (hasOPK : Bool) :
    ProbComp (Option pqxdh.KeyPair) :=
  if hasOPK then some <$> keygen else pure none

/-- Create the long-term state used by Alice and Bob respectively for all
  sessions. -/
def setup (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters SPK Msg × RecipientIdentity SPK SSK S) := do
  let ikA ← P.ecKeygen
  let ikB ← P.ecKeygen
  let sigkB ← P.sig.keygen
  let spkB ← P.ecKeygen
  let spkSigB ← P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)
  return ({ ikA := ikA, ikB := ikB.public_key, sigpkB := sigkB.1, msg := msg },
    { ikB := ikB, sigkB := sigkB, spkB := spkB, spkSigB := spkSigB })

/-- Compute Bob's key bundle to send to Alice.
  * DEVIATION FROM SPEC: In the spec, this is retrieved by Alice from a
    third-party server, however in UAKE, we have only two parties. Therefore,
    we make this a message from Bob. -/
def publish (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S) :
    ProbComp (PreKeyBundle ECKey PQPK S IdC IdK) := do
  let pqpkSigB ← P.sig.sign p.sigkB.1 p.sigkB.2 (EncodeKEM p.pqpkB.1)
  return { ikB := p.ikB.public_key
           spkB := (p.spkB.public_key, P.idEC p.spkB.public_key)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.public_key, P.idEC opk.public_key) }

/-- Compute Alice's initial message to Bob around the extracted
  `pqxdh_initiate`.
  * NOT EXTRACTED: Bob's identity pin, the pre-key signature checks, and the
    AEAD encryption happen here in the wrapper; the key agreement itself is
    extracted code. -/
def initiate (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : InitiatorParameters SPK Msg)
    (bundle : PreKeyBundle ECKey PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage ECKey CT C IdC IdK ×
      SessionContext ECKey PQPK Msg Key)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA ← P.ecKeygen
  let coins ← P.encapsCoins
  match pqxdh.pqxdh_initiate
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := bundle.ikB
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_kyber_pre_key := bundle.pqpkB.1 } coins with
  | .ok agreement =>
      let SK := agreement.keys.root_key
      let KA := agreement.keys.chain_key
      let KB := agreement.keys.pqr_key
      let AD := (p.ikA.public_key, bundle.ikB, bundle.pqpkB.1)
      let ctxt ← P.aead.encrypt KA AD p.msg
      return some ({ ikA := p.ikA.public_key
                     ekA := ekA.public_key
                     ct := agreement.kyber_ciphertext
                     idSPK := bundle.spkB.2
                     idPQPK := bundle.pqpkB.2
                     idOPK := bundle.opkB.map Prod.snd
                     ctxt := ctxt },
        { sk := SK, kb := KB, ad := AD, msg := p.msg })
  | _ => return none

/-- Bob's acceptance procedure around the extracted `pqxdh_accept`: check the
  key identifiers, run the extracted key agreement, and check that Alice's
  AEAD ciphertext decrypts. Also return the key, message, and AD for Bob's own
  AEAD ciphertext.
  * NOT EXTRACTED: the identifier checks and the AEAD decryption happen here
    in the wrapper.
  * DEVIATION FROM SPEC: Bob's AEAD ciphertext is not present in the spec; see
    bullet 1 of "Model simplifications" in `PQXDH.Spec.Basic`. -/
def accept [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S)
    (msg : InitialMessage ECKey CT C IdC IdK) :
    ProbComp (Option (SessionContext ECKey PQPK Msg Key)) := do
  if msg.idSPK ≠ P.idEC p.spkB.public_key ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.public_key) then return none
  match pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := msg.ikA
        their_ephemeral_key := msg.ekA
        their_kyber_ciphertext := msg.ct } with
  | .ok (some keys) =>
      let AD := (msg.ikA, p.ikB.public_key, p.pqpkB.1)
      match P.aead.decrypt keys.chain_key AD msg.ctxt with
      | some m =>
          return some { sk := keys.root_key, kb := keys.pqr_key, ad := AD, msg := m }
      | none => return none
  | _ => return none

/-- Alice's confirmation procedure: Check if Bob's AEAD ciphertext decrypts
  with the correct message, AD, and KDF-derived key. Return the shared key, if
  so. -/
def confirm [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK)
    (ctx : SessionContext ECKey PQPK Msg Key) (conf : C) : Option Key :=
  if P.aead.decrypt ctx.kb ctx.ad conf = some ctx.msg then some ctx.sk
  else none

/-- Alice's Party state machine, which internally uses the `initiate` function
  (wrapping the extracted `pqxdh_initiate`), followed by the `confirm`
  function, which checks Bob's AEAD ciphertext (not in the spec). -/
def initiator [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
  State := InitiatorParameters SPK Msg ⊕ SessionContext ECKey PQPK Msg Key ⊕ Key
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
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
  State := RecipientParameters SPK SSK S ⊕ Key
  init := fun idn => do
    let opkB ← genOPK P.ecKeygen hasOPK
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
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (InitiatorParameters SPK Msg)
      (RecipientIdentity SPK SSK S)
      (Message ECKey PQPK CT S C IdC IdK) where
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
def initiatorNoConfirm (P : Parameters SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
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
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
  State := RecipientParameters SPK SSK S ⊕ Key
  init := fun idn => do
    let opkB ← genOPK P.ecKeygen hasOPK
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
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (RecipientIdentity SPK SSK S)
      (InitiatorParameters SPK Msg)
      (Message ECKey PQPK CT S C IdC IdK) where
  /- 2 messages sent: Bob's pre-key bundle → Alice's initiate message -/
  rounds := 2
  /- Generate long-term state using `setup`. -/
  setup := Prod.swap <$> setup P msg
  /- Bob is unkeyed party -/
  U := recipientNoConfirm P hasOPK
  /- Alice is authenticated party -/
  T := initiatorNoConfirm P

end

end PQXDH.Aeneas.Simplified
