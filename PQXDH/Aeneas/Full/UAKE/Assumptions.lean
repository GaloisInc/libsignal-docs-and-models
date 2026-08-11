/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.Defs

/-!
# Common assumptions for correctness and security proofs.

This module collects facts about the Rust implementation that appear to be
true, but which are unprovable here due to gaps in the code model extracted by
Aeneas. The lemmas and their explanations are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

/- Believed true, not provable here. ML-KEM shared secrets are 32 bytes (FIPS 203), so `toKey`
never fails on them, but the KEM bottoms out in the opaque axiom
`kem.kyber1024.…encapsulate` whose type constrains no lengths (libcrux's ML-KEM is not
extracted). Discharging this needs a length-refined model of that axiom, or extraction of the
implementation. -/
lemma encaps_toKey_isSome {R : Type}
    (inst : rand_core_1.CryptoRng R) (pk : PQPub) (r : R)
    {ss ct : Aeneas.Std.Slice Aeneas.Std.U8} {rest : R}
    (h : kem.KeyPublic.encapsulate inst pk r = .ok (.Ok (ss, ct), rest)) :
    (toKey ss).isSome := sorry

/- Believed true, not provable here, and the decapsulation-side twin of
`encaps_toKey_isSome`. ML-KEM shared secrets are 32 bytes (FIPS 203), so `toKey` never fails on
them, but the KEM bottoms out in the opaque axiom `kem.kyber1024.…decapsulate` whose type
constrains no lengths; in the Rust, `type SharedSecret = Box<[u8]>` and the length is only
asserted in tests, never enforced by a type. Discharging this needs a length-refined model of
that axiom, or extraction of the implementation. -/
lemma decaps_toKey_isSome (sk : PQPriv) (ct : Aeneas.Std.Slice Aeneas.Std.U8)
    {ss : Aeneas.Std.Slice Aeneas.Std.U8}
    (h : kem.KeySecret.decapsulate sk ct = .ok (.Ok ss)) : (toKey ss).isSome := sorry

/- Believed true, not provable as the extraction stands. Aeneas erases `Box<T>` to `T`
(note this axiom's type is `T → Result T`), so `Box::as_ref` can only be the identity; it is
an `axiom` rather than a definition because the extraction's external-model file supplies no
body. Unlike `encaps_toKey_isSome` this is a modelling stub, not a knowledge gap: giving that
axiom its evident model `fun x => .ok x` would discharge it outright. -/
lemma as_ref_eq_ok (ss : Aeneas.Std.Slice Aeneas.Std.U8) :
    Box.Insts.CoreConvertAsRef.as_ref Aeneas.Std.Global ss = .ok ss := sorry

variable {Rand : Type}

/- Believed true, not provable here: XEd25519 sign-then-verify agreement, i.e. a signature
produced by `calculate_signature` verifies under the public key derived from the same private
key. The `ECKeyPairValid` premise is necessary, not incidental: `curve.KeyPair` is a plain
struct, and Rust's `KeyPair::new`/`from_public_and_private` build one from unrelated halves, so
without it the statement is false. Discharging it needs the curve25519 internals, which the
extraction axiomatises rather than translating. -/
lemma extractedSig_signVerify
    (rngInst : rand.rng.Rng Rand) (cryptoRngInst : rand_core_1.CryptoRng Rand)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8)
    {kp : ECKeyPair} (hkp : ECKeyPairValid kp) (m : ECPub ⊕ PQPub) (r : Rand)
    {σ : Aeneas.Std.Slice Aeneas.Std.U8} {rest : Rand}
    (hsign : libsignal_core.curve.PrivateKey.calculate_signature cryptoRngInst rngInst
      kp.private_key (encMsg m) r = .ok (.Ok σ, rest)) :
    ∃ parts, sigMsgParts (encMsg m) = .ok parts ∧
      libsignal_core.curve.PublicKey.verify_signature_for_multipart_message kp.public_key
        parts σ = .ok true := sorry

/- True of the Rust, not provable here: signing always succeeds, for every signing key, message
and randomness; no validity premise is needed. `calculate_signature_for_multipart_message`
matches on `PrivateKeyData`, which has the single variant `DjbPrivateKey [u8; 32]`, and returns
`Ok(..)` unconditionally; its `Result` is vestigial. We cannot derive that here because the
extraction supplies `calculate_signature` as an opaque axiom with no body. -/
lemma extractedSig_signTotal
    (rngInst : rand.rng.Rng Rand) (cryptoRngInst : rand_core_1.CryptoRng Rand)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8)
    (sk : ECPriv) (m : ECPub ⊕ PQPub) (r : Rand) :
    ∃ σ rest, libsignal_core.curve.PrivateKey.calculate_signature cryptoRngInst rngInst sk
      (encMsg m) r = .ok (.Ok σ, rest) := sorry

end

end PQXDH.Aeneas.Full
