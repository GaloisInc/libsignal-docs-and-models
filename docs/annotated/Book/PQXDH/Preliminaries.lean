import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.RustCode

open Verso.Genre Manual

#doc (Manual) "Preliminaries" =>

# PQXDH parameters

An application using PQXDH must decide on several parameters:

:::table +header
* * Name
  * Definition
* * curve
  * A Montgomery curve for which XEdDSA [\[1\]](https://signal.org/docs/specifications/pqxdh/#ref-xeddsa) is specified, at present this is one of curve25519 or curve448 {galoisnote}[libsignal itself relies on the curve25519 implementation of the [dalek](https://doc.dalek.rs/curve25519_dalek/) library; example of key pair generation: {libsignal "rust/core/src/curve.rs#L327-L341"}[]]
* * hash
  * A 256 or 512-bit hash function (e.g. SHA-256 or SHA-512) {galoisnote}[I think that the implementation itself uses SHA-256 {libsignal "rust/protocol/src/pqxdh.rs#L79-L92"}[]]
* * info
  * An ASCII string identifying the application with a minimum length of 8 bytes
* * pqkem
  * A post-quantum key encapsulation mechanism that has IND-CCA post-quantum security (e.g. Crystals-Kyber-1024 [\[2\]](https://signal.org/docs/specifications/pqxdh/#ref-kyberfips203)) {galoisnote}[libsignal itself supports {libsignal "rust/protocol/src/kem/kyber1024.rs"}[], {libsignal "rust/protocol/src/kem/kyber768.rs"}[] and {libsignal "rust/protocol/src/kem/mlkem1024.rs"}[] and uses Kyber1024 by default {libsignal "rust/protocol/src/session_management.rs#L855"}[]]
* * aead
  * A scheme for authenticated encryption with associated data that has IND-CPA and INT-CTXT post-quantum security {galoisnote}[libsignal uses AES-CBC {libsignal "rust/protocol/src/triple_ratchet.rs#L106-L110"}[], followed by HMAC {libsignal "rust/protocol/src/protocol.rs#L110-L115"}[]]
* * EncodeEC
  * A function that encodes a curve public key into a byte sequence{galoisnote}[{libsignal "rust/core/src/curve.rs#L122-L132"}[]]
* * DecodeEC
  * A function that decodes a byte sequence into a curve public key and is the inverse of EncodeEC{galoisnote}[{libsignal "rust/core/src/curve.rs#L84-L105"}[]]
* * EncodeKEM
  * A function that encodes a pqkem public key into a byte sequence{galoisnote}[{libsignal "rust/protocol/src/kem.rs#L333-L338"}[]]
* * DecodeKEM
  * A function that decodes a byte sequence into a pqkem public key and is the inverse of EncodeKEM{galoisnote}[{libsignal "rust/protocol/src/kem.rs#L319-L331"}[]]
:::

For example, an application could choose curve as curve25519, hash as SHA-512, info as "MyProtocol", and pqkem as CRYSTALS-KYBER-1024{galoisnote}[{libsignal "rust/protocol/src/pqxdh.rs#L72-L77"}[]].

The ranges of all encoding functions must be pairwise disjoint.

The recommended implementation of EncodeEC consists of a single-byte constant representation of curve followed by little-endian encoding of the u-coordinate as specified in [\[3\]](https://signal.org/docs/specifications/pqxdh/#ref-rfc7748). The single-byte representation of curve is defined by the implementer. Similarly the recommended implementation of DecodeEC reads the first byte to determine the parameter curve. If the first byte does not represent a recognized curve, the function fails. Otherwise it applies the little-endian decoding of the u-coordinate for curve as specified in [\[3\]](https://signal.org/docs/specifications/pqxdh/#ref-rfc7748).

The recommended implementation of EncodeKEM consists of a single-byte constant representation of pqkem followed by the encoding of the pqkem public key specified by pqkem. The single-byte representation of pqkem is defined by the implementer. Similarly the recommended implementation of DecodeKEM reads the first byte to determine the parameter pqkem. If the first byte does not represent a recognized key encapsulation mechanism, the function fails. Otherwise it applies the decoding specified by the selected key encapsulation mechanism.

:::galois
You can find examples of how keys can be encoded [here](https://github.com/signalapp/libsignal/blob/b58bd7d5dfa0a391486df4210fd83bab96b9b479/rust/protocol/src/kem.rs#L557-L567).
:::

# Elliptic Curve Keys

PQXDH uses the following elliptic curve public keys:

:::table +header
* * Name
  * Definition
* * _IKA_
  * Alice's identity key {galoisnote}[in example: {galoistest "rust/protocol/tests/pqxdh.rs#L27"}[], {galoistest "rust/protocol/tests/support/mod.rs#L226"}[]]
* * _IKB_
  * Bob's identity key {galoisnote}[in example: {galoistest "rust/protocol/tests/pqxdh.rs#L26"}[], {galoistest "rust/protocol/tests/support/mod.rs#L226"}[]]
* * _EKA_
  * Alice's ephemeral key {galoisnote}[{libsignal "rust/protocol/src/session.rs#L220"}[], which is called {galoistest "rust/protocol/tests/pqxdh.rs#L53"}[] in the example]
* * _SPKB_
  * Bob's signed prekey {galoisnote}[{galoistest "rust/protocol/tests/pqxdh.rs#L31"}[] in example]
* * (_OPKB1_, _OPKB2_, …)
  * Bob's set of one-time prekeys {galoisnote}[{galoistest "rust/protocol/tests/pqxdh.rs#L30"}[] in example]
:::

The elliptic curve public keys used within a PQXDH protocol run must either all be in curve25519 form{galoisnote}[{libsignal "rust/core/src/curve.rs#L327-L341"}[]], or they must all be in curve448 form, depending on the _curve_ parameter [\[3\]](https://signal.org/docs/specifications/pqxdh/#ref-rfc7748).

Each party has a long-term identity elliptic curve public key (_IKA_ for Alice, _IKB_ for Bob).

Bob also has a signed prekey _SPKB_, which he changes periodically and signs each time with _IKB_, and a set of one-time prekeys (_OPKB1_, _OPKB2_, …), which are each used in a single PQXDH protocol run. For each signed prekey or one-time prekey, _K_, that Bob generates, he also computes an identifier, denoted _IdEC(K)_{galoisnote}[{libsignal "rust/protocol/src/state/bundle.rs#L52"}[], {libsignal "rust/protocol/tests/support/mod.rs#L373-L378"}[]], that uniquely identifies this key on Bob's device. ("Prekeys" are so named because they are essentially protocol messages which Bob publishes to the server, along with their corresponding identifiers, prior to Alice beginning the protocol run.) These keys will be uploaded to the *server* as described in [Section 3.2](https://signal.org/docs/specifications/pqxdh/#publishing-keys).

During each protocol run, Alice generates a new ephemeral key pair with public key _EKA_.

:::galois
Note that in the code, a signed pre-key looks like:

```rust
// taken from here
struct SignedPreKey {
   id: SignedPreKeyId,
   public_key: PublicKey,
   signature: Vec<u8>,
}
```
:::

# Post-Quantum Key Encapsulation Keys

PQXDH uses the following post-quantum key encapsulation public keys:

:::table +header
* * Name
  * Definition
* * _PQSPKB_
  * Bob's signed last-resort _pqkem_ prekey {galoisnote}[last note in section]
* * (_PQOPKB1_, _PQOPKB2_, …)
  * Bob's set of signed one-time _pqkem_ prekeys {galoisnote}[prekey in example: {galoistest "rust/protocol/tests/pqxdh.rs#L32"}[], {libsignal "rust/protocol/tests/support/mod.rs#L308"}[]; signature: {libsignal "rust/protocol/tests/support/mod.rs#L310"}[]]
:::

The _pqkem_ public keys used within a PQXDH protocol run must all use the same _pqkem_ parameter.

Bob has a signed last-resort post-quantum prekey _PQSPKB_, which he changes periodically and signs each time with _IKB_, and a set of signed one-time prekeys (_PQOPKB1_, _PQOPKB2_, …) which are also signed with _IKB_ and each used in a single PQXDH protocol run. For each last-resort or ephemeral KEM key, _K_, that Bob generates, he also computes an identifier, denoted _IdKEM(K)_, that uniquely identifies this key on Bob's device. These keys and their corresponding identifiers will be uploaded to the *server* as described in [Section 3.2](https://signal.org/docs/specifications/pqxdh/#publishing-keys). The name "last-resort" refers to the fact that the last-resort prekey is only used when one-time _pqkem_ prekeys are not available. This can happen when the number of prekey bundles downloaded for Bob exceeds the number of one-time _pqkem_ prekeys Bob has uploaded (see [Section 3](https://signal.org/docs/specifications/pqxdh/#the-pqxdh-protocol) for details about the role of the server). An implementation should provide Bob a way to identify whether a _pqkem_ public key corresponds to a one-time _pqkem_ key or a last-resort _pqkem_ key.

:::galois
Note that in the code, a signed pre-key looks like:

```rust
// taken from here
struct KyberPreKey {
   id: KyberPreKeyId,
   public_key: kem::PublicKey,
   signature: Vec<u8>,
}
```

*Note:* Last resort pre-keys are created similarly to one time pre-keys; how these keys are stored when downloaded from the server: {libsignal "rust/protocol/src/storage/traits.rs#L114-L140"}[]. I believe that last resort pre-keys are created and handled at a higher level in the API when an account is registered: {libsignal "rust/net/chat/src/api/registration.rs#L287"}[], {libsignal "rust/net/chat/src/api/registration.rs#L83"}[].
:::
