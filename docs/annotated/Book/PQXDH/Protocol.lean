import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.RustCode

open Verso.Genre Manual

#doc (Manual) "The PQXDH protocol" =>

# Overview

PQXDH has three phases:

1. Bob publishes his elliptic curve identity key, elliptic curve prekeys, and _pqkem_ prekeys to a server.
2. Alice fetches a "prekey bundle" from the server, and uses it to send an initial message to Bob {galoisnote}[{libsignal "rust/protocol/src/session.rs#L181-L275"}[] where Alice processes those keys].
3. Bob receives and processes Alice's initial message{galoisnote}[{libsignal "rust/protocol/src/session_management.rs#L176-L188"}[]].

The following sections explain these phases.

# Publishing keys

Bob generates a sequence of 64-byte random values _ZSPK, ZPQSPK, Z1, Z2, …_ and publishes a set of keys to the server containing:

* Bob's _curve_ identity key  _IKB_ {galoisnote}[in example: {galoistest "rust/protocol/tests/pqxdh.rs#L26"}[], {galoistest "rust/protocol/tests/support/mod.rs#L226"}[]]
* Bob's signed _curve_ prekey and its identifier _(SPKB, IdEC(SPKB))_ {galoisnote}[{galoistest "rust/protocol/tests/pqxdh.rs#L31"}[] in example, and {libsignal "rust/protocol/tests/support/mod.rs#L271-L293"}[] in tests]
* Bob's signature on the _curve_ prekey _Sig(IKB, EncodeEC(SPKB), ZSPK)_  {galoisnote}[{libsignal "rust/protocol/tests/support/mod.rs#L286"}[] in test]
* Bob's signed last-resort _pqkem_ prekey and its identifier _(PQSPKB, IdKEM(PQSPKB))_ {galoisnote}[note in section 2.5]
* Bob's signature on the _pqkem_ prekey _Sig(IKB, EncodeKEM(PQSPKB), ZPQSPK)_
* A set of Bob's one-time _curve_ prekeys _(OPKB1, OPKB2, OPKB3, …)_ along with their identifiers _(IdEC(OPKB1), IdEC(OPKB2), IdEC(OPKB3), …)_
* A set of Bob's signed one-time _pqkem_ prekeys _(PQOPKB1, PQOPKB2, PQOPKB3, …)_ along with their identifiers _(IdKEM(PQOPKB1), IdKEM(PQOPKB2), IdKEM(PQOPKB3), …)_ {galoisnote}[in example: {galoistest "rust/protocol/tests/pqxdh.rs#L32"}[], {libsignal "rust/protocol/tests/support/mod.rs#L308"}[]]
* The set of Bob's signatures on the signed one-time _pqkem_ prekeys _(Sig(IKB, EncodeKEM(PQOPKB1), Z1), Sig(IKB, EncodeKEM(PQOPKB2), Z2), Sig(IKB, EncodeKEM(PQOPKB3), Z3), …)_{galoisnote}[{libsignal "rust/protocol/tests/support/mod.rs#L310"}[]]

Bob only needs to upload his identity key to the server once. However, Bob may upload new one-time prekeys at other times (e.g. when the server informs Bob that the server's store of one-time prekeys is getting low).

For both the signed _curve_ prekey and the signed last-resort _pqkem_ prekey, Bob will upload a new prekey along with its signature using _IKB_ at some interval (e.g. once a week or once a month). The new signed prekey and its signatures will replace the previous values.

After uploading a new pair of signed _curve_ and signed last-resort _pqkem_ prekeys, Bob may keep the private key corresponding to the previous pair around for some period of time to handle messages using it that may have been delayed in transit. Eventually, Bob should delete this private key for forward secrecy (one-time prekey private keys will be deleted as Bob receives messages using them; see [Section 3.4](https://signal.org/docs/specifications/pqxdh/#receiving-the-initial-message)).

# Sending the initial message

To perform a PQXDH key agreement with Bob, Alice contacts the server and fetches a "prekey bundle" containing the following values:

* Bob's _curve_ identity key _IKB_
* Bob's signed _curve_ prekey with its identifier _(SPKB, IdEC(SPKB))_
* Bob's signature on the _curve_ prekey _Sig(IKB, EncodeEC(SPKB), ZSPK)_
* One of either Bob's signed one-time _pqkem_ prekey _PQOPKBn_ or Bob's last-resort signed _pqkem_ prekey _PQSPKB_ if no signed one-time _pqkem_ prekey remains. Call this key _PQPKB_. The bundle also contains _IdKEM(PQPKB)_
* Bob's signature on the _pqkem_ prekey _Sig(IKB, EncodeKEM(PQPKB), ZPQPK)_
* (Optionally) Bob's one-time _curve_ prekey _OPKBn_ and its identifier _IdEC(OPKBn)_

:::galois
The code itself models this as follows

```rust
// take from here
pub struct PreKeyBundleContent {
   pub registration_id: Option<u32>,
   pub device_id: Option<DeviceId>,
   pub pre_key_id: Option<PreKeyId>,
   pub pre_key_public: Option<PublicKey>,
   pub signed_pre_key_id: Option<SignedPreKeyId>,
   pub signed_pre_key_public: Option<PublicKey>,
   pub signed_pre_key_signature: Option<Vec<u8>>,
   pub identity_key: Option<IdentityKey>,
   pub kyber_pre_key_id: Option<KyberPreKeyId>,
   pub kyber_pre_key_public: Option<kem::PublicKey>,
   pub kyber_pre_key_signature: Option<Vec<u8>>,
}
```
:::

The server should provide one of Bob's _curve_ one-time prekeys if one exists and then delete it. If all of Bob's _curve_ one-time prekeys on the server have been deleted, the bundle will not contain a one-time _curve_ prekey element.

The server should prefer to provide one of Bob's _pqkem_ one-time signed prekeys _PQOPKBn_ if one exists and then delete it. If all of Bob's _pqkem_ one-time signed prekeys on the server have been deleted, the bundle will instead contain Bob's _pqkem_ last-resort signed prekey _PQSPKB_.

:::galois
(The paragraph above is highlighted because I don't think that libsignal itself handles what the server should/shouldn't do.)
:::

{galois}[Alice processes the prekey\_bundle they receive from the server {libsignal "rust/protocol/src/session.rs#L181-L275"}[] and] Alice verifies the signatures on the prekeys{galoisnote}[{libsignal "rust/protocol/src/session.rs#L201-L206"}[], {libsignal "rust/protocol/src/session.rs#L208-L213"}[]] {galois}[and checks that Bob's address and key are trusted {libsignal "rust/protocol/src/session.rs#L192-L199"}[]]. If any signature check fails, Alice aborts the protocol. Otherwise, if all signature checks pass, Alice then generates an ephemeral _curve_ key pair with public key EKA{galoisnote}[{libsignal "rust/protocol/src/session.rs#L220"}[]]. Alice additionally generates a _pqkem_ encapsulated shared secret{galoisnote}[Alice's side: {libsignal "rust/protocol/src/pqxdh.rs#L226-L230"}[]; Bob's side: {libsignal "rust/protocol/src/pqxdh.rs#L368-L373"}[].]:

```
(CT, SS) = PQKEM-ENC(PQPKB)
           shared secret SS
           ciphertext CT
```

If the bundle does not contain a _curve_ one-time prekey, she calculates:

```
DH1 = DH(IKA, SPKB) [Alice's side and Bob's side]
DH2 = DH(EKA, IKB)  [Alice's side and Bob's side]
DH3 = DH(EKA, SPKB) [Alice's side and Bob's side]
SK = KDF(DH1 || DH2 || DH3 || SS)[see 1, 2]
```

If the bundle does contain a _curve_ one-time prekey, the calculation is modified to include an additional _DH_:

```
DH4 = DH(EKA, OPKB)[Alice's side and Bob's side]
SK = KDF(DH1 || DH2 || DH3 || DH4 || SS)[see 1, 2]
```

After calculating _SK_, Alice deletes her ephemeral private key, the _DH_ outputs and the shared secret _SS_.

Alice then calculates an "associated data" byte sequence _AD_ that contains identity information for both parties:

```
AD = EncodeEC(IKA) || EncodeEC(IKB)
```

If _pqkem_ does not incorporate _PQPKB_ into the ciphertext, Alice must also append _EncodeKEM(PQPKB)_ to _AD_ (see the discussion in [Section 4.12](https://signal.org/docs/specifications/pqxdh/#preventing-kem-re-encapsulation-attacks)). Alice may optionally append additional information to _AD_, such as Alice and Bob's usernames, certificates, or other identifying information.

Alice then sends Bob an initial message containing{galoisnote}[{galoistest "rust/protocol/src/session_management.rs#L101-L110"}[]]:

* Alice's identity key _IKA_
* Alice's ephemeral key _EKA_
* The _pqkem_ ciphertext _CT_ encapsulating _SS_ for _PQPKB_
* Identifiers stating which of Bob's prekeys Alice used
* An initial ciphertext encrypted with some AEAD encryption scheme [\[5\]](https://signal.org/docs/specifications/pqxdh/#ref-aead) using _AD_ as associated data and using an encryption key which is either _SK_ or the output from some cryptographic PRF keyed by _SK_.

The initial ciphertext is typically the first message in some post-PQXDH communication protocol. In other words, this ciphertext typically has two roles, serving as the first message within some post-PQXDH protocol, and as part of Alice's PQXDH initial message.

The initial message must be encoded in an unambiguous format to avoid confusion of the message items by the recipient{galoisnote}[{libsignal "rust/protocol/src/protocol.rs#L25-L30"}[]].

After sending this, Alice deletes the ciphertext _CT_ and may continue using _SK_ or keys derived from _SK_ within the post-PQXDH protocol for communication with Bob, subject to the security considerations discussed in [Section 4](https://signal.org/docs/specifications/pqxdh/#security-considerations).

:::galois
*Note*:

The points of entry of the actual exchange between Alice and Bob happen in :

- On Alice's side this is part of `fn process_prekey_bundle()`: {libsignal "rust/protocol/src/session.rs#L245"}[].
- On Bob's side, because ciphertexts are actually serialized differently based on whether they are pre-key or "regular ratcheting" ciphertext, this is part of `fn message_decrypt_prekey()` and the `fn process_prekey_impl()` it calls: {libsignal "rust/protocol/src/session_management.rs#L219-L229"}[], {libsignal "rust/protocol/src/session.rs#L166"}[].
:::

# Receiving the initial message

Upon receiving Alice's initial message, Bob retrieves Alice's identity key and ephemeral key from the message{galoisnote}[{libsignal "rust/protocol/src/session_management.rs#L219-L229"}[]]. Bob also loads his identity private key and uses the key identifiers to load the private key(s) corresponding to the signed prekeys, one-time prekeys, and KEM key Alice used.

Using these keys, Bob calculates _PQKEM-DEC(PQPKB, CT)_ as the shared secret _SS_{galoisnote}[{libsignal "rust/protocol/src/pqxdh.rs#L368-L373"}[]] and repeats the _DH_ and _KDF_ calculations from the previous section to derive _SK_, and then deletes the _DH_ values and _SS_ values{galoisnote}[{libsignal "rust/protocol/src/pqxdh.rs#L375"}[]]{claudenote}[The cited pqxdh.rs:375 is `Ok(HandshakeKeys::derive(&secrets))` — the function's return statement. No explicit zeroization/`clear` happens there; the "deletion" of the DH and SS values is implicit via Rust drop when the `secrets` `Vec` goes out of scope at function exit. The pointer is defensible interpretively but doesn't land on code that performs the action.].

Bob then constructs the _AD_ byte sequence using _IKA_ and _IKB_ as described in the previous section. Finally, Bob attempts to decrypt the initial ciphertext using _SK_ and _AD_{galoisnote}[{libsignal "rust/protocol/src/session_management.rs#L249-L256"}[]]. If the initial ciphertext fails to decrypt, then Bob aborts the protocol and deletes _SK_.

If the initial ciphertext decrypts successfully, the protocol is complete for Bob. For forward secrecy, Bob deletes the ciphertext and any one-time prekey private key that was used. Bob may then continue using _SK_ or keys derived from _SK_ within the post-PQXDH protocol for communication with Alice subject to the security considerations discussed in [Section 4](https://signal.org/docs/specifications/pqxdh/#security-considerations).
