import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.RustCode

open Verso.Genre Manual

#doc (Manual) "The ML-KEM Braid Protocol" =>

# Overview

The ML-KEM Braid protocol takes advantage of the incremental interface ML-KEM described above to parallelize message sending and speed recovery from compromise. Specifically, the incremental interface allows _ct1_ to be sampled after receiving just a _header_, after which _ct1_ and _ek\_vector_ - the largest components of the ciphertext and encapsulation key - can be sent in parallel.

The following is a high level description of one epoch of the ML-KEM Braid protocol.

* A samples a new ML-KEM keypair: _(dk, ek\_seed, ek\_vector) = ML-KEM-KeyGen()_{galoisnote}[{spqr "src/incremental_mlkem768.rs#L34"}[]].
* A encodes a header message, _ek\_seed || SHA3-256(ek\_seed || ek\_vector)_, and begins sending it to B in chunks{galoisnote}[{spqr "src/v1/unchunked/send_ek.rs#L82C1-L98C6"}[], {spqr "src/v1/chunked/send_ek.rs#L54"}[]].
* When B receives enough chunks to reconstruct the message, they decode and compute _(encaps\_secret, ct1, shared\_secret) = ML-KEM-Encaps1(ek\_seed, SHA3-256(ek\_seed || ek\_vector))_. B stores _encaps\_secret_ and _shared\_secret_ for later use{galoisnote}[{spqr "src/v1/unchunked/send_ct.rs#L119-L148"}[], {spqr "src/v1/chunked/send_ct.rs#L118-L138"}[]].
* B encodes _ct1_ and begins sending it to A in chunks{galoisnote}[{spqr "src/v1/unchunked/send_ct.rs#L119C16-L148C1"}[], {spqr "src/v1/chunked/send_ct.rs#L208-L223"}[]].
* When A receives the first chunk of _ct1_, they stop sending chunks of the header and start sending chunks of _ek\_vector_{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L112"}[]].
* Now A and B send their messages in parallel.
* When A receives all of _ct1_ they begin acknowledging the receipt in future messages sent to B{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L144"}[]].
* Once B receives all of _ek\_vector_ and receives an acknowledgment that _ct1_ was received, they compute _ct2 = ML-KEM-Encaps2(encaps\_secret, ek\_seed, ek\_vector)_{galoisnote}[{spqr "src/v1/unchunked/send_ct.rs#L190"}[]].
* B encodes _ct2_ and begins sending it to A in chunks{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L298"}[]].
* When A receives the first chunk of _ct2_, they stop sending chunks of _ek\_vector_{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L176"}[]].
* When A receives all of _ct2_, they decapsulate the shared secret: _shared\_secret = ML-KEM-Decaps(dk, ct1, ct2)_{galoisnote}[{spqr "src/v1/unchunked/send_ek.rs#L146"}[]].
* Now A and B switch roles. A begins waiting for a header message from B{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L223"}[]], and indicates it has moved to the next epoch when sending messages to B.
* Once B receives a message showing that A has advanced to the next epoch, they sample a new keypair and begin again{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L308-L311"}[]].

While this captures the main flow of the protocol, it does not tell us how A and B know _when_ they can use the keys returned by the protocol. Clearly, when B returns _shared\_secret_ above, they cannot use it to encrypt messages to A because A does not know _shared\_secret_ yet. This will be addressed by the values _sending\_epoch_ and _receiving\_epoch_ returned from the functions defined below - a value that tells the caller what latest epoch key known by both parties at the time a message was created.

The protocol below also performs optional authentication, with details presented in [Section 2.4](https://signal.org/docs/specifications/mlkembraid/#internal-authentication) and discussed further in [Section 3.3](https://signal.org/docs/specifications/mlkembraid/#optional-internal-authentication).

# Parameters

* *KEM*: An IND-CPA secure Key Encapsulation Mechanism that offers an incremental interface. For this document it will be one of _ML-KEM-512_, _ML-KEM-768_, or _ML-KEM-1024_. {galoisnote}[{spqr "src/incremental_mlkem768.rs"}[] itself uses _ML-KEM-768 using the rust library [libcrux\_ml\_kem](https://docs.rs/libcrux-ml-kem/latest/libcrux_ml_kem/index.html)_.]
* *Constants*: Several constants are also associated with the KEM and are needed in the protocol description:

:::table +header
* * Constant
  * ML-KEM 512
  * ML-KEM 768
  * ML-KEM 1024
* * *HEADER\_SIZE*
  * 64
  * 64
  * 64
* * *EK\_SIZE*
  * 768
  * 1152
  * 1536
* * *CT1\_SIZE*
  * 640
  * 960
  * 1408
* * *CT2\_SIZE*
  * 128
  * 128
  * 160
:::

* *Encode/Decode*: An erasure code or fountain code that can encode a long message into a stream of codewords, or chunks, so that when the receiver gets a sufficient number of these chunks, regardless of order or dropped codewords, they will be able to reconstruct the original message. Reed-Solomon based erasure codes over _GF(216)w/2_ for a chunk size of _w_ bytes are recommended. {galoisnote}[libsignal uses Reed-Solomon based erasure codes with chunks of size 32 bytes {spqr "src/encoding/polynomial.rs#L498"}[]. The polynomials used for the encoder are at most of degree 35 in v1 {spqr "src/encoding/polynomial.rs#L69"}[].]
  * *Encode(byte\_array) → encoder*: Returns a stateful encoding object that produces a stream of codewords, or _chunks_, that can be decoded to reconstruct _byte\_array_{galoisnote}[{spqr "src/encoding/polynomial.rs#L651"}[]]. These codewords are accessed by calling the method _encoder.next\_chunk()_{galoisnote}[{spqr "src/encoding/polynomial.rs#L711"}[]].
  * *Decoder.new(message\_size) → decoder*: Returns a stateful decoding object that will decode a message of length _message\_size_ from a set of codewords produced by a single encoder. It exposes the functions:
    * *decoder.add\_chunk(chunk)*: Adds a codeword to the decoder's state{galoisnote}[{spqr "src/encoding.rs#L84"}[]].
    * *decoder.has\_message() → bool*: Returns true when the decoder has received enough codewords to reconstruct the message.{galoisnote}[{spqr "src/encoding/polynomial.rs#L748"}[]]{claudenote}[`has_message()` does not exist in libsignal/SPQR as a separate function — the cited polynomial.rs:748 is `fn necessary_points(...)`, a private helper. libsignal collapses the spec's `has_message()` and `message()` into one method `decoded_message() → Option<Vec<u8>>` at polynomial.rs:860 (already cited on the next bullet); a None return means "not enough chunks yet".]
    * *decoder.message() → maybe\_byte\_array*: Returns the reconstructed message if possible, otherwise returns Null.{galoisnote}[{spqr "src/encoding/polynomial.rs#L860"}[]]
* *EPOCH\_TYPE*: The unsigned integer type used to represent epochs. We recommend using unsigned 64-bit integers{galoisnote}[{spqr "src/lib.rs#L39"}[]].
* *ToBytes(epoch)*: Represent an epoch as a byte string. When _EPOCH\_TYPE_ is a 64-bit unsigned integer, use of big-endian encoding is recommended.
* *MAC(mac\_key, msg)*: A message authentication code. _HMAC-SHA256_ is recommended and used in the library itself using libcrux{galoisnote}[{spqr "src/authenticator.rs#L99"}[]].
* *MAC\_SIZE*: Size of _MAC_'s output, in bytes. In libsignal/SPQR the size is 32 bytes{galoisnote}[{spqr "src/authenticator.rs#L34"}[]].
* *PROTOCOL\_INFO*: The concatenation of a protocol identifier, a string representation of _KEM_, and a string representation of _MAC_, separated with the delimiter "`_`", such as "`MyProtocol_MLKEM768_SHA-256`". The string representations of the ML-KEM Braid parameters are defined by the implementer.{galoisnote}[{spqr "src/authenticator.rs#L46"}[]]
* *KDF\_AUTH(root\_key, update\_key, epoch)*: 64 bytes of output from the HKDF algorithm [\[5\]](https://signal.org/docs/specifications/mlkembraid/#ref-rfc5869) using _hash_ with inputs{galoisnote}[{spqr "src/authenticator.rs#L44"}[]]:
  * _HKDF input key material_ = _update\_key_{galoisnote}[{spqr "src/authenticator.rs#L53"}[]]{claudenote}[Spec/impl divergence. The cited authenticator.rs:53 is `self.mac_key = kdf_out[32..].to_vec()` — the output-split assignment, not the IKM construction. The actual IKM in libsignal at authenticator.rs:45 is `[self.root_key.as_slice(), k].concat()` — i.e. root\_key ‖ update\_key, not just update\_key. The HKDF inputs in code differ from the spec's abstraction (see also salt note below).]
  * _HKDF salt_ = _root\_key_{galoisnote}[{spqr "src/authenticator.rs#L52"}[]]{claudenote}[Spec/impl divergence. The cited authenticator.rs:52 is `self.root_key = kdf_out[..32].to_vec()` — output split. The actual HKDF call at authenticator.rs:51 passes `&[0u8; 32]` (a zero-filled 32-byte slice) as the salt argument; root\_key is folded into the IKM at line 45 instead. So in code, salt = zero and IKM = root\_key‖update\_key, not the spec's salt = root\_key and IKM = update\_key.]
  * _HKDF info_ = PROTOCOL\_INFO || ":Authenticator Update" || ToBytes(epoch){galoisnote}[{spqr "src/authenticator.rs#L46"}[]]
  * _HKDF length_ = 64
* *KDF\_OK(shared\_secret, epoch)*: 32 bytes of output from the HKDF algorithm [\[5\]](https://signal.org/docs/specifications/mlkembraid/#ref-rfc5869) using _hash_ with inputs{galoisnote}[{spqr "src/v1/unchunked/send_ct.rs#L129"}[]]:
  * _HKDF input key material_ = _shared\_secret_
  * _HKDF salt_ = A zero-filled byte sequence with length equal to the _hash_ output length, in bytes.
  * _HKDF info_ = PROTOCOL\_INFO || ":SCKA Key" || ToBytes(epoch)
  * _HKDF length_ = 32

# Messages

Messages consist of the following fields{galoisnote}[{spqr "src/v1/chunked/states.rs#L41"}[]]:

* *epoch* (unsigned integer): Current epoch being negotiated{galoisnote}[{spqr "src/proto/pq_ratchet.proto#L46"}[]]
* *type* (enum): One of _\{None, Hdr, Ek, EkCt1Ack, Ct1Ack, Ct1, Ct2\}_ with the following meanings{galoisnote}[{spqr "src/v1/chunked/states.rs#L31"}[]]:
  * _None_: There is no payload
  * _Hdr_: The payload contains a _chunk_ of the header.
  * _Ek_: The payload contains a _chunk_ of the encapsulation key.
  * _EkCt1Ack_: The payload contains a _chunk_ of the encapsulation key, and the sender has completely received _ct1_.
  * _Ct1Ack_: No payload, but the sender has completely received _ct1_.
  * _Ct1_: The payload contains a _chunk_ of _ct1_.
  * _Ct2_: The payload contains a _chunk_ of _ct2_.
* *data* (bytes, optional): Erasure code chunk when _type_ is not one of _\{ None, Ct1Ack \}_

In what follows we will describe messages logically using object notation. Implementations may use a custom compact binary format or a general purpose serialization tool such as Protocol Buffers [\[6\]](https://signal.org/docs/specifications/mlkembraid/#ref-protobuf) to encode these messages. In the presence of bandwidth limits, implementers should consider that a custom format may allow larger chunk sizes and correspondingly improve post-compromise security (See [Section 3.4](https://signal.org/docs/specifications/mlkembraid/#bandwidth-limits-message-sizes-and-speed-of-pcs)).

# Internal Authentication

While messaging protocols such as the Double Ratchet [\[2\]](https://signal.org/docs/specifications/mlkembraid/#ref-doubleratchet) provide ratcheted message authentication through the use of AEAD or explicit MACs on messages, it may be desirable for an SCKA protocol to provide internal authenticity guarantees. We attain this using a _Ratcheted Authenticator_.

## Ratcheted Authenticator state variables

The Ratcheted Authenticator holds the following state{galoisnote}[{spqr "src/authenticator.rs#L27"}[]]:

* *root\_key*: a 32 byte value.
* *mac\_key*: a 32 byte key for use with _MAC_.

## Ratcheted Authenticator functions

The Ratcheted Authenticator offers a function to update the internal state with new entropy as well as functions to compute and verify MACs on ciphertexts and header messages{galoisnote}[{spqr "src/authenticator.rs#L33C1-L105C2"}[]].

In the event of a verification failure, protocol participants should not proceed with the ML-KEM Braid session and should negotiate a new ML-KEM Braid session .

# State Machine and Transitions

We describe the protocol as a state machine that transitions from state to state when sending or receiving messages. The states and transitions can be seen in the following figure, which can serve as a helpful reference in the detailed descriptions that follow.

State machine transitions for the ML-KEM Braid Protocol. Each transition is labeled with a number that can be found in the pseudocode below.

All states of the agents contain at least the following two variables:

* _epoch_: an unsigned integer identifying the epoch of the key being negotiated.
* _auth_: an Authenticator object.

The following describes the state of an agent when they are transmitting an encapsulation key and awaiting the corresponding ciphertext. For each state we define the SCKA _Send()_ and _Receive()_ functions.

## KeysUnsampled

Represents an agent that is ready to sample a new KEM keypair on the next _send_ event. It carries no additional state{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L16-L18"}[]].

When sending a message, the *KeysUnsampled* agent samples a new keypair, starts sending a header message, and transitions into the *KeysSampled* state. The *KeysUnsampled* agent ignores all messages it receives {galoisnote}[chunked: {spqr "src/v1/chunked/send_ek.rs#L54C1-L67C2"}[]; unchunked: {spqr "src/v1/unchunked/send_ek.rs#L82C1-L98C6"}[].]:

```rust
// UserA starts off in the state "KeysUnsampled" when sending the very first header chunk.
pub fn send_hdr_chunk<R: Rng + CryptoRng>(self, rng: &mut R) -> (KeysSampled, Chunk) {
	 // The line below calls the "unchunked" function that actually
	// constructs the header
        let (uc, hdr, mac) = self.uc.send_header(rng);
        let to_send = [hdr, mac].concat();
        let encoder = polynomial::PolyEncoder::encode_bytes(&to_send);
        let chunk = sending_hdr.next_chunk();
	// The line below is where the state transition actually happens to the "KeysSampled" state
        (KeysSampled { uc, sending_hdr }, chunk)
}
```

## KeysSampled

Represents an agent that has sampled a KEM keypair and is sending the header. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L21-L24"}[], {spqr "src/v1/unchunked/send_ek.rs#L45-L52"}[]]:

* _dk_: a KEM decapsulation key
* _ek\_vector_: vector part of a KEM encapsulation key
* _header\_encoder_

The *KeysSampled* agent sends chunks of the header{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L71-L78"}[]]. When it receives a message of type _Ct1_ it knows that the other party has received the complete header so it transitions into the *HeaderSent* state, in which it will begin sending chunks of _ek\_vector_{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L81-L97"}[]]:

```rust
 //  UserA stays in the "KeysSampled" state when sending the rest of the header chunks.
pub fn send_hdr_chunk(self) -> (KeysSampled, Chunk) {
    let Self {
            uc,
            mut sending_hdr,
        } = self;
    let chunk = sending_hdr.next_chunk();
    (KeysSampled { uc, sending_hdr }, chunk)
}
```

```rust
// UserA switches from the "KeysSampled" state to the "HeaderSent" state after receiving the first chunk of ct1 from UserB
pub fn recv_ct1_chunk(self, epoch: Epoch, chunk: &Chunk) -> HeaderSent {
        assert_eq!(epoch, self.uc.epoch);
        let decoder = polynomial::PolyDecoder::new(incremental_mlkem768::CIPHERTEXT1_SIZE);
        hax_lib::assume!(decoder.is_ok());
        let mut receiving_ct1 = decoder.expect("should be able to decode header size");
        receiving_ct1.add_chunk(chunk);
        let (uc, ek) = self.uc.send_ek();
        let encoder = polynomial::PolyEncoder::encode_bytes(&ek);
        hax_lib::assume!(encoder.is_ok());
        let sending_ek = encoder.expect("should be able to send ek");
        HeaderSent {
            uc,
            receiving_ct1,
            sending_ek,
        }
    }
```

## HeaderSent

Represents an agent that has completed sending a header, is currently sending an _ek\_vector_, and is receiving chunks of _ct1_. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L27"}[], {spqr "src/v1/unchunked/send_ek.rs#L56-L61"}[]]:

* _dk_: a KEM decapsulation key
* _ct1\_decoder_
* _ek\_encoder_

In the *HeaderSent* state, an agent sends chunks of its _ek\_vector_{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L112-L127"}[]]. When receiving a message of type _Ct1_ for the current epoch, if it has enough chunks to decode the incoming _ct1_, it transitions to the _Ct1Received_ state{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L130-L152"}[]]:

```rust
// UserA sends ek_vector in chunks and remains in state "HeaderState".
pub fn send_ek_chunk(self) -> (HeaderSent, Chunk) {
    let Self {
        uc,
        mut sending_ek,
        receiving_ct1,
    } = self;
    let chunk = sending_ek.next_chunk();
    (
        HeaderSent {
            uc,
            sending_ek,
            receiving_ct1,
        },
        chunk,
    )
}
```

```rust
// UserA makes the decision here to either switch to the "Ct1Received" state or remain in the "HeaderSent" state depending on whether or not they have received enough chunks to reconstruct ct1. The code structure is similar to what we have seen thus far.
// Note that ct1 should be 960 byte long in total. Each chunk is 32 bytes long. Meaning that the user should expect to receive 30 unique chunks before reconstructing the message.
pub fn recv_ct1_chunk(self, epoch: Epoch, chunk: &Chunk) -> HeaderSentRecvChunk {
// This assertions main purpose is to confirm that there isn't an epoch mismatch between the two users.
    assert_eq!(epoch, self.uc.epoch);
    let Self {
        uc,
        sending_ek,
        mut receiving_ct1,
    } = self;
    receiving_ct1.add_chunk(chunk);
// The user should have already changed states if they already had enough points to reconstruct ct1.
    hax_lib::assume!(
        receiving_ct1.get_pts_needed() <= polynomial::MAX_STORED_POLYNOMIAL_DEGREE_V1
    );
    if let Some(decoded) = receiving_ct1.decoded_message() {
        hax_lib::assume!(decoded.len() == 960);
        let uc = uc.recv_ct1(epoch, decoded);
        // I believe that the "Ct1Received" state is serialized and sent over to the other user [see]. When serialized, it's turned into the ct1_ack acknowledgement flag defined [here].
        HeaderSentRecvChunk::Done(Ct1Received { uc, sending_ek })
    } else {
        HeaderSentRecvChunk::StillReceiving(HeaderSent {
            uc,
            sending_ek,
            receiving_ct1,
        })
    }
}
```

## Ct1Received

Represents an agent that has completely received _ct1_ and is still sending chunks of _ek\_vector_. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L35-L38"}[], {spqr "src/v1/unchunked/send_ek.rs#L65-L72"}[]]:

* _dk_: a KEM decapsulation key
* _ct1_: The compressed public key part of a KEM ciphertext
* _ek\_encoder_

In the *Ct1Received* state an agent sends chunks of the _ek\_vector_ until it receives a chunk of _ct2_. At that point it knows _ek\_vector_ has been received so it transitions into the *EkSentCt1Received* state{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L168-L180"}[]]:

```rust
// UserA switches from "Ct1Received" to "EkSentCt1Received". The function below is the first one called when first receiving ct2.
pub fn recv_ct2_chunk(self, epoch: Epoch, chunk: &Chunk) -> EkSentCt1Received {
        assert_eq!(epoch, self.uc.epoch);
        let decoder = polynomial::PolyDecoder::new(
            incremental_mlkem768::CIPHERTEXT2_SIZE + authenticator::Authenticator::MACSIZE,
        );
        hax_lib::assume!(decoder.is_ok());
        let mut receiving_ct2 = decoder.expect("should be able to decode ct2+mac size");
        receiving_ct2.add_chunk(chunk);
        EkSentCt1Received {
            uc: self.uc,
            receiving_ct2,
        }
    }
```

## EkSentCt1Received

Represents an agent that has received _ct1_, sent _ek_, and is receiving chunks of _ct2_. Additional state includes{galoisnote}[{spqr "src/v1/unchunked/send_ek.rs#L65-L72"}[]]:

* _dk_: a KEM decapsulation key
* _ct1_: The compressed public key part of a KEM ciphertext
* _ct2\_decoder_

In the *EkSentCt1Received* state an agent doesn't send any data to the other party and it receives chunks of _ct2_. Once _ct2_ is received, it verifies the MAC, decapsulates the secret, emits the key, and transitions to the *NoHeaderReceived* state to wait for the other party to begin sending an encapsulation key for the next epoch{galoisnote}[{spqr "src/v1/chunked/send_ek.rs#L195-L234"}[]]:

```rust
pub fn recv_ct2_chunk(
    self,
    epoch: Epoch,
    chunk: &Chunk,
) -> Result<EkSentCt1ReceivedRecvChunk, Error> {
    assert_eq!(epoch, self.uc.epoch);
    let Self {
        uc,
        mut receiving_ct2,
    } = self;
    receiving_ct2.add_chunk(chunk);
    hax_lib::assume!(
        receiving_ct2.get_pts_needed() <= polynomial::MAX_STORED_POLYNOMIAL_DEGREE_V1
    );
    // If ct2 decodes properly and the mac authentication works out
    // UserA transitions from "EkSentCt1Received" to "NoHeaderReceived".
    // In other words, the users switch roles and UserA now awaits UserB's
    // header and ek_vector.
    if let Some(mut ct2) = receiving_ct2.decoded_message() {
        let mac: authenticator::Mac = ct2
            .drain(incremental_mlkem768::CIPHERTEXT2_SIZE..)
            .collect();
        hax_lib::assume!(
            ct2.len() == incremental_mlkem768::CIPHERTEXT2_SIZE
                && mac.len() == authenticator::Authenticator::MACSIZE
        );
        let (uc, sec) = uc.recv_ct2(ct2, mac)?;
        let decoder = polynomial::PolyDecoder::new(
            incremental_mlkem768::HEADER_SIZE + authenticator::Authenticator::MACSIZE,
        );
        hax_lib::assume!(decoder.is_ok());
        Ok(EkSentCt1ReceivedRecvChunk::Done((
            send_ct::NoHeaderReceived {
                uc,
                receiving_hdr: decoder.expect("should be able to decode header size"),
            },
            sec,
        )))
    } else {
        Ok(EkSentCt1ReceivedRecvChunk::StillReceiving(
            EkSentCt1Received { uc, receiving_ct2 },
        ))
    }
}
```

The following describes the state of an agent when they are transmitting a ciphertext in response to an encapsulation key.

## NoHeaderReceived

Represents an agent that is receiving a header. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L15-L19"}[], {spqr "src/v1/unchunked/send_ct.rs#L44-L47"}[]]:

* _header\_decoder_

In the *NoHeaderReceived* state an agent receives chunks of the header. Once the header has been completely received, it transitions to the *HeaderReceived* state, but does not sample the ciphertext yet{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L75-L105"}[]]:

```rust
// Depending on whether or not UserB can reconstruct the header, UserB either stays in the "NoHeaderReceivedRecvChunk" state or switch to "HeaderReceived" by the end of this function.
pub fn recv_hdr_chunk(
    self,
    epoch: Epoch,
    chunk: &Chunk,
) -> Result<NoHeaderReceivedRecvChunk, Error> {
// Recall that this protocol requires making sure that the users are at the correct epoch and state
    assert_eq!(epoch, self.uc.epoch);
    let Self {
        uc,
        mut receiving_hdr,
    } = self;
    receiving_hdr.add_chunk(chunk);
    // The line below ensures that we only receive as many chunks as we need
// to reconstruct the message. Any more would be redundant and would signal that we haven't changed states appropriately.
    hax_lib::assume!(
        receiving_hdr.get_pts_needed() <= polynomial::MAX_STORED_POLYNOMIAL_DEGREE_V1
    );
// If we can reconstruct the header, then we authenticate it and check that its of the appropriate length
    if let Some(mut hdr) = receiving_hdr.decoded_message() {
        let mac: authenticator::Mac = hdr.drain(incremental_mlkem768::HEADER_SIZE..).collect();
        hax_lib::assume!(hdr.len() == 64 && mac.len() == authenticator::Authenticator::MACSIZE);
// We can now start reconstructing the encapsulation key
        let receiving_ek =                polynomial::PolyDecoder::new(incremental_mlkem768::ENCAPSULATION_KEY_SIZE);
        hax_lib::assume!(receiving_ek.is_ok());
// We switch states since receiving the header is complete to "HeaderReceived"
        Ok(NoHeaderReceivedRecvChunk::Done(HeaderReceived {
            uc: uc.recv_header(epoch, hdr, &mac)?,
            receiving_ek: receiving_ek.expect("should be able to decode EncapsulationKey size"),
        }))
    } else {
        // Otherwise the header is still being transmitted and the user remains in the "NoHeaderReceivedRecvChunk" state.
        Ok(NoHeaderReceivedRecvChunk::StillReceiving(Self {
            uc,
            receiving_hdr,
        }))
    }
}
```

## HeaderReceived

Represents an agent that has received a header and is prepared to sample a new _ct1_ on the next send. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L22-L26"}[], {spqr "src/v1/unchunked/send_ct.rs#L51-L56"}[]]:

* _ek\_seed_: seed of a KEM encapsulation key
* _hek_: SHA3 hash of _ek\_seed || ek\_vector_
* _ek\_decoder_

In the *HeaderReceived* state an agent is ready to sample a ciphertext when asked to send. When it does this, it computes the encapsulated shared secret for this epoch and returns it to the caller. While it has an _ek\_decoder_ prepared, it will not receive any _ek\_vector_ chunks until after it has sent a _ct1_ message - and then it will have transitioned out of this state{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L118-L138"}[]]. So the _Receive_ function is a no-op:

```rust
// Here UserB switches from the "HeaderReceived" state to the "Ct1Sampled" state and will remain in this state until UserA acks receiving all of ct1
pub fn send_ct1_chunk<R: Rng + CryptoRng>(
        self,
        rng: &mut R,
    ) -> (Ct1Sampled, Chunk, EpochSecret) {
        let Self { uc, receiving_ek } = self;
        let (uc, ct1, epoch_secret) = uc.send_ct1(rng);
        let encoder = polynomial::PolyEncoder::encode_bytes(&ct1);
 let mut sending_ct1 = encoder.expect("should be able to send CTSIZE");
        let chunk = sending_ct1.next_chunk();
        (
            Ct1Sampled {
                uc,
                sending_ct1,
                receiving_ek,
            },
            chunk,
 // Note that the "epoch_secret" is just the reconstructed shared secret and the epoch identifier
            epoch_secret,
        )
    }
```

## Ct1Sampled

Represents an agent that has received a header, has sampled _ct1_, and is sending it in chunks. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L29-L34"}[], {spqr "src/v1/unchunked/send_ct.rs#L60-L69"}[]]:

* _ek\_seed_: seed of a KEM encapsulation key
* _hek_: SHA3 hash of _ek\_seed || ek\_vector_
* _encaps\_secret_: the secret material used to encapsulate a KEM ciphertext
* _ct1_: The compressed public key part of a KEM ciphertext
* _ct1\_encoder_
* _ek\_decoder_

The *Ct1Sampled* state has the most complex transition possibilities. In this state an agent is receiving chunks of _ek\_vector_ and sending chunks of _ct1_. If it receives all of _ek\_vector_ before receiving an acknowledgment that _ct1_ was received, it will transition to *EkReceivedCt1Sampled*. On the other hand, if it receives an acknowledgment that _ct1_ was received before _ek\_vector_ has been completely received, it will transition to *Ct1Acknowledged*. If this agent both receives an acknowledgment for _Ct1_ and receives the last chunk of _ek\_vector_ in a single receive call, it will compute _ct1_ and transition to *Ct2Sampled*{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L165-L206"}[]]:

```rust
pub fn recv_ek_chunk(
        self,
        epoch: Epoch,
        chunk: &Chunk,
        ct1_ack: bool,
    ) -> Result<Ct1SampledRecvChunk, Error> {
//// All the code over the here has the same structure as we've seen so far:
// 1- Combine the chunked pieces of messages
// 2- See if you have enough to reconstruct the msg
// 3- Try to reconstruct it
// 4- Ensure that the reconstructed messages is of the correct size
        let Self {
            uc,
            mut receiving_ek,
            sending_ct1,
        } = self;
        receiving_ek.add_chunk(chunk);
        hax_lib::assume!(
            receiving_ek.get_pts_needed() <= polynomial::MAX_STORED_POLYNOMIAL_DEGREE_V1
        );
	// Note that the actual reconstruction of the message happens [here]
       Ok(if let Some(decoded) = receiving_ek.decoded_message() {
            hax_lib::assume!(decoded.len() == 1152);
            let uc = uc.recv_ek(epoch, decoded)?;
///// *********************************************************************

// Assuming that UserB has received an acknowledgement that ct1 was received by UserA
if ct1_ack {
	    // If Ct1 was acked, then UserB constructs Ct2 prior to sending it in chunks. The line below is where the ML-KEM encapsulation happens [see] for more details.
                let (uc, ct2, mac) = uc.send_ct2();
                hax_lib::assume!(
                    [ct2.clone(), mac.clone()].concat().len() % 2 == 0
                        && [ct2.clone(), mac.clone()].concat().len()
                            <= (1 << 16) *  crate::encoding::polynomial::NUM_POLYS
                );
		  // UserB then switches states to "Ct2Sampled". The only way to reach "Ct2Sampled" is for UserB to receive ek_vector and UserA to receive ct1
                Ct1SampledRecvChunk::Done(Ct2Sampled {
                    uc,
                    sending_ct2: send_ct2_encoder(&ct2, &mac),
                })
       } else { // If ct1 was not acked and UserB can still reconstruct ek_vector, then UserB keeps sending chunks of Ct1 and switches over to the "EkReceivedCt1Sampled" state from the "Ct1Sampled" state. In this case, [this] is where ct1_ack is eventually received and ct2 sampled.
                Ct1SampledRecvChunk::StillSending(EkReceivedCt1Sampled { uc, sending_ct1 })
            }
        } else if ct1_ack { // If ct1 was acked but UserB could not reconstruct ek_vector, then they stop sending chunks of ct1 and still expect chunks of ek. In this case, they switched over to the state "Ct1Acknowledged".
//
// Note that in this case, UserB samples ct2 over [here] but does not send it until ek is received.
            Ct1SampledRecvChunk::StillReceiving(Ct1Acknowledged { uc, receiving_ek })
        } else { // If neither ct1 was acked nor ek_vector was receiver, UserB remains in their current state and sends over chunks of ct1 while expecting more pieces of ek_vector
            Ct1SampledRecvChunk::StillReceivingStillSending(Self {
                uc,
                receiving_ek,
                sending_ct1,
            })
        })
    }
```

## EkReceivedCt1Sampled

Represents an agent that has received an encapsulation key and is still sending _ct1_ in chunks. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L37-L40"}[], {spqr "src/v1/unchunked/send_ct.rs#L73-L82"}[]]:

* _encaps\_secret_: the secret material used to encapsulate a KEM ciphertext
* _ct1_: The compressed public key part of a KEM ciphertext
* _ek\_seed_
* _ek\_vector_
* _ct1\_encoder_

In the *EkReceivedCt1Sampled* state an agent sends chunks of _ct1_ and awaits an acknowledgment that it has been received. When that acknowledgment comes, it computes _ct2_ and transitions to the *Ct2Sampled* state{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L241-L249"}[]]:

```rust
// Once in the "EkSentCt1Received" state, UserA receives chunks of ct2 using the function below.
pub fn recv_ct2_chunk(
        self,
        epoch: Epoch,
        chunk: &Chunk,
    ) -> Result<EkSentCt1ReceivedRecvChunk, Error> {
        assert_eq!(epoch, self.uc.epoch);
        let Self {
            uc,
            mut receiving_ct2,
        } = self;
        receiving_ct2.add_chunk(chunk);
        hax_lib::assume!(
            receiving_ct2.get_pts_needed() <= polynomial::MAX_STORED_POLYNOMIAL_DEGREE_V1
        );
	// Again, this is where UserA attempts to decode Ct2
	// For more information on the decapsulation
// and the mac authentication [see]
        if let Some(mut ct2) = receiving_ct2.decoded_message() {
            let mac: authenticator::Mac = ct2
                .drain(incremental_mlkem768::CIPHERTEXT2_SIZE..)
                .collect();
            hax_lib::assume!(
                ct2.len() == incremental_mlkem768::CIPHERTEXT2_SIZE
			// The Mac size is 32 byte long [see]
                    && mac.len() == authenticator::Authenticator::MACSIZE
            );
            let (uc, sec) = uc.recv_ct2(ct2, mac)?;
            let decoder = polynomial::PolyDecoder::new(
                incremental_mlkem768::HEADER_SIZE + authenticator::Authenticator::MACSIZE,
            );
            hax_lib::assume!(decoder.is_ok());
	    // Once Ct2 has been received, the users switch roles and UserA now expects a header from UserB
   // Note that "uc" contains UserA's current epoch and is serialized and sent over to UserB to signal that they've moved on to the next epoch. The epoch itself is incremented over [here].
            Ok(EkSentCt1ReceivedRecvChunk::Done((
                send_ct::NoHeaderReceived {
                    uc,
                    receiving_hdr: decoder.expect("should be able to decode header size"),
                },
                sec,
            )))
        } else {
	// If Ct2 has not been completely received yet, then UserA remains in the current state
            Ok(EkSentCt1ReceivedRecvChunk::StillReceiving(
                EkSentCt1Received { uc, receiving_ct2 },
            ))
        }
    }
```

## Ct1Acknowledged

Represents an agent that has completed sending _ct1_ but is still receiving chunks of _ek\_vector_. Additional state includes:

* _ek\_seed_: seed of a KEM encapsulation key
* _hek_: SHA3 hash of _ek\_seed || ek\_vector_
* _encaps\_secret_: the secret material used to encapsulate a KEM ciphertext
* _ct1_: The compressed public key part of a KEM ciphertext
* _ek\_decoder_

In the *Ct1Acknowledged* state an agent receives chunks of an incoming _ek\_vector_. Once this has been completely received, it can compute _ct2_ and transition to the *Ct2Sampled* state{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L265-L289"}[], {spqr "src/v1/unchunked/send_ct.rs#L60-L69"}[]]:

```rust
pub fn recv_ek_chunk(
    self,
    epoch: Epoch,
    chunk: &Chunk,
) -> Result<Ct1AcknowledgedRecvChunk, Error> {
    let Self {
        uc,
        mut receiving_ek,
    } = self;
    receiving_ek.add_chunk(chunk);
    hax_lib::assume!(
        receiving_ek.get_pts_needed() <= polynomial::MAX_STORED_POLYNOMIAL_DEGREE_V1
    );
    Ok(if let Some(decoded) = receiving_ek.decoded_message() {
        hax_lib::assume!(decoded.len() == 1152);
        let uc = uc.recv_ek(epoch, decoded)?;
        let (uc, ct2, mac) = uc.send_ct2();
        Ct1AcknowledgedRecvChunk::Done(Ct2Sampled {
            uc,
            sending_ct2: send_ct2_encoder(&ct2, &mac),
        })
    } else {
        Ct1AcknowledgedRecvChunk::StillReceiving(Self { uc, receiving_ek })
    })
}
```

## Ct2Sampled

Represents an agent that has completed sending _ct1_, received _ek\_vector_, and is sending _ct2_. Additional state includes{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L50-L53"}[], {spqr "src/v1/unchunked/send_ct.rs#L85-L88"}[]]:

* _ct2\_encoder_

In the *Ct2Sampled* state an agent sends chunks of _ct2_ and waits for a message from the next epoch{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L298-L305"}[]]. Once a message from the next epoch is received, it transitions to the *KeysUnsampled* state and prepares to start sending a new encapsulation key{galoisnote}[{spqr "src/v1/chunked/send_ct.rs#L308-L311"}[]]:

```rust
// UserB will only call this function once they've reached the "Ct2Sampled" state, meaning that they've received ek_vector and UserA received ct1. We emphasize this point because, as we will see next, the first chunks of ct2 will act as an ek_vector_ack for UserA.
pub fn send_ct2_chunk(self) -> (Ct2Sampled, Chunk) {
        let Self {
            uc,
            mut sending_ct2,
        } = self;
        let chunk = sending_ct2.next_chunk();
        (Self { uc, sending_ct2 }, chunk)
 }
```

```rust
// Once UserB received the next epoch identifier from UserA, they switch to the "KeysUnsampled" state
pub fn recv_next_epoch(self, epoch: Epoch) -> send_ek::KeysUnsampled {
    let uc = self.uc.recv_next_epoch(epoch);
    send_ek::KeysUnsampled { uc }
}
```
