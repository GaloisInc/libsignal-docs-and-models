import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.RustCode

open Verso.Genre Manual

#doc (Manual) "Note on libsignal's code structure" =>

:::galois
This entire chapter is Galois-authored commentary on the SparsePostQuantumRatchet repo structure; it has no analogue in the upstream Signal ML-KEM Braid spec.
:::

:::galois
Before going any further, we highlight how the [SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet/blob/46e387458d438b81a3485e26bf6bb44595e52073) libsignal repository is structured. As mentioned in the README, the bulk of the protocol is available under {spqr "src/v1"}[]. In there, you will find two kinds of folders:

1. {spqr "src/v1/chunked"}[] — chunked: this is where the users will receive/send over the chunked messages and switch states. When users receive all the necessary chunks to reconstruct a message, the functions here will perform basic checks, like for example checking the size of the message, and will leave any involved integrity check for their "unchunked" counterpart.
2. {spqr "src/v1/unchunked"}[] — unchunked: this is where the users will actually authenticate reconstructed messages (hence the name), and encapsulate/decapsulate them using the ML-KEM-768 protocol. This is also where the epoch will be incremented. Note that the actual implementation of ML-KEM-768 or HMAC-SHA256 happens in [libcrux](https://github.com/cryspen/libcrux).

In each of those folders, you will find two main components that users will call depending on their role. For example if UserA starts the protocol and sends off the first message with the shared secret, header and encapsulation key, then:

1. send\_ek — {spqr "src/v1/chunked/send_ek.rs"}[]: will include all UserA's parts of the protocol involving the sending of ek/header and the receiving of ct1/ct2.
2. send\_ct — {spqr "src/v1/unchunked/send_ct.rs"}[]: will include all of UserB's parts of the protocol involving the sending of ct1/ct2 and reception of ek/header.
3. states — {spqr "src/v1/chunked/states.rs"}[]: this is where the top level protocol decides what to call when sending and receiving the messages, i.e. this file will orchestrate which state we should be in when receiving a message over the wire. This file is only available in the chunked case.

Once the users move to the next epoch and switch roles, then they will call the other file associated with that role.

In general, the code is structured around state transitions that are shared by both the chunked and unchunked parts. For example, we show below how the "Ct1Sampled" state is defined across the various files:

```rust
// **** SparsePostQuantumRatchet/src/v1/chunked/send_ct.rs ****
pub struct Ct1Sampled {
    // The line below calls the state defined in the unchunked file,
    // i.e. the state once the message has been reconstructed
    uc: unchunked::Ct1Sent,
    sending_ct1: polynomial::PolyEncoder,
    receiving_ek: polynomial::PolyDecoder,
}
// Think of this enum as a way to describe the relation between the state
// UserA and UserB are currently in, i.e. what happens when UserA and UserB are // sending messages in parallel
pub enum Ct1SampledRecvChunk {
    StillReceivingStillSending(Ct1Sampled),
    StillReceiving(Ct1Acknowledged),
    StillSending(EkReceivedCt1Sampled),
    Done(Ct2Sampled),
}
// This is where the functions are defined over the state
impl Ct1Sampled {
    pub fn recv_ek_chunk(
        self,
        epoch: Epoch,
        chunk: &Chunk,
        ct1_ack: bool,
	// Notice how the result includes a state transition to "Ct1SampledRecvChunk"
    ) -> Result<Ct1SampledRecvChunk, Error>{...}
   pub fn send_ct1_chunk(self) -> (Ct1Sampled, Chunk) {...}
   pub fn epoch(&self) -> Epoch {...}
}
// **************************************************************
```

```rust
// **** SparsePostQuantumRatchet/src/v1/unchunked/send_ct.rs ****

// Think of the state defined in "unchunked" as a more granular version of
// the one in "chunked". It contains all the information that is reconstructed
// and validated during the protocol.
pub struct Ct1Sent {
    pub epoch: Epoch,
    auth: authenticator::Authenticator,
    hdr: incremental_mlkem768::Header,
    es: incremental_mlkem768::EncapsulationState,
    ct1: incremental_mlkem768::Ciphertext1,
}
// This is where the functions are defined over the state and where
// the user actually handles authentication
impl Ct1Sent {
    pub fn recv_ek(
        self,
        epoch: Epoch,
        ek: incremental_mlkem768::EncapsulationKey,
    ) -> Result<Ct1SentEkReceived, Error> {...}
}
// **************************************************************
```

```rust
// **** SparsePostQuantumRatchet/src/v1/chunked/states.rs ****

// The enum below includes ALL the state including the one in our e.g.
pub enum States {
    ...
    Ct1Sampled(send_ct::Ct1Sampled),
    ...
}
pub enum MessagePayload {
    ...
    // The message payload may include a bunch of acks and chunks including the ones related to "Ct1Sampled"
    Ct1Ack(bool),
    Ct1(Chunk),
    ...
}
// This is the top level message that has not been yet translated matched
// into "Ct1Sampled"
pub struct Message {
    pub epoch: Epoch,
    pub payload: MessagePayload,
}
// This is an abstraction of the top level message that has been received by the highest level of the protocol.
pub struct Send {
    pub msg: Message,
    pub key: Option<EpochSecret>,
    pub state: States,
}

impl States {
...
    // Here we just show the example of how the top level "send" gets translated to "send_ct1_chunk" that is defined over "Ct1Sampled". There are other functions implemented for "States" that we omit for simplicity.
    pub(crate) fn send<R: Rng + CryptoRng>(self, rng: &mut R) -> Result<Send, Error> {
        match self {
	...
	     // We only show here the case where self is matched with the state
	     // "Ct1Sampled". It can be matched with other states that we omit for simplicity.
            Self::Ct1Sampled(state) => {
                let epoch = state.epoch();
                let (state, chunk) = state.send_ct1_chunk();

                Ok(Send {
                    state: Self::Ct1Sampled(state),
                    msg: Message {
                        epoch,
                        payload: MessagePayload::Ct1(chunk),
                    },
                    key: None,
                })
            }
	...
}
}
...
}
// **************************************************************
```

You will also notice some serialization files across the SPQR folder that will actually translate these messages into bytes sent over the network. It may be simpler to find the flags associated with the different states at {spqr "src/v1/chunked/states/serialize.rs"}[].

If you are curious about how the basic blocks of this protocol are implemented, you may need to look under {spqr "src"}[]. For example, you will find the ML-KEM-768 protocol at {spqr "src/incremental_mlkem768.rs"}[] and any basic operation related to Reed-Solomon erasure codes at {spqr "src/encoding/polynomial.rs"}[].

Finally, if you are interested in testing the SPQR protocol for yourself and playing around with different scenarios that UserA and UserB might find themselves in, you can do so using Signal's existing tests at {spqr "src/test"}[]. In general, whether you are playing around with SPQR or libsignal itself, you will find multiple useful tools that will help you "mock" a signal account instead of using an actual phone number to create one.
:::
