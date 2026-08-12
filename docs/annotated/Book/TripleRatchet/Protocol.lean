import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.Papers

open Verso.Genre Manual

#doc (Manual) "Triple Ratchet" =>

:::galois
Following that initial handshake, the Signal protocol then runs the Double Ratchet and the SPQR protocol in parallel. 
For every new message a new ratcheting key is generated. However, while the Double Ratcheting protocol is continuously 
producing new keys with each received message, the SPQR protocol only does so after an epoche of time (hence the term sparse in SPQR). 
Meaning that until SPQR constructs a new epoch secret, the Triple Ratchet mixes the new Double Ratchet key with
whatever the pre-existing SPQR key is. 

This transition from old SPQR key to new SPQR key is reflected in the state transitions described in sections 2.1 and 2.5 of the
ML-KEM Braid specification {citep Book.Papers.signalMLKEMBraid}[]. Assuming that Alice is initiating a conversation with Bob, then:
:::

# {galois}[Alice's side]

:::galois
On Alice's side
{libsignal57d "rust/protocol/src/triple_ratchet.rs#L86-L135"}[], the code
itself:

* Alice uses the key associated with the current epoch (i.e. not the one being negotiated, but rather the one already agreed upon) {spqrf258 "/src/lib.rs#L298"}[]
* If Alice has finished constructing the next epoch’s shared secret, they can add it to the chain of epoch secrets so that it may be 
used with the next round of messages {spqrf258 "src/lib.rs#L295-L297"}[]. Notice that under the hood, the SPQR shared secret is transformed into an SPQR message key 
before being added to the chain {spqrf258 "src/chain.rs#L357-L362"}[].
* Alice only emits and uses a fresh constructed epoch secret and key when they switch states from EkSentCt1Received state to the NoHeaderReceived state, 
reflected here {spqrf258 "src/v1/unchunked/send_ek.rs#L150"}[] in the code. 
* Alice finally mixes the SPQR and Double ratcheting keys using an HKDF based on SHA256 {libsignal57d "rust/protocol/src/triple_ratchet.rs#L104"}[]
{libsignal57d "rust/protocol/src/ratchet/keys.rs#L32-L44"}[], {libsignal57d "rust/protocol/src/ratchet/keys.rs#L100-L118"}[]
and updates the SPQR state {libsignal57d "rust/protocol/src/triple_ratchet.rs#L132"}[], {spqrf258 "src/lib.rs#L307-L313"}[], {spqrf258 "src/v1/chunked/states.rs#L115-L273"}[].
:::

# {galois}[Bob's side]

:::galois
Similarly, on Bob's side:
{libsignal57d "rust/protocol/src/triple_ratchet.rs#L215-L297"}[]
* Bob retrieves all the Double Ratchet key material
  {libsignal57d "rust/protocol/src/triple_ratchet.rs#L224-L236"}[].
* Bob then identifies the key {libsignal57d "rust/protocol/src/triple_ratchet.rs#L239-L251"}[] that should be used by inspecting the SPQR state and 
  Bob either updates the SPQR key {spqrf258 "src/lib.rs#L427-L429"}[] or uses the pre-existing SPQR key {spqrf258 "src/lib.rs#L432-L434"}[]
  (note here how the index of the chain key here is not decremented) depending on the epoch 
  that the parties have finished negotiating.
* Bob only constructs the new epoch shared secret when they reach the HeaderReceived state {spqrf258 "src/v1/unchunked/send_ct.rs#L135-L147"}[] and switch to the 
  Ct1Sampled state. Note that this secret is turned into a key when its added to the SPQR chain {spqrf258 "src/lib.rs#L427-L429"}[].
* Bob finally mixes the two ratcheting keys using an HKDF based on SHA256 {libsignal57d "rust/protocol/src/triple_ratchet.rs#L254"}[] and updates the SPQR state {spqrf258 "src/lib.rs#L437-L443"}[].
:::

