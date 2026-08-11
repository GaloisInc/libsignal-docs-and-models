import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.Papers

open Verso.Genre Manual

#doc (Manual) "Triple Ratchet" =>

:::galois
Following that initial handshake, the Signal protocol then runs the Double
Ratchet and SPQR protocols in parallel. For every new message a new ratcheting
key is generated. However, while the Double Ratchet continuously produces new
fresh keys for each message, SPQR does so after an epoche of time, hence the term "sparse" in SPQR.
The relevant SPQR state transitions are described in section 2.5 of the
ML-KEM Braid specification
{citep Book.Papers.signalMLKEMBraid}[]. Until SPQR constructs
a new epoch secret, the Triple Ratchet mixes the new Double Ratchet key with
whatever the pre-existing SPQR key is.
:::

# {galois}[Alice's side]

:::galois
On Alice's side
{libsignal57d "rust/protocol/src/triple_ratchet.rs#L93-L132"}[], the code
itself:

* Identifies whether the current SPQR state emits a fresh epoch secret
  {spqrf258 "src/lib.rs#L263-L299"}[]
  {spqrf258 "src/v1/chunked/states.rs#L115-L273"}[]. Only the
  `HeaderReceived` send transition emits one
  {spqrf258 "src/v1/chunked/states.rs#L203-L219"}[].
* Based on the current state, it may add a fresh SPQR epoch secret for use with
  the next round of messages {spqrf258 "src/lib.rs#L294-L297"}[].
* Uses what the source calls the "pre-existing SPQR key" in each round
  {spqrf258 "src/lib.rs#L298"}[].
* Note: Since Alice is the initiator of the conversation, they need to indicate to Bob
  that they have moved on to next epoch before both parties start using the negotiated
  SPQR shared secret. At a code level, this is reflected on line {spqrf258 "src/lib.rs#L298"}[]
  where Alice saves the new epoch secret for the next round of messages. At a state transition level, 
  this is marked by Alice switching from the EkSentCt1Received state to the NoHeaderReceived state 
  (where Alice effectively switches roles with Bob), and Bob switching from Ct2Sampled to KeysUnsampled.
* Then mixes the two ratcheting keys using HKDF based on SHA-256
  {libsignal57d "rust/protocol/src/triple_ratchet.rs#L104"}[]
  {libsignal57d "rust/protocol/src/ratchet/keys.rs#L28-L44"}[]
  {libsignal57d "rust/protocol/src/ratchet/keys.rs#L99-L118"}[] and finally
  updates the SPQR state
  {libsignal57d "rust/protocol/src/triple_ratchet.rs#L131-L132"}[]
  {spqrf258 "src/lib.rs#L303-L313"}[].
:::

# {galois}[Bob's side]

:::galois
Similarly, on Bob's side:

* Bob retrieves all the Double Ratchet key material
  {libsignal57d "rust/protocol/src/triple_ratchet.rs#L224-L236"}[].
* For SPQR
  {libsignal57d "rust/protocol/src/triple_ratchet.rs#L238-L251"}[], the code
  identifies whether the current state emits a fresh epoch secret
  {spqrf258 "src/lib.rs#L421-L429"}[]
  {spqrf258 "src/v1/chunked/states.rs#L275-L533"}[]. Completing the
  `EkSentCt1Received` receive transition emits one
  {spqrf258 "src/v1/chunked/states.rs#L350-L369"}[].
* It either adds the fresh SPQR epoch secret
  {spqrf258 "src/lib.rs#L427-L429"}[] or uses what the source calls the
  "pre-existing SPQR key" if both parties have not finished negotiating the fresh SPQR secret.
* It then mixes the two ratcheting keys using HKDF based on SHA-256
  {libsignal57d "rust/protocol/src/triple_ratchet.rs#L253-L254"}[] and finally
  updates the SPQR state {spqrf258 "src/lib.rs#L436-L443"}[].
:::
