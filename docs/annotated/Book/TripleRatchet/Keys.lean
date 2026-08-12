import VersoManual
import Book.Annotation
import Book.Papers
import Book.CodeRef

open Verso.Genre Manual

#doc (Manual) "Note on Keys and Storage" =>

:::galois

The Signal docs and code make a distinction between an SPQR epoch secret, an SPQR chain key and an SPQR message key. 
An SPQR epoch secret is a shared secret among Alice and Bob that they compute using KEM throughout the protocol. 
Bob is first able to compute it using the header sent by Alice, and Alice is able to compute once she receives ct1 and ct2. 
The SPQR chain key is derived from that secret and the previous SPQR chain key using an HKDF {spqrf258 "src/chain.rs#L357-L362"}[]. The SPQR message key is a 
salted chain key {spqrf258 "src/lib.rs#L298"}[], {spqrf258 "src/chain.rs#L406"}[]{spqrf258 "src/chain.rs#L229-L246"}[]. This in essence is not too different from 
what is done in the Double Ratchetting protocol where a ratcheting stage outputs both a chain key and an output message key from the prior rounds key. 

We highlight this distinction because libsignal has different lifetimes for these different keys. 
On the SPQR side, as we’ve seen, libsignal stores both the current and next epoch chain keys(if the later has been constructed). 
Additionally, libsignal will store at most one extra epoch chain prior to the current one {spqrf258 "src/chain.rs#L391-L395"}[], {spqrf258 "src/chain.rs#L125"}[]. 
The number of SQPR message keys stored can reach 25,000 
such keys {spqrf258 "src/chain.rs#L34-L37"}[]. And here we make the distinction between two out of order message scenarios:
* When i messages have not been received but the i+1th message arrives. Whether we can or can’t read that message depends 
on this max\_jump parameter which tells us that i+1 <= 25,000 in order for the message key to still be available.
* When  message i has been received and message i - k arrives.  Whether we can or can’t read that message depends on this 
max\_ooo\_keys parameter which tells us that k <= 2,000 in order for the message key to still be available.

The number of DR message keys is similarly 25,000 keys {libsignal57d "rust/protocol/src/consts.rs#L8-L9"}[]. However, the number of 
DR chain keys stored at any given time is 5 {libsignal57d "rust/protocol/src/consts.rs#L10"}[].

:::