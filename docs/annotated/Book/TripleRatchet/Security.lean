import VersoManual
import Book.Annotation
import Book.Papers

open Verso.Genre Manual

#doc (Manual) "Note on Security" =>

:::galois
The sparsity of the PQ part of the Triple Ratchet has significant implications
for the security of the protocol. While the Double Ratchet allows users to
recover from a classical adversary as soon as they can receive fresh key
material, in the best case almost instantly, in the case of a quantum
adversary the users have to wait until they can construct a new SPQR secret.
That is why both the Signal docs (see section 3.1 of the ML-KEM Braid
specification {citep Book.Papers.signalMLKEMBraid}[]) and the papers
{citep Book.Papers.compareSecureMessaging}[] mention a _vulnerable message
set_: the number of messages that are compromised while a user waits to
recover from an attack. In the best case the vulnerable message set is as large as an epoche, i.e.
the number of messages that Alice and Bob need to exchange before they can reconstruct the message
header, ct1 and ct2 in order to derive the "fresh" SPQR shared secret. 
In other words the lower bound on the size of the vulnerable set is as large as the number 
of messages that need to be exchanged before a party can reconstruct a fresh SPQR key and 
heal from an attack. The vulnerable message set is hence dependent on the choice of KEM algorithm and
the bandwidth limitations of an application like Signal that in turn determines the chunk size and 
number of chunks needed to reconstruct a message (i.e. the header, ct1 and ct2). See sections 3.4, 3.5
and 3.6 of the MLKEM Braid specification {citep Book.Papers.signalMLKEMBraid}[].
:::