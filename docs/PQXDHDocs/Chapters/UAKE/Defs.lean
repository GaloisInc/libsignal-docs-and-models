import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import ToVCVio.CryptoFoundations.AKE.UAKE.Party
import ToVCVio.CryptoFoundations.AKE.UAKE.Transcript

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true
set_option verso.blueprint.autoDeps true
set_option verso.blueprint.foldCodeBlocks true
set_option doc.verso true

#doc (Manual) "UAKE Model Definitions" =>

:::group "uake"
The unilaterally-authenticated key exchange (UAKE) model of {Informal.citet DF17}[], against which the PQXDH realizations are stated and proved.
:::

A UAKE scheme is a possibly interactive scheme between two parties: a keyed party $`T`, and an unkeyed party $`U`. At the end of the protocol both parties output a key, which is guaranteed to be indistinguishable from random, and $`T` is authenticated to $`U` (but not vice-versa).

The security game assumes a scheme is *well-formed*: that an honest run transfers exactly `rounds` messages, that both parties produce outputs only once the protocol is complete, and that party $`T` speaks last. The round-count and output constraints are captured by the well-formedness predicate below; the $`T`-speaks-last convention is not.

*Model simplifications*

- **Rejected protocol messages.** DF'17 does not say what happens when a protocol message is rejected, but it seems necessary to model this in real protocols. A rejected message is dropped from the transcript and the session continues. The alternatives would be to record the message and either halt the session, which prevents the adversary from retrying, or continue, which lets the adversary win by injecting a rejected dummy message that prevents transcript matching.
- **WLOG protocol assumptions.** DF'17 assumes explicitly that $`T` speaks last; the model does not enforce it. Since the ping-pong predicate depends on the parity of `rounds` to determine who should speak first, a protocol with a correct value of `rounds` where $`T` does *not* speak last is trivially insecure, assuming $`U` ever accepts in an honest run.
- **No 1-round protocols.** The model can represent only protocols of at least two rounds, since a party's init function has no variant indicating that it is done at that stage. DF'17 likewise does not consider UAKE protocols with fewer than two rounds.

# Parties

:::defTitle "uake_party_init" "Party initialization result"
:::

::::definition "uake_party_init" (parent := "uake") (lean := "AKE.UAKE.Party.InitResult")
Result of a party's init function. An honest run dispatches on this to decide which party opens the protocol: a party either speaks first, contributing an opening message, or waits for the first message.
::::

:::defTitle "uake_party_step" "Party step result"
:::

::::definition "uake_party_step" (parent := "uake") (lean := "AKE.UAKE.Party.StepResult")
Result of a party's step function. A step may accept the incoming message and send a reply, flagging with `done` whether the protocol is thereby complete; complete the session without a reply; or reject, in which case the message is dropped from the transcript and the session continues.
::::

:::defTitle "uake_party" "Party"
:::

::::definition "uake_party" (parent := "uake") (lean := "AKE.UAKE.Party")
A party, structured as a Mealy machine with a final output function. In DF'17 a party is an ITM; here it is instead modelled as a Mealy machine with a step function that outputs a protocol message and a new state. The output function takes the party's state and produces its final output — in UAKE, this is the key.

It is up to the protocol realization to ensure that the output function produces output only at the end.
::::

:::defTitle "uake_party_outputs" "Outputs only at completion"
:::

::::definition "uake_party_outputs" (parent := "uake") (lean := "AKE.UAKE.Party.OutputsOnlyAtCompletion")
True if a party is well-formed, i.e. if it outputs iff the state is the result of an execution of the step function that returns `done = true` or `complete`, assuming the state is reachable.
::::

:::defTitle "uake_run_honest" "Honest protocol run"
:::

::::definition "uake_run_honest" (parent := "uake") (lean := "AKE.UAKE.Party.runHonest")
Execute an honest run of the protocol. The result is a triple of $`P`'s output, $`Q`'s output, and the message list, with the `fuel` argument giving the number of rounds in the protocol.

The run begins by dispatching on the two parties' initialization results to determine which party opens, then runs the two parties against each other. The messages sent are returned in chronological order alongside both parties' states; within the loop, `fuel` counts the rounds remaining and a Boolean tracks whose turn it is.
::::

# Schemes and correctness

:::defTitle "uake_scheme" "UAKE scheme"
:::

::::definition "uake_scheme" (parent := "uake") (lean := "AKE.UAKE.Scheme")
A UAKE scheme with a fixed number of rounds. The keyed (authenticated) party is $`T`; the unkeyed (unauthenticated) party is $`U`.

- `rounds`: the total number of protocol messages sent — not round trips — in an honest execution, assumed fixed for a given protocol. This is not enforced structurally but is captured by the well-formedness predicate. Together with the $`T`-speaks-last convention of DF'17 it determines the first speaker in the ping-pong predicates used in the security game.
- `setup`: create the initial key material used by $`U` and $`T`. In the security game this is called just once by the challenger — as opposed to $`T`'s init function, which is called each time the adversary spins up a new party instance — so the parameters it creates are long term and global.
- `U`: the unkeyed (unauthenticated) party.
- `T`: the keyed (authenticated) party.
::::

:::defTitle "uake_scheme_wellformed" "Well-formed scheme"
:::

::::definition "uake_scheme_wellformed" (parent := "uake") (lean := "AKE.UAKE.Scheme.WellFormed")
True if both parties output iff the protocol run is complete, and an honest run of the protocol transfers exactly `rounds` messages.

This does *not* enforce the WLOG $`T`-speaks-last convention from DF'17.
::::

:::defTitle "uake_correct_exp" "Correctness experiment"
:::

::::definition "uake_correct_exp" (parent := "uake") (lean := "AKE.UAKE.CorrectExp")
The UAKE correctness experiment, Def. 7 of DF'17. The parties' keys are sampled using the setup routine, then both parties are run honestly to completion. The protocol is correct if both honest parties output the same key, or either party outputs ⊥.
::::

:::defTitle "uake_perfectly_correct" "Perfect correctness"
:::

::::definition "uake_perfectly_correct" (parent := "uake") (lean := "AKE.UAKE.PerfectlyCorrect")
True if the correctness experiment always returns true.
::::

# Transcripts

:::defTitle "uake_transcript" "Session transcript"
:::

::::definition "uake_transcript" (parent := "uake") (lean := "AKE.UAKE.Transcript")
A transcript is a list of messages and timestamps. Transcripts in DF'17 bundle messages with timestamps from a global clock, incremented whenever a party sends a message.
::::

:::defTitle "uake_matching" "Matching sessions"
:::

::::definition "uake_matching" (parent := "uake") (lean := "AKE.UAKE.Matching")
Def. 3 from DF'17. A pair of transcripts match ($`T \subseteq T^*`) if their messages are elementwise identical and their timestamps are interleaved as

$$`t_1 < t_1^* < t_2^* < t_2 < \cdots \qquad \text{or} \qquad t_1^* < t_1 < t_2 < t_2^* < \cdots`

depending on which party speaks first.
::::

# The security experiment

:::defTitle "uake_tsession" "T-session state"
:::

::::definition "uake_tsession" (parent := "uake") (lean := "AKE.UAKE.TSession")
The state of a single copy of the $`T` oracle state in the UAKE security experiment.

- `state`: $`T`'s state.
- `transcript`: the transcript for this session.
- `key`: the final key output by $`T` for this session. `none` means the session has not yet completed, assuming a well-formed party that outputs only at completion; `some none` means the session completed with $`T` outputting ⊥; and `some (some k)` means it completed with $`T` outputting `k`.
- `revealed`: whether the key for this session has been revealed to the adversary through a reveal query.
::::

:::defTitle "uake_env" "Experiment environment"
:::

::::definition "uake_env" (parent := "uake") (lean := "AKE.UAKE.Env")
Challenge environment for the UAKE security experiment.

- `clock`: the global clock, incremented once for each message sent by a party.
- `challenge`: the challenge session.
- `challengeDone`: whether the challenge session has completed.
- `tSessions`: list of sessions the adversary has opened with copies of $`T`.
::::

:::defTitle "uake_op" "Adversary oracle operations"
:::

::::definition "uake_op" (parent := "uake") (lean := "AKE.UAKE.Op")
Adversary's oracle operations for the UAKE security experiment.

- `openT`: start a new session. Returns the new session id and the initial protocol message, or ⊥ if $`T` is not the first speaker.
- `stepT`: increment an existing session with a given message. Returns the next protocol message.
- `revealT`: reveal the key for this session. This is a no-op until the session is complete.
- `stepChallenge`: increment the challenge session, which is created up front.
::::

:::defTitle "uake_op_impl" "T-session and challenge oracles"
:::

::::definition "uake_op_impl" (parent := "uake") (lean := "AKE.UAKE.opImpl")
Logic for the UAKE experiment's oracle queries: the $`T`-session and challenge-session oracles.
::::

:::defTitle "uake_oracle_impl" "Oracle implementation"
:::

::::definition "uake_oracle_impl" (parent := "uake") (lean := "AKE.UAKE.oracleImpl")
Full oracle for the UAKE experiment. Uniform-sampling queries — the adversary's coin flips — are forwarded to the ambient monad; the remaining queries are handled by the $`T`-session and challenge-session oracles.
::::

:::defTitle "uake_adversary" "UAKE adversary"
:::

::::definition "uake_adversary" (parent := "uake") (lean := "AKE.UAKE.Adversary")
An adversary in the UAKE security game. It runs in two stages: a challenge stage, with oracle access to copies of $`T` and to the challenge session, and a post stage, which receives the challenge key and outputs a guess.
::::

:::defTitle "uake_ping_pong" "Ping-pong relaying"
:::

::::definition "uake_ping_pong" (parent := "uake") (lean := "AKE.UAKE.fullPingPong")
True if the challenge transcript is ping-pong and a session whose transcript matches has been revealed to the adversary through a reveal query.

A challenge transcript is ping-pong when an oracle session matches it, meaning that the adversary is trivial: it simply relayed the oracle session in the challenge.
::::

:::defTitle "uake_finalize" "Experiment finalization"
:::

::::definition "uake_finalize" (parent := "uake") (lean := "AKE.UAKE.finalize")
Final stage in the security experiment.

1. Pick between $`K_b = K_1` if $`b` is true, or $`K_b = K_0` otherwise.
2. Finalize the challenge oracle, so the adversary cannot continue the challenge session, by setting `challengeDone`.
3. Give the adversary $`K_b`, along with continued oracle access to copies of $`T`, and let it make a guess $`b'`.
4. Declare the adversary a winner if $`b' = b` and the challenge session is not full ping-pong, in which case it wins with probability $`1/2`.
::::

:::defTitle "uake_exp" "Security experiment"
:::

::::definition "uake_exp" (parent := "uake") (lean := "AKE.UAKE.Exp")
The security experiment from Sec. 3 of DF'17.

1. Run setup.
2. Choose a uniform challenge bit $`b`.
3. Run the adversary with oracle access to copies of $`T` and the challenge session.
4. Declare the adversary a winner if it did *not* relay the challenge session and the challenge key is not ⊥.
5. Run finalization, either with $`K_0 = K_1 = ⊥` if the challenge key was ⊥, or on the challenge key $`K_0` and a uniformly chosen $`K_1`.
::::

:::defTitle "uake_advantage" "UAKE advantage"
:::

::::definition "uake_advantage" (parent := "uake") (lean := "AKE.UAKE.advantage")
$`\todo`
::::
