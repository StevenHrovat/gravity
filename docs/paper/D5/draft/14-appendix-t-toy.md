# Appendix T. The verify toy: binary

*Draft 5, 2026-11-25. A complete example of the observable API of II.4.1, on binary words, small enough to read in full and to rerun.
Lean: IM, `arsenal/Arsenal/Toy.lean`. Claim labels (T.n) are listed in `../CLAIMS.md`.*

The headline of the paper (II.4.1) says that every observable system has a one-box description, DMP-complete exactly when its claim
holds at every tick, with a route to the proof that, once shown, is certified at every tick and, with the gate shared across scales,
at every scale. This appendix runs every part of that statement on the simplest data there is, binary words, where nothing is open.
Each part is one Lean declaration in IM's arsenal; a reader can rebuild a larger proof by taking these parts and reassembling them as
the API guides.

## T.1 A box that passes

The states are the k-bit words, the step adds two modulo 2^k, and the claim at each word is "even" (`evens k`). Its one-box
description has the claim as its marker and the truth of the claim as its gate. The route is shown: the word 0 is even, and a step of
two keeps a word even (`evens_step`), so the description is DMP-complete, the claim holding at every tick (`evens_route`) **[Lean]**
(claim T.1). On a byte the step is also checked the most direct way: all 256 words, one kernel evaluation (`evens_step_byte`, by
`decide`) **[Lean]** (claim T.2).

## T.2 The sharing across scales, proved

The scales are the bit widths. Reduction modulo 2 maps every k-bit word to one bit, and it keeps the step (adding two leaves the last
bit as it was) and the gate (a word is even exactly when its last bit is 0): every width is rebuilt from one bit through its gate,
start to start, carrying the marker (`toBit`, `evens_shared`) **[Lean]**. So here the sharing that the paper's one assumption asks for
on the cards (Part X) is a theorem, and the route shown at one bit certifies every bit width (`evens_everywhere`, from
`route_everywhere`) **[Lean]** (claim T.3). On the cards the same sharing is the open assumption; the toy shows what it gives where
it holds.

## T.3 A box that says R136a1

Change one thing: the step adds one, a binary counter (`counter k`), with the same claim. At tick 1 the word is 1, which is odd: the
gate reads R136a1, outside, while the marker claims inside (`counter_gate`), so the description is not DMP-complete
(`counter_refuted`) **[Lean]** (claim T.4). On a byte the first word is checked odd by one kernel evaluation (`counter_byte`). One
wrong tick refutes the claim, as II.4.1 says.

## T.4 Reassembly

Two systems run side by side form a system whose claim is that both claims hold (`Observable.prod`), and routes for the two give a
route for the pair (`route_prod`). The toy reassembles a byte and a 16-bit word, each stepping by two, into one certified pair
(`pair_route`) **[Lean]** (claim T.5). The first author reads this as the whole method in small: rebuilding is taking the parts that
are shown and reassembling them as the API guides **[reading]** (claim T.6).

## T.5 The string vxunderground

The example string is `vxunderground`, the name of the collective whose work gave the first author the idea. Converted to binary, its
13 bytes are the characters of the string (`vx_eq`), and each byte is listed as its 8 bits (`vx_binary`). Read tick by tick, with the
positions as states, the next position as the step and "the byte here is a lowercase letter" as the claim, the description is
DMP-complete over the whole string (`vxRead_complete`) **[Lean]** (claim T.7). Hidden by a half-turn of the 26 letters, a rotation by
13, the string reads `ikhaqretebhaq` (`vx_rot13`); the second half-turn completes the full turn and returns it
(`vx_rot13_twice`), and so does any known rotation completed to a full turn, 5 + 21 = 26 (`vx_rot_complete`) **[Lean]** (claim T.8).
This is R.8b's "a turn undoes a known cyclic rotation" on concrete data; the rotation by 13 has the shape of II.2.4's half-turn, an
involution. Every fact
about the string is one kernel evaluation.

## T.6 A digest of all zeros and a one

Hashing is immediate in one direction: the sha256 of the 32-byte value 0...01, all zeros and a one at the end, is
`ec4916dd...aac8bc5`. The other direction, an input whose digest has a fixed shape, is a preimage search, and its cost can be shown in
small. For k = 1 to 5, the first input `vxunderground-n` whose digest starts with k zero hex digits and ends in the hex digit 1 is
found after 246, 609, 13113, 26014 and 2123543 tries; the k = 5 digest is `000002385f5f...2edd1e1` **[numerical]**
(`docs/unified/sha256_scaled.py`, its log `sha256_scaled.log`, rerun by `tools/reproduce.sh certs`; claim T.9). Each count is one
draw; the expected count is about 16^(k + 1), growing sixteenfold with each fixed hex digit. The full shape 000...0001 fixes all 64
hex digits, about 2^256 = 1.2 x 10^77 tries: at about 10^21 hashes a second, the rate of the whole Bitcoin network, some 10^56
seconds, and with Grover's search on a quantum computer still about 2^128 steps **[classical]** for the arithmetic and Grover 1996.
Whether 000...0001 is the digest of any input at all is not known: the pigeonhole theorem (`hash_collision`) gives some digest many
inputs, not every digest one. A digest is traced to an origin, not undone (R.6a).

## T.7 Rerunning it

In a clone of the public IM repository, at the commit `docs/mass-gap/formal/lakefile.toml` pins: `cd arsenal`, then
`lake exe cache get` (Mathlib's prebuilt files, about 5 GB) and `lake build Arsenal.Toy`; `tools/check.sh` reports, for every
declaration of the arsenal, the axioms it rests on, and every one of the toy's rests on Lean's three standard axioms only.
