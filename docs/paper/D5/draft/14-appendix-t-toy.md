# Appendix T. The verify toy: binary

*Draft 5, 2026-11-25. A complete example of the observable API of II.4.1, on binary words, small enough to read in full and to rerun.
Lean: IM, `arsenal/Arsenal/Toy.lean`. Claim labels (T.n) are listed in `../CLAIMS.md`.*

The headline of the paper (II.4.1) says that each problem is restated as one statement checked at every step, exactly equivalent
to it, and that a proof is an induction, base case and inductive step, which then holds at every step and, along a map of scales that
keeps the step and the check, at every scale. This appendix runs every part of that statement on the simplest data there is, binary
words, where nothing is open and nothing carries an error bar.
Each part is one Lean declaration in IM's arsenal; a reader can rebuild a larger proof by taking these parts and reassembling them as
the API guides.

## T.1 A box that passes

The states are the k-bit words, the step adds two modulo 2^k, and the claim at each word is "even" (`evens k`). Its one-box
description has the claim as its marker and the truth of the claim as its gate. The induction is shown: the base case, the word 0 is
even, and the inductive step, a step of two keeps a word even (`evens_step`), so the description is DMP-complete, the claim holding at
every step (`evens_route`) **[Lean]**
(claim T.1). On a byte the step is also checked the most direct way: all 256 words, one kernel evaluation (`evens_step_byte`, by
`decide`) **[Lean]** (claim T.2).

## T.2 The sharing across scales, proved

The scales are the bit widths. Reduction modulo 2 maps every k-bit word to one bit, and it keeps the step (adding two leaves the last
bit as it was) and the gate (a word is even exactly when its last bit is 0): every width is rebuilt from one bit through its gate,
start to start, carrying the marker (`toBit`, `evens_shared`) **[Lean]**. So here the sharing that the paper's one assumption asks for
on the cards (Part X) is a theorem, and the route shown at one bit certifies every bit width (`evens_everywhere`, from
`route_everywhere`) **[Lean]** (claim T.3). What the sharing costs is visible here: on one bit a step of two changes nothing, so the induction there is free, and the parity
argument for k bits sits in the map itself (`toBit`, its step condition). The content of "every scale" is the map, as II.4.1 says.

## T.3 A box that says R136a1

Change one thing: the step adds one, a binary counter (`counter k`), with the same claim. At tick 1 the word is 1, which is odd: the
gate reads R136a1, outside, while the marker claims inside (`counter_gate`), so the description is not DMP-complete
(`counter_refuted`) **[Lean]** (claim T.4). On a byte the first word is checked odd by one kernel evaluation (`counter_byte`). One
wrong tick refutes the claim, as II.4.1 says.

## T.4 Reassembly

Two systems run side by side form a system whose claim is that both claims hold (`Observable.prod`), and inductions for the two give an
induction for the pair (`route_prod`). The toy reassembles a byte and a 16-bit word, each stepping by two, into one certified pair
(`pair_route`) **[Lean]** (claim T.5). The first author reads this as the whole method in small: rebuilding is taking the parts that
are shown and reassembling them as the API guides **[reading]** (claim T.6).

## T.5 The string vxunderground

The example string is `vxunderground`, the name of the collective whose work gave the first author the idea. Converted to binary, its
13 bytes are the characters of the string (`vx_eq`), and each byte is listed as its 8 bits (`vx_binary`). Read step by step, with the
positions as states, the next position as the step and "the byte here, if any, is a lowercase letter" as the claim, the description is
DMP-complete at every step: the 13 bytes are checked, and past the end there is no byte to check (`vxRead_complete`) **[Lean]**
(claim T.7). Hidden by a half-turn of the 26 letters, a rotation by
13, the string reads `ikhaqretebhaq` (`vx_rot13`); the second half-turn completes the full turn and returns it
(`vx_rot13_twice`), and so does a known rotation completed to a full turn, for example 5 + 21 = 26 (`vx_rot_complete`) **[Lean]** (claim T.8).
This is R.8b's "a turn undoes a known cyclic rotation" on concrete data; the rotation by 13 has the shape of II.2.4's half-turn, an
involution. Every fact
about the string is one kernel evaluation.

## T.6 A digest of all zeros and a one

In the terms of II.4.1 each candidate input is one step whose statement, "this input's digest is the target", is checked by one hash.
A digest is a certificate of its path: given the input, one forward run rebuilds the path to the digest, for anyone, every time.

**Forward, the path cost is 1** **[numerical]** (`docs/unified/sha256_scaled.py`, its log `sha256_scaled.log`, rerun by
`tools/reproduce.sh certs`; claim T.9). The test vectors published with the Secure Hash Standard reproduce (for "abc" the digest
`ba7816bf...f20015ad`), so the encoding used here agrees with the standard. The sha256 of the 32-byte value 0...01 is immediate,
`ec4916dd...aac8bc5`. Flipping any one of the 104 input bits of `vxunderground` changes between 105 and 148 of the 256 digest bits,
128.7 on average: half, the avalanche a hash is designed for **[classical]** for the design criterion (Webster-Tavares 1985).

**Backward, without the input, there is no short path** **[numerical]** (claim T.9). Inputs built by rotating a 1 into place (one byte
0x01, the character "1", 32 bytes 0...01, 256 characters 0...01) are hashed once each; none gives 000...0001, so each is refuted at
its one step. A digest of a chosen shape is a search: the first input `vxunderground-n` whose digest starts with k zero hex digits and
ends in 1 is found after 246, 609, 13113, 26014 and 2123543 tries for k = 1 to 5, single draws against an expected count of about
16^(k + 1) (256, 4096, 65536, 1048576 and 16777216), growing sixteenfold with each fixed digit. The full shape 000...0001 fixes all 64
hex digits, about 2^256 = 1.2 x 10^77 tries: at about 10^21 hashes a second, the rate of the whole Bitcoin network, some 10^56
seconds, and with Grover's search on a quantum computer still about 2^128 steps **[classical]** for the arithmetic and Grover 1996.
Whether 000...0001 is the digest of any input at all is not known: the pigeonhole theorem (`hash_collision`) gives some digest many
inputs, not every digest one. In the terms of II.4.1, 2^256 is the cost of having no induction: every step must be checked.

**The first author's readings** **[reading]** (claim T.10). The path is the certificate, so a digest is verification incarnate. A
digest of length 256 can be built from the end, a 1 rotated into the last of 256 places, the one case without error bars, and the
rotation is exact there: turned once over the 256 places, a single 1 spreads into 256 phases of equal size **[classical]** (the
discrete Fourier transform of a single point). Hashing flips the content between 1 and 0, half and half, preserving only the
correlation of input and digest, as the avalanche above measures. Under O1 he reads a reconstruction at path cost 1 as sharing a DB
with what was provided, hence correlated, hence valid as an encoding and as a certificate across that DB **[reading] (under O1)**.
Care points: the rotation builds the value 000...0001, not an input whose digest it is; a reversible computation runs backwards only
with the history it kept (II.4.1); the correlation is established by supplying the input, not by the digest; no step from O1 to an
input of a given digest is claimed, and the measured evidence above stands either way.

## T.7 Rerunning it

In a clone of the public IM repository, at the commit `docs/mass-gap/formal/lakefile.toml` pins: `cd arsenal`, then
`lake exe cache get` (Mathlib's prebuilt files, about 5 GB) and `lake build Arsenal.Toy`; `tools/check.sh` reports, for every
declaration of the arsenal, the axioms it rests on, and every one of the toy's rests on Lean's three standard axioms only.
