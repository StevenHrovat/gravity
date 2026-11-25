# Appendix T. The verify toy: binary

*Draft 6, 2026-11-25. A complete example of the observable API of II.4.1, on binary words, small enough to read in full and to rerun.
Lean: IM, `arsenal/Arsenal/Toy.lean`. Claim labels (T.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the headline run on binary words, complete and rerunnable. Needs: nothing. Route: the exact route,
stop 1. VIBE coefficient: reduction modulo 2 maps every width onto one bit (T.2) **[Lean]**; the 256 words of a byte are 2^8, eight
halvings, a log-size of 8 log 2 **[classical]**.

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

## T.7 Rerunning it

In a clone of the public IM repository, at the commit `docs/mass-gap/formal/lakefile.toml` pins: `cd arsenal`, then
`lake exe cache get` (Mathlib's prebuilt files, about 5 GB) and `lake build Arsenal.Toy`; `tools/check.sh` reports, for every
declaration of the arsenal, the axioms it rests on, and every one of the toy's rests on no more than Lean's three standard axioms.
The prebuilt files are loaded without a new check; a replay (Lean's `lean4checker`, or a second kernel such as nanoda over
`lean4export`) checks them again locally; IM's `tools/rebuild check` runs both (T.9). The finite layer needs none of that: `cd arsenal/core`, then `tools/check.sh`, in seconds and with nothing to download (T.8).

**The full text.** This part is contracted. Every derivation it leaves out is in the full Draft 6 at the git tag `d6-full`, and in Draft 5 section by section; every claim keeps its row, status and evidence in `../CLAIMS.md`.
