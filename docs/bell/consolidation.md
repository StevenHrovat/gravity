# Consolidation pass, 2026-10-29

The owner, 10:18Z: "Let's completely redo the spinning section and just also rederive it from our theory. Also, please do a
consolidation pass." This file records the pass: what was read for, what was found, what was changed in `bell.tex`.

## The spinning section, redone

Section 9.1 replaces the earlier Kerr paragraph (a reading of a known result) with a rederivation in seven steps, each marked D (DMP's
text), R (the owner's reading) or P (established physics):

1. Split the mass into the part no outside act reaches (contained, m) and the actable rest (D, containment).
2. The contained part never shrinks under outside acts: only entropy leaves (D, T31).
3. The spin is one more count, read from outside, so it sits with the actable part at the boundary (D, Axiom 3; R, "one more information").
4. Only the contained part sets the boundary: Schwarzschild area 16 pi m^2 (R, gravity as existence asserting itself; P, the area).
5. The spin carried at R = 2m as momentum J/2m, combined as M^2 = m^2 + p^2 (P, special relativity; the identification is heuristic).
6. Solve: Kerr's area for every spin, the bound a <= 1, 29% extractable at a = 1.
7. delta m >= 0 is Hawking's area theorem.

Honest status, written into the paper ("What this is") and into "Where we expect it to break": exact agreement with general relativity,
not a derivation from DMP alone (two physical inputs, one identification), and not a new number (Kerr 1963, Christodoulou and Ruffini 1971,
Hawking 1971). Check B8 was rewritten to test the rederivation itself: 7 assertions, 29 of 29 in total.

## Findings and fixes

| # | Finding | Fix |
|---|---|---|
| 1 | Abstract did not mention the outlook and repeated detail the body carries | Rewritten: Kerr sentence added, Part 1 and the readings shortened; 1757 characters |
| 2 | "26 of 26" after B8 grew | "29 of 29" in "What we claim" and README |
| 3 | Intro roadmap omitted Section 3.5 and the outlook | Both named |
| 4 | Result paragraph silent on the outlook | One sentence: no new number, Kerr exactly, with its inputs |
| 5 | Lean names used with and without module prefix | Full names once in Section 2 with the file, short names after; `rf_past_is_a_chain` introduced there |
| 6 | Weinberg 1967 cited for colour, which is not in it | Citation limited to the electroweak part |
| 7 | "the refresh rate of the earlier physics pass" had no source | Cited as gravity#19 (unmerged), whose `docs/physics.md` reads the refresh rate as the lapse; sentence now says the assertion rate is the lapse |
| 8 | W/Z verdict came after the three-nodes discussion, so it read as the verdict on three nodes | W/Z verdict moved up; three nodes got its own paragraph and verdict |
| 9 | Contributions section pointed only to Sections 6 to 8 | Now 3.5, 6 to 8 and 9 |
| 10 | Ledger had no row for the outlook | Row "Kerr horizon, spin bound, area theorem: model with two inputs, host yes, Section 9.1, B8" |
| 11 | "Where we expect it to break" sat before the outlook | Moved after it, with items on the step-5 identification and on T31 against Page |
| 12 | Conclusion's Kerr sentence predated the rederivation | Rewritten to the balanced statement |

Checked and left as is: every verbatim quote of the owner against the thread (spelling kept, including "nobel price"); every number against
the source log in README; section references (built twice, no undefined references, no overfull boxes).
