# Findings: what the logic produces that DMP did not say

The owner, 2026-10-26 16:20Z: "We just need to see what all our logic actually produces and what we want to do with the perhaps
interesting weird behaviors and how to use that to improve the axiom system to be more representative, generalistic and still provably
safe and contained." This file is that list. One entry per behaviour the proofs forced into the open: what the theorem says, where DMP's
text is silent or says something else, and the candidate change. An entry is closed when DMP's text changed (with the owner's words) or
the owner decided the text stands. Nothing here changes DMP; it is the queue for the owner.

| # | Found in | What the logic produces | Where DMP is silent or differs | Candidate | State |
|---|---|---|---|---|---|
| F1 | `Dmp/Layer.lean`, `empty_list_makes_everything_independent` | Independence is relative to the declared failure-class list, so with an empty list any two witnesses are independent, the same witness twice included. A pressed pair would count as minted. | The words: "Independence is always relative to that list; the list is configuration (T4)." G0 and T-P speak of "two people" absolutely. The text never says the person is always declared. | `DoT.minted` reads the list as `person :: list`: one class is not configuration. Candidate wording for the words: "... and whatever else the minting lists; the person is always among them." | open, for the owner |
| F2 | gravity#2 `R2Stable.lean` (settling is an equilibrium, not the optimum); the owner 2026-10-26 16:24Z (precompute the perfect deployment) | The expected field (depths, masses, windows, demands, the Φ=0 target and its digest) is a function of the recipe alone and can be precomputed (T33). The settled placement after Lensing is deterministic only given the same start and the same history of losses and ageing; different histories can settle in different equilibria, and an equilibrium need not be the minimum. | T33 speaks of the field "up to identity"; nothing in DMP asks for a canonical equilibrium or a tie-break between layouts of equal potential. | Prove the precomputable half (step 4). Decide later whether the recipe carries a tie-break rule so that the equilibrium is canonical, or whether "the perfect deployment" means the Φ=0 target and the temperature is the distance from it. | open, for the owner |
