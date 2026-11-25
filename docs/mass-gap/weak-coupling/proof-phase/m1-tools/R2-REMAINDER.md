# R2: the remainder route compared with the carrying route (m1-tools, 2026-11-22)

Brief (coordinator; owner's reading `../../PREP.md`, "What does not settle cannot exist"): instead of carrying
long-lived conserved-flux sheets (`R2-REPAIR.md`), prove they are negligible and split them off the law as a remainder of
small total mass, using that M1's block densities are laws.
* (a) Bound the probability of the bad event (a moderate non-central sheet irregular beyond Balaban's delay) per
  physical cell, in physical units, with rigorous lower bounds on the action.
* (b) Split the remainder off at each scale without breaking the inductive form, with total removed mass vanishing or
  uniformly small; say what it does to the main theorem's error terms.
* (c) If both close, say that E8's extension is unnecessary.

Compare with the carrying route and keep the simpler one that closes. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **(a) closes.** A sheet still extended (more than `2·3^d` cubes) `R_s` steps after its birth at scale `s` has
   at least `L^{R_s}/2` sites, so at least `N_s ≥ L^{R_s}/(2 (M R_s)^d)` irregular cubes. Its suppression is
   `exp(-p0² N_s/(4C_d))` ([16] (69)-(71), read; it needs regularity of the finer field, which holds at birth). Its shape
   entropy is `C^{N_s}`. Per scale-`K` cell (the cells at `L_*`) there are `L^{d(K-s)}` positions, and
   `d (K-s) log L ≤ d g_s^{-2}/b` by the running. Since `L^{R_s} ≥ (g_s^{-2})^{r log L}` grows much faster than
   `g_s^{-2}`, every term is `≤ exp(-c L^{R_s}/R_s^d)`, and the sum over birth scales is dominated by `s = K`:
   **`P(bad event in a given L_* cell) ≤ δ(γ) := exp(-c L^{R(γ)}/R(γ)^d)`**, uniformly in the lattice spacing.
   Converting Balaban's bounds into probabilities uses his lower bound on the normalisation ([16] Theorem 1, lower half;
   [V] the analogue) and is paper-level.
2. **(b) does not close as stated.**
   * **Mass:** the removed mass is `≤ δ(γ) |Λ|` (`|Λ|` the number of `L_*` cells). It is not small uniformly in the
     volume, and the decay and transfer bounds of the interface (`BlockGapBddW`, `ObsTransferPhysTW`) are uniform in the
     volume.
   * **Local observables:** `|E[f] - E[f | no bad event within distance D of supp f]| ≤ C D^d δ(γ)` is fine. But the
     law with far-away bad events still has to have the inductive form, because the estimates are global
     representations on the torus.
   * **Global conditioning:** conditioning on "no bad event anywhere" changes local marginals by `O(δ)` only if the law
     decorrelates. That is the output of the whole argument, so using it here is circular unless a separate decoupling
     lemma for rare defects is proved.
   * **What that lemma needs:** a decoupling lemma has to represent the bad regions as localised factors, i.e. carry
     them in a cruder form. So it brings back part of the carrying machinery.
3. **(c) the comparison.** The carrying route of `R2-REPAIR.md` already closes on paper. It needs no decomposition lemma
   (attribution suffices), and its E8 change is one re-reading: Balaban's step-count life control replaced by the summed
   footprint, which is the quantity his cost already sums. The remainder route would need (a), plus a defect-decoupling
   lemma, plus a volume-uniform treatment of the removed mass. **Keep the carrying route.** Result (a) stays as a
   cross-check: long-lived sheets are astronomically rare (`δ(γ)` per `L_*` cell), so the carrying route's error terms
   are dominated by ordinary large-field regions, not by these sheets.

## 1. The count in (a)

For birth scale `s ≤ K` and `j = K - s`:
* **sizes:** extended at age `R_s` means `n_s ≥ L^{R_s}/2` sites (contrapositive of Lemma F), so
  `N_s ≥ L^{R_s}/(2 (M R_s)^d)` cubes;
* **weight:** `≤ exp(-(p0(g_s)²/(4 C_d) - log C) N_s)`;
* **positions:** `L^{d j}` per scale-`K` cell, `j ≤ (g_s^{-2} - g_K^{-2})/(b log L)`.

Hence the exponent is `≤ d g_s^{-2}/b - c p0(g_s)² L^{R_s}/R_s^d`. With `R_s ≥ (log g_s^{-2})^r` the second term wins by a
super-polynomial margin, and the terms decrease super-exponentially as `j` grows. Total `≤ 2 δ(γ)`.

## 2. Why (b) needs more than the mass

Write `ρ_k = ρ_k Π_x (1 - 1_{bad,x}) + (rest)`. The first factor is a product of local characteristic functions, so it
keeps Balaban's form (normalisation absorbed into the vacuum energy). But it is the law **conditioned** on a global event
of probability about `exp(-δ |Λ|)`, not the true law. The rest has mass `≈ δ |Λ|`. To compare the two on local
observables uniformly in `|Λ|`, one expands `Π_x (1 - 1_{bad,x})` as a gas of bad sets `B` with weights `≤ δ^{|B|}`. The
expansion converges only if the terms with `B ≠ ∅` have the inductive form outside `B`. That means representing each `B`
as a frozen large-field region at all later scales, which is the carrying route again, without its renormalisation but
with the same entropy question at the boundary of `B`.

## 3. Status

* (a): paper (probability bound `δ(γ)` per `L_*` cell; normalisation lower bound cited).
* (b): not closed; needs a defect-decoupling lemma; not attempted.
* R2 stays as in `R2-REPAIR.md` (carrying, closed on paper); this note records the comparison and the rarity bound.
