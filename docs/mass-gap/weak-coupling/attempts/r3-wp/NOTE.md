# Round 3, attempt 3 (r3-wp): the form of W_p, the Balaban map, and the one-block step (2026-11-21)

Brief: settle the form of W_p (the quantum half, `../r2-stepscaling/NOTE.md` §4), map it against Balaban's large-field
programme, attack the single-block version for SU(2) with the Wilson action (no admissibility). Rules: `../RULES.md`
with the round-2 and round-3 additions.

Claim levels: **proved (Lean)**, **proved (paper)**, **certified** (interval arithmetic, computer-assisted),
**standard** (literature, cited, not reproved), **reading** (read in the OpenAI source, not verified by a build or a
proof of ours), **heuristic**, **open**.

Files:
- `PREREG.md`: written before any computation.
- `chain_float.py`, `chain_float.json`: float design run.
- `chain_cert.py`, `chain_cert.json`, `chain_cert.log`: the certificate. One process, CPU, 74 s in total.
- `build.sh`: Lean build in `~/formal-att-r3-3`.
- Lean: `../../../formal/Attempts/R3/WpNoise.lean`. It builds ("Build completed successfully"), with no `sorry`, no
  `native_decide` and no new axioms. `#print axioms` on all five main theorems gives `propext`, `Classical.choice` and
  `Quot.sound` only.

---

## 0. Result in one paragraph

**W_p as stated is not an open large-field problem. It is a compactness statement once one blocking step is noisy.**
A noisy blocking step draws the coarse field from a kernel around a prediction. The OpenAI construction blocks this way
at every level: `RG/Block.lean`, `noise`, `penaltyWeight` (reading). The coarse density is then a mixture of
continuous kernels bounded below. Two consequences follow:
- The large-field lower bound that `../H1-OPENAI.md` (Stage A) and attempt D named as the missing piece comes free:
  on every configuration, however large the field, ρ ≥ min K > 0.
- Relative sup-norm convergence on all configurations, per volume, is then equivalent to weak convergence of the laws
  of the predictions (Lean: `noise_uniform`).

By Prokhorov compactness it holds along a subsequence for every sequence of bare theories (Lean: `noise_subseq`). With
the subsequence principle (Lean: `eventually_of_subseq`), uniqueness of the limit is not needed for the gap. It
suffices that (H2) holds for every limit point with one constant.

So the weakest sufficient form of W_p is *nothing beyond compactness*, at the price of moving all uniqueness questions
into H2. The sufficiency chain is proved, except for one classical step not formalised here: Theorem A with tails.

The Balaban large-field machinery, the "basic step of the R operation" (CMP 122, 1989), is needed:
- not for W_p per volume;
- for a volume-uniform (local) W_p, where the missing input is a *relative* (ratio) bound on large-field activities,
  which nobody has proved;
- for the crossover, where it would have to carry the flow from g² ≈ 10⁻⁶ towards O(1). That is where the large-field
  problem really lives.

**Single block.** For one noisy step of one block the large-field bound is explicit and uniform in everything (§3.1).
For the one exactly computable SU(2) Wilson block (2D, ℓ × ℓ plaquettes) the relative error is certified on all
configurations, U = −1 included:
- the error is largest at U = −1 and falls like ℓ⁻⁴;
- δ ≤ 9.4·10⁻⁴ at ℓ = 8, t = 1, and δ ≤ 2.8·10⁻³ at ℓ = 8, t = 0.5;
- the naive "absolute error / minimum density" conversion is 5·10⁴ times worse at t = 0.5.

All three pre-registered predictions pass.

## 1. Is W_p the right statement? The weakest sufficient form

### 1.1 W_p as stated, and why the large-field worry dissolves per volume

W_p (attempt D, §4): per volume, sup_U |log ρ_{k,p}(U) − log ρ_{∞,p}(U)| ≤ ε_k(v) → 0, on all configurations. The
worry: on large fields the densities are tiny (e^{−c/g²}), and relative closeness there looks like a delicate
large-deviation statement.

Three structural facts settle the per-volume form.

1. **Compact configuration space.** In a fixed volume the coarse field lives on G^n, n coarse links, G = SU(2). There
   are no fields at infinity. "Large" means far from the identity on a compact set.
2. **Noisy blocking (the noise lemma).** Let the last blocking step into the scale draw V from a kernel K(V, Q) around a
   prediction Q, with K continuous and bounded below by m > 0. Examples:
   - heat-kernel noise;
   - Wilson-type noise κ_β(W) ∝ e^{(β/2) tr W};
   - OpenAI's penalty noise Z⁻¹ e^{−β·penalty·price(V Q⁻¹)}, mixed over random frames by `likelihood` (reading:
     `RG/Block.lean`, `noise`, `IsKernel`).

   If ν is the law of the prediction, the coarse density is ρ_ν(V) = ∫ K(V, Q) dν(Q). Then:
   - (a) ρ_ν ≥ m on every V (`le_integral_of_forall_le`). For a product kernel the bound is m₀ⁿ
     (`prod_kernel_lower`). **This is the large-field lower bound, supplied by the noise, not by the action.**
   - (b) If K_k → K_∞ uniformly and ν_k → ν_∞ weakly, then log ρ_k → log ρ_∞ uniformly on all of G^n. This is
     **`noise_uniform`, proved (Lean)**: a finite δ-net, uniform continuity of K on the compact product, and
     |log a − log b| ≤ |a − b|/m.
   - (c) Conversely, uniform convergence of ρ_k forces weak convergence of the smoothed laws. For heat-kernel noise
     this is weak convergence of ν_k itself, since the heat kernel's character coefficients e^{−tC(λ)} never vanish
     (**proved, paper**, one line).

   So, per volume, **W_p ⇔ weak convergence of the prediction laws.**
3. **Compactness (Prokhorov).** Probability measures on a compact metric space form a compact space (Mathlib:
   `Prokhorov.lean`). Every sequence of bare theories therefore has a subsequence along which W_p holds
   (**`noise_subseq`, proved (Lean)**).

### 1.2 From W_p to H1, uniformly in the boundary condition

Lemma T (attempt D, **proved, paper**) does the transport:
- relative closeness e^{±ε} of the densities at one scale survives every later blocking step, deterministic or noisy;
- it passes to every conditional law with factor e^{±2ε}, **uniformly over all boundary conditions**, large-field
  boundaries included.

Hence TVClose ≤ e^{2ε} − 1 and SpecDist ≤ |B|(e^{2ε} − 1) for every block at L₁, per volume. The noise is what makes
this uniform: without a lower bound, a boundary on which the density is tiny could carry an uncontrolled conditional
law.

### 1.3 The weaker forms, compared

| form | statement (per volume v, k → ∞) | suffices for H1 uniformly in the boundary? |
|---|---|---|
| W_p (as stated) | sup \|log ρ_k − log ρ_∞\| → 0 on all configurations | yes (Lemma T) |
| **W_p^w (weak)** | **the prediction laws of one noisy step at some scale ≤ L₁ converge weakly** | **yes**: noise lemma ⇒ W_p at that scale ⇒ Lemma T |
| W_p^{sub} (subsequential) | nothing: compactness | yes for the gap, if (H2) holds for **every** limit point with one γ (`eventually_of_subseq`) |
| W_p^{sf} (small fields + mass) | relative closeness on small fields, large-field mass → 0 | without noise: **no** (example below); with one noisy step: yes, since it implies TV and hence weak convergence |
| specification form | single-site conditional densities relatively δ-close | per volume **equivalent** to W_p with ε ≤ 2nδ (Brook's identity, below); **not** transportable with volume-uniform constants |

**Why W_p^{sf} fails without noise.** Take two densities equal on the small-field set S. Let them differ arbitrarily on
a large-field set of mass η. Choose a boundary condition that forces the block into the large-field set, for example
one with a large plaquette straddling the block boundary. Its conditional laws are then unrelated, for every η > 0.
GDS takes a supremum over boundaries, so closeness "on average over boundaries" is not enough. A "GDS with rare bad
boundaries" (disagreement percolation) would rescue it, but no such Theorem A exists in our framework. The noise makes
this unnecessary.

**Brook's identity (proved, paper).** For positive densities on a product of n coordinates,
ρ(x)/ρ(y) = ∏ᵢ ρ(xᵢ | x_{<i}, y_{>i}) / ρ(yᵢ | x_{<i}, y_{>i}).
If the single-site conditional log-densities of ρ_k and ρ_∞ differ by at most δ everywhere, then
osc(log ρ_k − log ρ_∞) ≤ 2nδ. Since both densities integrate to 1, the difference changes sign, so
sup |log ρ_k − log ρ_∞| ≤ 2nδ.

So the specification form is the "local" form. It is equivalent per volume, but the factor n is the volume. A
volume-uniform specification form does *not* transport to L₁ with uniform constants. That would need a Dobrushin-type
decoupling at every scale between L_p and L₁, which is the crossover's content. Blocked specifications can even fail to
exist as Gibbsian objects (van Enter–Fernández–Sokal, **standard**).

### 1.4 The weakest sufficient form, and the status of its sufficiency

**Statement (W_p^min).** There is a scale L_p ≤ L₁ at which the block variables are produced by a noisy step (a kernel
with a continuous density bounded below). No convergence hypothesis at all is needed. The gap conclusion follows from:
- **(H2-all)** every subsequential limit of the block theory at L₁ (in each volume v), which exists by compactness,
  satisfies GDS with exponentially weighted influence sums, with one γ < 1 and one weight rate for all v and all limit
  points;
- **Theorem A with tails** (below).

If the limit is unique (the full sequence converges weakly, see §2.2 for OpenAI), (H2-all) is (H2) for that one
theory.

**Sufficiency chain and status:**
1. Noise lemma: absolute or weak ⇒ relative on all configurations. **Proved (Lean)**: `noise_uniform`, `noise_subseq`,
   `abs_log_sub_log_le`, `le_integral_of_forall_le`, `prod_kernel_lower`.
2. Lemma T: relative closeness ⇒ conditional laws at L₁ e^{±2ε}-close, uniformly in the boundary. **Proved (paper)**,
   attempt D. Not in Lean.
3. Per-volume reduction: in `gap_of_effective` the rate and the prefactor do not depend on δ, so δ_k(v) → 0 per v is
   enough in the order mesh first, then volume. **Proved (paper)**, `../H1-OPENAI.md` §4. Not in Lean.
4. Subsequence principle. **Proved (Lean)**: `eventually_of_subseq`.
5. **Theorem A with tails. Classical, not formalised here; the one real gap in the chain.**
   - Noisy blocked specifications are not finite range: the conditional law of a block depends on the whole torus. Our
     Theorem A needs finite range (`IsLocal`, `UniformGeometry`).
   - What is needed is Dobrushin's condition with exponential weights,
     sup_j Σ_{z∉B_j} κ_j(z) e^{λ d(z, B_j)} ≤ γ < 1, which gives exponential decay of covariances (Dobrushin 1970;
     Gross 1979; Kuensch 1982, **standard**).
   - The perturbation from step 2 is uniform in (j, z), not decaying. In volume v it adds at most
     |Λ_v| e^{λ diam(v)} |B|(e^{2ε_k} − 1) to the weighted sum. This → 0 as k → ∞ at fixed v (**proved, paper**,
     elementary).

**Plausibility of W_p as stated (deterministic block variables, no noise): heuristic yes, but not recommended.**
- With deterministic block averaging, the coarse density on a coarse large field is a genuine large-deviation
  quantity. The minimiser is a smooth fine field (coarse curvature O(1) means fine plaquettes O(a²/L_p²)), so the
  relevant fine fluctuations are small-field ones around a smooth background. Relative convergence there is plausible
  (heuristic).
- §3.2 certifies it in the one solvable SU(2) case.
- But equicontinuity and positivity of log ρ_k become real estimates, and deterministic block maps can have
  degenerate points (non-unique minimisers, such as flux ±π). The noise removes all of this at no cost.
- Recommendation: **state H1 with one noisy step**, as OpenAI does.

## 2. The map against Balaban

### 2.1 What the large-field programme proved

All citations below are standard. The bibliographic data of the starred items was checked online; the content is from
abstracts and secondary sources, not from the originals.
- **Small fields.** Balaban, "Renormalization group approach to lattice gauge field theories. I. Generation of
  effective actions in a small field approximation and a coupling constant renormalization in four dimensions", CMP
  109 (1987) 249–301*. II, "Cluster expansions", CMP 116 (1988) 1–22*. "Convergent renormalization expansions for
  lattice gauge theories", CMP 119 (1988) 243–285 (from memory).
- **Large fields.** "Large field renormalization. I. The basic step of the R operation", CMP 122 (1989) 175–202*.
  "II. Localization, exponentiation, and bounds for the R operation", CMP 122 (1989) 355–392*.
  - The abstract of I says the R operation, which renormalises expressions attached to large-field regions, "removes
    the main obstacle to proving ultraviolet stability of four-dimensional gauge field theories". The proof is
    completed in II.
- **3D.** "Ultraviolet stability of three-dimensional lattice pure gauge field theories", CMP 102 (1985) 255–275*.
- **Expositions.** Dimock, "The renormalization group according to Balaban", I (small fields, arXiv:1108.1335), II
  (large fields, arXiv:1212.5562, J. Math. Phys. 54 (2013), DOI 10.1063/1.4821275), III (arXiv:1304.0705). They treat
  φ⁴₃, not gauge theory.
  - The large-field mechanism, as presented in II: a cube is a large-field cube if a Gaussian, gradient or potential
    condition fails at the threshold p₀ = (−log λ)^p. Each such cube costs e^{−O(1)p₀²}, so a large-field region Ω^c
    costs e^{−O(1)p₀²|Ω^c|}.
  - The output is **stability bounds** on the partition function, uniform in the cutoff, with convergence of the
    expansions completed in III.
- **What the programme gives, in one line:** ultraviolet stability, i.e. upper and lower bounds e^{±E|Λ|} on
  partition functions and bounded effective actions, uniformly in the cutoff in finite volume (standard reading, also
  in `../PREP.md` §2).
  - **Upper** bounds on large-field contributions, localised and exponentiated.
  - **Not** convergence as the cutoff is removed.
  - **Not** relative (ratio) bounds on large-field activities.
  - **Not** any control at O(1) coupling.
  - Secondary sources remark that UV limits of gauge-invariant observables would then follow by compactness along
    subsequences. That is the same mechanism as §1.1.3.

### 2.2 The exact large-field lemma at each level, and who has it

| what is wanted | large-field input needed | Balaban | OpenAI | status |
|---|---|---|---|---|
| **W_p, per volume, subsequential** | none (noise gives ρ ≥ min K; compactness gives limits) | not needed | not needed | **proved here** (Lean core) |
| **W_p, per volume, full sequence** | the level-0 density converges in sup norm (absolute). In finite volume the polymer gas is a finite sum, so sup-norm convergence of each large-field activity Kᵢ suffices; **no lower bound** | upper bounds only, no convergence | `Winter.convergence`: level-0 activities converge in a norm whose docstring lists "K sup and E regular derivatives" (reading); `Transfer`: level-m `eval` is the push of level m+1, on all configurations (reading) | **reduced** to one reading check: is `Rep.eval` continuous in their `Show` norm? If yes, W_p holds along their sequence by `noise_uniform` |
| W_p, volume-uniform (local) | **ratio bounds**: \|K_N(X,·) − K_∞(X,·)\| ≤ δ_N\|K_∞(X,·)\|, or gas_N/gas_∞ ∈ e^{±δ\|X\|} on all configurations | not proved (upper bounds e^{−κp²\|X\|} only) | not proved (K from above only) | **open, and not needed** for the gap in the order mesh, then volume |
| crossover (H2 side: from bar ≈ 10⁶ to O(1)) | the R operation at every scale while g is small, then something new at g ~ 1 | small g only (thresholds p(g) need g → 0) | stops at bar by construction (`Bar.threshold`) | **open**: the true home of the large-field problem |

**Correction to the record.** `../H1-OPENAI.md` Stage A and attempt D's §5(ii)(a) named "lower bounds on large-field
activities" as the missing half of W_p. For W_p in the per-volume form they used, that bound is not needed:
- the relative form follows from the absolute one, because the density, not its polymer representation, is bounded
  below by the noise;
- what is missing is only the qualitative identification of OpenAI's norm convergence with sup-norm convergence of
  `eval` (a reading check), or nothing at all in the subsequential form.

The lower-bound problem is real for a **volume-uniform** W_p, but the gap does not need that form.

**The honest catch.** All of this makes H1 per volume cheap because it moves everything into H2:
- H2 is now about every limit point of a theory at β = bar ≈ 9·10⁵, blocked about 10⁷ e-folds to L₁;
- it carries all of the running, all of the large-field control along the way, and uniqueness.

This is `../H1-OPENAI.md` §4's catch made exact. **W_p is not where the difficulty is.**

## 3. The single-block step

### 3.1 One noisy step of one block: the large-field bound, explicit (proved, paper; Lean for the abstract part)

SU(2) with Wilson-type noise. In normalised Haar measure,
κ_β(W) = β e^{β cos θ}/(2 I₁(β)), where tr W = 2cos θ and θ ∈ [0, π] is the bi-invariant geodesic distance to 1.

For any fine theory, any volume, any boundary, and any coarse configuration V:
1. **Two-sided bound.** β e^{−β}/(2I₁(β)) ≤ κ_β ≤ β e^{β}/(2I₁(β)), so ρ ∈ [κ_min^n, κ_max^n]. Per link the ratio is
   e^{2β}.
2. **Log-Lipschitz bound.** |log ρ(V) − log ρ(V′)| ≤ β Σ_e d(V_e, V′_e). Reason: cos θ is 1-Lipschitz in d, d is
   bi-invariant, and a mixture of functions with log-Lipschitz constant β has the same constant. So the conditional
   density of one coarse link, given everything else, lies in [e^{−βπ}, e^{βπ}] relative to Haar.
3. **Quantitative transport.** |log ρ_ν(V) − log ρ_ν′(V)| ≤ β·W_∞(ν, ν′), where W_∞ is the ∞-Wasserstein distance for
   the ℓ¹ sum of link distances.
   - Proof: couple Q ~ ν and Q′ ~ ν′ with Σ_e d(Q_e, Q′_e) ≤ D almost surely. Then each kernel product changes by at
     most a factor e^{βD} pointwise.
   - Unlike the conversion "absolute error / minimum", this carries no factor e^{2βn}.
4. **Conversion constant per volume.** sup |log ρ_k − log ρ_∞| ≤ ‖ρ_k − ρ_∞‖_∞ · (2I₁(β) e^{β}/β)^n.
   - With OpenAI's noise at β of order bar (~10⁶), this is qualitatively fine and quantitatively astronomical.
   - That is the exact sense in which large fields cost nothing qualitatively and everything quantitatively.

**Check against H2 (no fake gap).** Bound 2 is not local:
- every coarse link, however far, may move log ρ by up to βπ;
- so the a-priori influence sum over a torus grows with the volume.

The noise yields no GDS and no decay by itself. For U(1) the same bounds hold and the photon stays massless.

**From one block to the full volume:** nothing remains for this form. The noisy step factorises over coarse links,
`prod_kernel_lower` gives the volume bound, and `noise_uniform` is stated on the whole configuration space of a volume.

### 3.2 The quantitative one-block test: SU(2) Wilson, one 2D block, all configurations (certified)

**Setup.**
- A 2D block of ℓ × ℓ Wilson plaquettes. In axial gauge the plaquettes are independent, and the block plaquette is
  their product: a chain of n = ℓ² SU(2) elements.
- Block density ρ_n = w_β^{*n} = Σ_j (2j+1) d_j(β)ⁿ χ_j, with d_j = I_{2j+1}(β)/I₁(β).
- Limit: the heat kernel K_t = Σ_j (2j+1) e^{−t j(j+1)} χ_j.
- Tuning (line of constant physics by a block observable): d_{1/2}(β_n)ⁿ = e^{−3t/4}, so ⟨χ_{1/2}⟩ is the same as in
  the limit. β_n = 8.48, 32.50, 128.50 (t = 1) and 16.49, 64.50, 256.50 (t = 0.5) for ℓ = 2, 4, 8.
- δ_n = sup over **all** θ ∈ [0, π] of |log ρ_n − log K_t|. θ = π is U = −1, the largest field; at t = 0.5,
  K_t(π)/K_t(0) ≈ 2·10⁻⁷.

**Method (`chain_cert.py`).**
- mpmath interval arithmetic, 50 digits.
- Bessel values by their power series with a rigorous tail bound. For ν > β, the Bessel tail uses
  I_ν/I_{ν−1} < β/(2ν), from I_{ν−1} − I_{ν+1} = (2ν/β)I_ν.
- Character sums truncated at 2j+1 ≤ 36, with tail bounds (≤ 10⁻⁵⁵).
- The sup over θ by 1000 cells: sixth-order Taylor enclosures of ρ, ρ′, ρ″ with a global seventh-derivative remainder,
  and f = log ρ − log K enclosed by f(c) + f′(c)h + f″(cell)h²/2.
- t is enclosed exactly from the rational β_n.

| t | ℓ | n | **certified δ_n ∈** | sup at | n²δ_n |
|---|---|---|---|---|---|
| 1 | 2 | 4 | [0.272019, 0.272023] | θ = π | 4.35 |
| 1 | 4 | 16 | [0.0155326, 0.0155329] | θ = π | 3.98 |
| 1 | 8 | 64 | [9.40130, 9.40145]·10⁻⁴ | θ = π | 3.85 |
| 0.5 | 2 | 4 | [0.745352, 0.745373] | θ = π | 11.9 |
| 0.5 | 4 | 16 | [0.0448951, 0.0448964] | θ = π | 11.5 |
| 0.5 | 8 | 64 | [2.76363, 2.76374]·10⁻³ | θ = π | 11.3 |

Float design run (not certified): ℓ = 1 gives δ = 1.90 (t = 1) and 6.66 (t = 0.5). The naive bound
N_n = sup|ρ_n − K_t| / min K_t gives 0.374 and 0.0226 at t = 1, and 2325 and 143 at t = 0.5 (ℓ = 4, 8).

**Pre-registered predictions: all pass.**
- **P1 (contraction):** the certified ratios δ_{4n}/δ_n are 0.0571 and 0.0605 (t = 1), and 0.0602 and 0.0616
  (t = 0.5). All are ≤ 1/2; they are in fact ≈ 1/16, i.e. δ ∝ ℓ⁻⁴.
- **P2 (no large-field blow-up):** n·δ_n = 0.25, 0.060 (t = 1) and 0.72, 0.18 (t = 0.5). All are far below 20/t.
- **P3 (naive conversion lossy):** N_n/δ_n = 5.2·10⁴ at t = 0.5 for both n (float). At t = 1 it is 24.

**Reading.**
- In the one solvable SU(2) Wilson block, relative convergence on all configurations holds with the natural rate of an
  irrelevant correction, ℓ⁻⁴ = n⁻². The constant C(t) = n²δ_n → 3.85 (t = 1) and 11.3 (t = 0.5) is comparable to the
  classical estimate π⁴/(12t), off by a factor 0.5–0.7 (heuristic).
- The worst point is the largest field. Its error is about 50 times the small-field error, but it is not exponentially
  larger. The density at U = −1 is approached relatively because lattice and limit are dominated by the same smooth
  path (uniform rotation), so their ratio is a smooth correction.
- Converting absolute closeness into relative closeness through the minimum density loses a factor of order e^{π²/t}.
  The truth does not.

This supports W_p as stated (deterministic variables, quantitative) as plausible. It is evidence, not proof, for 4D.

**What remains from this one block to a 4D full volume (the obstruction, precisely):**
1. **Inter-block coupling.** In 2D the blocks decouple exactly, because there is no Bianchi constraint. In 3D and 4D
   adjacent blocks share plaquettes and fine links. The block law is not a convolution, and one needs a cluster
   expansion in the inter-block coupling, uniform on large-field boundaries: Balaban's small-field expansions
   (CMP 116, 119) plus the R operation (CMP 122) for upper bounds. **The ratio (relative) version is missing.**
2. **Running.** The 2D chain is superrenormalisable (t = g²·area, no logarithms). In 4D the fine fluctuations inside
   one block renormalise the coupling, and relative control must survive the one-loop shift. This is small-field
   territory (Balaban CMP 109; OpenAI `Transfer`), but has not been proved on large-field backgrounds in relative
   form.
3. **Uniformity in the volume.** Needed only for the local form, which the gap does not need (§2.2).

For the per-volume form none of 1–3 is needed (§3.1).

## 4. Unit tests

- **Photon (4D U(1), weak coupling).**
  - Everything in §1 and §3.1 holds verbatim for U(1), a compact group: noisy block laws converge per volume along
    subsequences to the free photon's block laws.
  - That is fine: W_p is gap-free.
  - Nothing here gives a gap. The noise lemma's a priori bounds are not local (§3.1), so they give no GDS. The gap
    still needs (H2), which fails for the Gaussian photon limit by the sum rule (round 1, route (c)).
  - The 2D certificate is 2D SU(2) and claims nothing about any 4D theory.
- **Z₂.**
  - The group is finite, so the configuration space per volume is finite. There is no continuum of fields, no Gaussian
    regime and no "small field" except the flat one.
  - Every excitation is a discrete defect (a frustrated plaquette) costing 2β. In Balaban's sense there are no large
    fields to control: the problem the R operation solves (fields between the perturbative scale and O(1)) does not
    arise. At weak coupling the convergent low-temperature (Peierls) expansion covers everything.
  - W_p reduces to convergence of finitely many probabilities, and the noise (random flips) gives the lower bound
    trivially.
  - Gap-only test: the chain's conclusion is decay, true for weak-coupling Z₂. Nothing here implies an area law.
  - Z₂ has no line of constant physics from weak coupling, so the continuum statements are silent for it.
- **Triviality (φ⁴₄).**
  - The analogue of §1 for φ⁴₄ gives at most subsequential per-volume limits of block laws (with ℝ as target one also
    needs tightness, and the Gaussian noise lower bound fails at |φ| → ∞). By Aizenman–Duminil-Copin those limits are
    Gaussian.
  - W_p-type statements are existence-of-a-limit statements and **never** yield non-triviality. Nothing here does.
  - What makes the difference in the gauge setting is the line of constant physics. Asymptotic freedom allows the
    coupling at L_p to be held at a fixed non-zero value (OpenAI `reaches`: β = bar at level 0 for every cutoff) while
    the bare coupling → 0.
  - The block coupling at L_p is a weakly continuous functional of the block law, so it passes to every limit point.
    Non-triviality of the continuum theory itself (as a theory of local fields) is OpenAI's `nonfree`, not ours.
  - For φ⁴₄ such tuning is impossible: the renormalised coupling at a fixed scale → 0.
  - The compact target also matters: per volume there is no large-field region at infinity, which is what lets
    compactness and the noise do the work.

## 5. Under admissibility (r3-dmp's theory)

How much of this would become trivial:
- **§1 (form, noise lemma, compactness):** nothing. It never used the action, so it holds unchanged with or without
  admissibility.
- **§2:** the fine-scale part of the volume-uniform large-field lemma (rough fine fields) becomes vacuous. Coarse-scale
  large fields remain: smooth fine fields with coarse curvature O(1), i.e. topology, and so does the crossover.
- **§3.1:** unchanged.
- **§3.2:** admissibility would *hurt* the relative form at small blocks. With fine plaquette angles ≤ ε, the product
  of n of them has angle ≤ nε, so the deterministic block density vanishes on coarse fields beyond nε (for example
  θ > 1.92 at n = 64, ε = 0.03), and relative closeness to the heat kernel fails there until n ≥ π/ε. One more reason
  to block with noise.

In short, about a quarter of the large-field content (the fine-scale, volume-uniform part) becomes trivial. The
per-volume H1 needs no large-field input with or without admissibility.

## 6. Verdicts

| statement | status |
|---|---|
| Noise lemma: weak convergence + continuous kernel ≥ m ⇒ uniform relative convergence on all configurations (`noise_uniform`) | **proved, Lean** |
| W_p along a subsequence for every sequence (`noise_subseq`, Prokhorov) | **proved, Lean** |
| Subsequence principle (`eventually_of_subseq`); \|log a − log b\| ≤ \|a−b\|/m; mixture and product lower bounds | **proved, Lean** |
| Per volume: W_p ⇔ weak convergence of the prediction laws (heat-kernel noise) | **proved, paper** (⇐ Lean; ⇒ Fourier, one line) |
| Specification form ⇔ density form per volume, factor 2n (Brook) | **proved, paper** |
| W_p^{sf} insufficient without noise, uniformly in the boundary | **proved, paper** (example) |
| Weakest sufficient form W_p^min (one noisy step, nothing else, with H2 for all limit points) ⇒ gap per volume | **proved, paper**, except Theorem A with tails (**standard**, not formalised); Lemma T paper only |
| W_p along OpenAI's full sequence | **reduced** to the reading check "Rep.eval continuous in the Show norm" |
| One noisy step: explicit two-sided, log-Lipschitz and W_∞ bounds for SU(2) Wilson noise | **proved, paper** |
| One 2D SU(2) Wilson block: relative error ≤ 9.4·10⁻⁴ (t = 1) and 2.8·10⁻³ (t = 0.5) at ℓ = 8, max at U = −1, rate ℓ⁻⁴ | **certified** (P1–P3 pass) |
| Volume-uniform W_p: ratio bounds on large-field activities | **open**; not proved by Balaban or OpenAI; not needed for the gap |
| Large-field control through the crossover | **open**: the real home of Balaban's problem |
| Photon, Z₂, triviality | **pass** |

## 7. The single most promising next step

Formalise **Theorem A with exponentially weighted influences** (Dobrushin–Kuensch), together with Lemma T and the
per-volume variant of `gap_of_effective_W`. Then state H1 in Lean as "one noisy blocking step" (no convergence
hypothesis: `noise_subseq` plus `eventually_of_subseq`).

That removes W_p, and with it the whole quantum half, from the list of open hypotheses of the Lean reduction. The only
open hypothesis left would be (H2-all), GDS with tails for every limit point of the noisy block theory at L₁. That is
the crossover, which is where the difficulty actually is.

In parallel, a cheap check that makes the limit unique: read whether OpenAI's `Rep.eval` is continuous in their `Show`
norm. If so, W_p holds along their full sequence by `noise_uniform`, and (H2-all) shrinks to (H2) for one theory.
