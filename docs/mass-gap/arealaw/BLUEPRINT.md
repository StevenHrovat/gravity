# Blueprint: the strong-coupling area law for U(n) / SU(2) lattice gauge theory, in Lean (2026-11-21)

Goal: for a compact gauge group G ⊆ U(n) with centre element z = −1 (U(n), SU(2), SU(n) with n even), Wilson action at small β ≥ 0, on
the periodic lattice (ℤ/Nℤ)^d, and the R × T rectangular Wilson loop C in a plane (μ, ν):

  |⟨W_C⟩| ≤ K₀ · e^{κ₁ · |C|} · (K · (e^{2nβ} − 1))^{A},   A = min(R·T, N² − R·T),

with constants depending only on d and n (|C| = 2(R + T) links). That is the area law. Everything is finite (finite lattice, finite sums);
no limit is taken. Known mathematics (Osterwalder–Seiler 1978, via cluster expansion).

**Prior formalisations (found 2026-11-21, after this blueprint was written).** This is not the first Lean area law:
`github.com/bharathsrivats/fisher-lorentz-formalization` proves a general SU(N) strong-coupling area law (`area_law_general`, checked
here: no `sorry`; the repository carries no licence, so nothing is copied from it), and `github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME`
claims one (not checked). What this project adds is an independent proof by a different route (Kotecký–Preiss cluster expansion from
balaban-lean, a centre-parity selection rule, and a minimal-area count by projection to the loop's plane), on a narrower window of β.
It is a cross-check, not a first.

Reused: `scottnarmstrong/balaban-lean` (Apache-2.0), `Balaban.Polymer`: `Xi`, `KPCond`, `pe_xi_eq_exp`, `pe_logSeries_bound`,
`decomposition`, `pe_lattice`, `card_animals_le`, `RootedAnimals`. Ours: `AreaLaw.Lattice`, `WilsonLoop`, `CentreSymmetry`, `Expansion`.

## Notation

- μ = product Haar measure on connections (`productHaar`), single-link measure invariant under left and right multiplication by any
  group element (hypotheses), and under left multiplication by z.
- For a plaquette p: x_p(U) = Re tr U_p ∈ [−n, n]. Weight e^{β x_p}. c₀ = ∫ e^{β Re tr U} dHaar(U) (one link).
- g(x) = e^{βx}/c₀ − 1. Even and odd parts: g⁺(x) = cosh(βx)/c₀ − 1, g⁻(x) = sinh(βx)/c₀.
- ε = e^{2nβ} − 1. Bounds (P6): |g|, |g⁺|, |g⁻| ≤ ε on [−n, n] (uses 1 ≤ c₀ ≤ e^{nβ}).
- Plaquette graph H: vertices = plaquettes, p ~ q iff they share a link. Degree ≤ Δ := 4·(2(d−1) − 1).
- A set X of plaquettes is *link-connected* if connected in H. Polymers = nonempty link-connected sets.

## Steps

**P1 (centred expansion).** ∫ g(x_p(U)) dμ = 0 for each p (Haar invariance moves U_p to a single Haar variable; ∫ e^{βRe tr}/c₀ = 1).
∏_{p∈P} e^{βx_p} = c₀^{|P|} ∑_{X⊆P} ∏_{p∈X} g(x_p). Define I(X) = ∫ ∏_X g dμ and I_C(X) = ∫ W_C ∏_X g dμ. Then
⟨W_C⟩ = ∑_X I_C(X) / ∑_X I(X).

**P2 (factorisation).** If X₁, X₂ share no link (and, for I_C, X₂ shares no link with C), then I(X₁ ∪ X₂) = I(X₁) I(X₂) and
I_C(X₁ ∪ X₂) = I_C(X₁) I(X₂). (Integrands depending on disjoint sets of coordinates of a product probability measure.)

**P3 (no free link).** Not needed for the bound once P4 is used; omitted.

**P4 (parity).** ∏_X g = ∑_{O⊆X} ∏_O g⁻ ∏_{X∖O} g⁺. By `integral_parity_eq_zero` (g⁻ odd, g⁺ even), the term with O integrates to zero
against W_C unless every link ℓ has visits(ℓ, C) + plaqVisits(ℓ, O) even.

**P5 (minimal area).** If O satisfies the parity condition of P4 for the rectangle C (1 ≤ R, T and R, T < N), then O contains at least
A = min(R·T, N² − R·T) plaquettes in the plane (μ, ν). Proof: project to the (μ, ν) torus. For a link in direction μ, sum the parity
condition over the N^{d−2} links with the same (μ, ν)-projection: plaquettes in planes (μ, ρ), ρ ∉ {μ, ν}, contain two such links and
cancel; the (μ, ν)-plaquettes give a(i, j) + a(i, j−1), with a(i, j) the parity of the number of (μ, ν)-plaquettes of O over the cell
(i, j). So a satisfies a(i, j) + a(i, j−1) = c_μ(i, j), a(i, j) + a(i−1, j) = c_ν(i, j) mod 2, with c the projection of C. On the
connected torus the solutions are a = 1_rectangle or a = 1 − 1_rectangle; each cell with a = 1 holds at least one plaquette of O.

**P6 (bounds).** 1 ≤ c₀ (Jensen, ∫ Re tr U dHaar = 0 by the centre flip) and c₀ ≤ e^{nβ}; hence |g|, |g⁺|, |g⁻| ≤ ε; |W_C| ≤ n.

**P7 (polymer gas).** Decompose each X into its link-connected components (`decomposition`): ∑_X I(X) = Xi(polymers on H, activity I(γ),
incompatible iff sharing a link). For the numerator, the components touching C (sharing a link with C) form Y ("C-attached"); the rest
is a family of polymers sharing no link with Y ∪ C. So
⟨W_C⟩ = ∑_{Y C-attached} I_C(Y) · Xi(polymers avoiding Y ∪ C) / Xi(all polymers).

**P8 (cluster ratio).** |I(γ)| ≤ ε^{|γ|} (P6). For ε small enough (in terms of Δ), `pe_lattice` gives KP with per-vertex bound α;
then |log Xi(all) − log Xi(avoiding S)| ≤ α · #(plaquettes adjacent to S) and |Xi(avoiding S) / Xi(all)| ≤ e^{α·(Δ' |S|)}, with S a
set of links and Δ' = 2(d − 1) plaquettes per link.

**P9 (assembly).** |I_C(Y)| ≤ n · 2^{|Y|} ε^{|Y|} if some O ⊆ Y satisfies the parity condition, else 0 (P4). By P5 such Y have
|Y| ≥ A. With x = 2 ε e^{4 Δ' α}: |⟨W_C⟩| ≤ n e^{Δ' α |C|} ∑_{Y C-attached, |Y| ≥ A} x^{|Y|} ≤ n e^{Δ' α |C|} x₀^{A} ∑_{Y C-attached}
(x/x₀)^{|Y|} for any x ≤ x₀ ≤ 1, and the last sum is at most exp(c · |C|) by the rooted-animal count. Choosing x₀ = √x gives the area
law with K · ε ↦ √(2ε) e^{2Δ'α}: |⟨W_C⟩| ≤ n e^{c'|C|} (2ε)^{A/2} e^{...}. (Any fixed power of ε per plaquette is an area law.)

## Division of labour

- P5: self-contained combinatorics on `AreaLaw.Lattice` and `WilsonLoop` (file `AreaLaw/MinArea.lean`).
- P8: self-contained on a finite bounded-degree graph with `Balaban.Polymer` (file `AreaLaw/ClusterRatio.lean`): the ratio bound for a
  polymer gas restricted to polymers avoiding a vertex set.
- P1, P2, P4, P6, P7, P9: measure side and assembly (files `AreaLaw/Expansion.lean`, `AreaLaw/Integrals.lean`, `AreaLaw/Assembly.lean`).

## Status (2026-11-21): complete

All steps are proved; `lake build AreaLaw` succeeds, no `sorry`, and `#print axioms` on the final theorems shows only `propext`,
`Classical.choice`, `Quot.sound`. The final statements (`AreaLaw/Concrete.lean`) are `wilson_area_law_SU2` and `wilson_area_law_Un`: for
SU(2) and U(n) with normalised Haar measure, on (ℤ/Nℤ)^d, β ≥ 0 with e^{nβ} − 1 ≤ 1 / (4 e^{16d+1} (16d+1)⁴), and an R × T rectangle
(1 ≤ R, T < N), the partition function is nonzero and

  |⟨W_C⟩| ≤ n · e^{16d(R+T)} · (e^{16d+1} (e^{nβ} − 1))^{A/2},   A = min(R·T, N² − R·T).

The base of the power is below 1 throughout the allowed range, so the bound decays with the area. Differences from the goal stated at the
top: the smallness parameter is e^{nβ} − 1 (what the measure lemmas use), and the plaquette graph's degree bound is 16d (proved), giving
the constants above. The window of β is very small (for d = 4, β below about 4 × 10⁻³⁷; this β multiplies Re tr U_p, so for SU(2) it is half the standard β): this is a proof of the strong-coupling regime only,
like every cluster-expansion area law, and says nothing about the continuum. `wilson_area_law_explicit` is the same result for any
compact group with a continuous unitary representation, a left-invariant Haar probability measure and a central z with rep z = −1.
Files: `Lattice`, `WilsonLoop`, `CentreSymmetry`, `Expansion`, `Integrals` (P1, P2, P4, P6), `ClusterRatio` (P8), `MinArea` (P5),
`Assembly` (P7, P9), `Concrete` (finiteness, degree and perimeter bounds, SU(2) and U(n)). Proof work on `ClusterRatio`, `MinArea`,
`Assembly` and `Concrete` was done by Opus subagents and checked here (build, escape-hatch scan, axioms).
