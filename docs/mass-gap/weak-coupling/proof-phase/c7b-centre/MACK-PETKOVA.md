# Mack–Petkova and the status of the 4D Z2 area law (c7b-centre, 2026-11-22)

Claim levels as in c6c: **read** / **abstract** (only abstract or listing read) / **recalled** / **paper**.

## 1. The source

* G. Mack and V. B. Petkova, "Comparison of lattice gauge theories with gauge groups Z2 and SU(2)", **Annals of Physics 123
  (1979) 442–467**, DOI 10.1016/0003-4916(79)90346-4; DESY preprint 78/68 (Nov 1978). **Abstract only** (INSPIRE record 132702,
  OSTI 5470010, Scilit). The full text was not reachable here (the DESY PDF returned empty).
* What the abstract says: a pure SU(2) lattice gauge theory is compared with the model obtained by restricting the link variables
  to Z2; an inequality between Wilson-loop expectation values of the two shows that **confinement of static quarks holds in the SU(2)
  model whenever it holds in the corresponding Z2 model**; the SU(2) model is further shown to have high- and low-temperature
  phases distinguished by the behaviour of the 't Hooft disorder parameter.
* Companion papers: Mack–Petkova, Ann. Phys. 125 (1980) 117 (vortex condensation as a sufficient condition for confinement,
  recalled from Ito–Seiler); Mack–Petkova, "Z2 monopoles in the standard SU(2) lattice gauge theory model", DESY 79/22,
  Z. Phys. C 1 (1979) (listing only).

## 2. The mechanism (reconstruction, not read in the source)

Write each SU(2) link as `U = σ V`, `σ = ±1`, `V` in a section of SU(2) → SO(3). The fundamental Wilson loop is `σ_C · w(V)` with
`|w| ≤ 2`; the plaquette is `Re tr U_p = σ_p r_p(V)` with `|r_p| ≤ 2` (the sign of `r_p` is a frustration that depends on `V`). Given
`V`, the measure on `σ` is a Z2 gauge model with plaquette couplings `β r_p(V)`; replacing those by their worst case `2β` is allowed
by two inequalities of Ising type (Ginibre: `|⟨σ_C⟩_J| ≤ ⟨σ_C⟩_{|J|}`; Griffiths II: monotone in the couplings). This is what
c7b proves in Lean (section 2 of NOTE.md); whether Mack–Petkova's own proof follows exactly this route is **unconfirmed**. Two
things are certain from the abstract: the result is an inequality of Wilson loops, and its content is "Z2 confines ⇒ SU(2) confines".

Consequence for the bare action: the comparison Z2 model has coupling `2β` (SU(2) at `β`, n = 2), the Z2 strong-coupling region is
`e^{2β} − 1` small, and that is the **same range and the same bound** as the repo's direct SU(2) strong-coupling theorem
(`su2_bound_eq`). The bare comparison therefore does not extend what is known; it extends it only for a worst-case coupling
`J̄(ℓ)` measured at a block scale.

## 3. Status of the 4D Z2 lattice gauge theory area law

* **Strong coupling, proved:** Osterwalder–Seiler, Ann. Phys. 110 (1978) 440 (cluster expansion, all gauge groups; recalled); in
  the repo, `wilson_area_law_Z2` (`e^β − 1 ≤ 1/(4 e^{16d+1}(16d+1)^4)`, d = 4, explicit constants, every volume).
* **Weak coupling (large β):** the Z2 theory is in the Coulomb-like/ordered (deconfined, perimeter-law) phase; the 4D theory is
  self-dual (Wegner duality, 4D Z2 gauge theory ↔ 4D Z2 gauge theory; β* = ½ ln(1+√2) ≈ 0.4407), with a first-order transition at the
  self-dual point (numerical; recalled). Proved there: Chatterjee, CMP 377 (2020) 307, arXiv:1811.09770 (Wilson loop to leading
  order at weak coupling, perimeter-type); Cao, CMP 380 (2020); Forsstroem–Lenells–Viklund (finite abelian groups). **Not proved:**
  an area law for all β below the transition, or a sharp transition in 4D (Duncan–Schweinhart's sharpness is for codimension two,
  so 4D 2-form Z2 theory and 3D Z2 gauge theory, not 4D 1-form theory; abstract, c6c).
* **Orland (2019), arXiv:1908.09178:** an area law "for all couplings" is proved for a *modified* Z2 model (link variables in
  [−1,1]), not for the standard ±1 model; the standard case is stated as not rigorously proved (listing).
* So the only rigorous input for **general local positive couplings** is the strong-coupling convergent expansion; the repo has it
  for the single-plaquette Wilson form only. A block-scale effective Z2 action has multi-plaquette terms; the area law for it is a
  separate (open to the repo) cluster-expansion statement.

## 4. Not checked

Mack–Petkova full text (both), Osterwalder–Seiler, Ginibre 1970 (the Lean proof is self-contained and uses the replica
substitution, so it does not depend on the source), Marra–Miracle-Sole-type 3D results, Froehlich–Spencer. No search result used here
quoted a line number or statement beyond the abstracts.
