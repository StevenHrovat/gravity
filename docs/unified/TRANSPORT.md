# Transport of an uncertainty across a DB: the final approach as one theorem

2026-11-23. Lean: `docs/mass-gap/formal/ProofPhase/Unified/Transport.lean` (the theorem),
`TransportBridges.lean` (the three bridges), `TransportInstances.lean` (a model where everything is proved); 68
declarations, standard axioms only, no `sorry` (`axioms-transport.sh`, `axioms-transport.log`). CPU check, refute-only:
`transport_check.py`, `transport_check.log` (0 failures).

The approach is the owner's: "Exactly define the uncertainty, then transport it in a meaningful way across a DB."
(`mass-gap/weak-coupling/PREP.md`, last entry; paper outline, Part VI.)

**Status marks.** **[Lean]** proved in Lean, standard axioms only; **[classical]** known mathematics, recalled;
**[external]** proved by others, imported as a named hypothesis; **[numerical]** measured, not proved; **[reading]**
interpretation, including every DMP identification; **[open]** not proved by anyone. Nothing marked [open] is used as
proved: each open step enters the Lean as a named hypothesis or as a hypothesis of a theorem.

---

## 1. In plain words

**The theorem.** Each column carries something across a chain of boundaries (slabs, scales, the two halves of a gadget).
On top of what is carried sits an uncertainty: how far our certified picture may be from the real object. Treat that
uncertainty as one more carried amount. At every step it is multiplied by the step's factor, exactly like the ledger,
and the step may add some fresh uncertainty of its own. Three things then follow:
- **(a) If the steps contract** (the factor stays below 1 after the floor), the uncertainty stays bounded forever: at
  most its start plus the fresh uncertainty per step divided by (1 - factor).
- **(b) If a step costs exactly the floor**, nothing is damped: the uncertainty is the start plus the sum of everything
  added. That bound is attained, so it cannot be improved. It stays bounded exactly when the added amounts are summable;
  a constant fresh uncertainty grows without limit.
- **(c) If the uncertainty stays below a sign margin**, the sign is certified on the other side of the boundary, at
  every step.

With no fresh uncertainty this is the existing ledger (`Pays`, `carry`, `Ledger.contract`); the Lean says so.

**One more exact fact, which is the precise meaning of "zero slack".** When the uncertainty and the margin it is
compared with are carried by the same factor, their ratio is carried at exactly cost = floor. Damping relative to a
margin exists only if the margin shrinks more slowly than the uncertainty.

**The three bridges in this form.**
- **Yang-Mills.** The uncertainty is the boundary uncertainty of a slab: how much the charged (twisted) sector can be,
  relative to the neutral one, at any outside. O1 asks it to be below 1/mu. In the slab geometry the slab chain carries
  it with each layer's own factor and adds nothing (Lean). In a box, the side seam adds a fresh amount per join (named,
  open). The electric-side deficit sets the factor. A positive deficit, as long as the twist ratio is positive, only
  costs more layers (Lean). The real open step: the ratio must stay bounded below at fixed physical length as the
  lattice spacing goes to zero.
- **GRH.** The uncertainty is how far zeta's margin (Szego prediction error at scale n) is from the finite model's, as
  a fraction of the model's margin. The explicit formula's remainder enters each scale as the relative difference of the
  two Szego factors 1 - |k|^2. In log form the uncertainty is carried at exactly cost = floor: zero slack, no damping,
  ever (Lean). So zeta's margin is certified, with size, while the summed remainders stay below log 2 (Lean). The sign
  alone is decided per step (Lean). The size of the remainder, from the primes alone, is open beyond Dirichlet.
- **NP.** The uncertainty is the hidden information per variable: Alice's pointer, log m bits. Each hidden variable a
  refutation must resolve takes a fixed fraction of the line count across the two-party split. That is a ledger with no
  fresh uncertainty, and it is exactly a size bound (Lean). Lifting gives the cost c log n per variable (external, named).
  A constant-size quantum needs a constant cost c > 0 per variable, uniform in n: `LiftCPConst` (open). Hiding errors
  per block add up with no damping (critical case).

**What each open step needs, in one line each.**
- Yang-Mills: a cost above the floor at fixed physical length, uniform in the cutoff; in a box, a seam cost per join
  below the margin left by the contraction.
- GRH: remainders, measured against a margin that collapses, that are summable with total below log 2; nothing in the
  chain damps them.
- NP: a constant cost per hidden variable for a constant-size gadget; with known proofs, the per-block hiding errors
  add up across all n blocks without damping [reading].

---

## 2. The theorem (`Transport.lean`) [Lean]

**Definitions.**
- `TransportsCert Cert a r n`: step `i < n` carries every certified value `e` to `a i * e + r i` (certificate form).
- `Transports e f r δ n`: `e (i + 1) <= e^δ * f i * e i + r i` for `i < n` (real-sequence form, like `Pays`).
- `acc a r e₀ n`: the transported value (`acc 0 = e₀`, `acc (n + 1) = a n * acc n + r n`).
- `critAcc e₀ r n = e₀ + Σ_{j<n} r j`: the critical chain.

**Closed form.**
- `transport_cert`, `transport`: the uncertainty is at most the transported value.
- `acc_eq`: `acc n = (∏_{i<n} a i) e₀ + Σ_{j<n} (∏_{j<i<n} a i) r j` (variation of constants).
- `acc_const`: constant factor `q`: `q^n e₀ + Σ_{j<n} q^{n-1-j} r j`.

**The ledger is the case `r = 0`.**

| Lean | says |
|---|---|
| `transportsCert_zero_iff` | `TransportsCert Cert a 0 n <-> Carries Cert a n` |
| `carry_of_transport` | `carry` from the transport theorem |
| `pays_iff_transports` | `Pays M c δ n <-> Transports M (e^{-c}) 0 δ n` |
| `ETM.Ledger.transports` | every DMP ledger (`ETM/RunSys.lean`) is a transport with `r = 0` |
| `contract_of_transport` | `Ledger.contract` from (a) |

**(a) Bounded transport.**
- `transport_geom`: factors in `[0, θ]`, `q = e^δ θ`: `e n <= q^n e 0 + Σ_{j<n} q^{n-1-j} r j`.
- `bounded_transport`: with `q < 1` and `0 <= r <= R`: `e n <= q^n e 0 + R/(1 - q) <= e 0 + R/(1 - q)` for every
  `n`. The constant is explicit.
- `geom_tail_le`, `geom_tail_le_sum`: the tail is at most `R/(1 - q)`; for `q <= 1` at most the plain sum.

**(b) The critical case.**
- `critical_transport`: `e^δ f i = 1` gives `e n <= e 0 + Σ_{j<n} r j`. No sign condition is needed.
- `critical_sharp`: the critical chain `e₀ + Σ r` is a transport with factor `e^{-δ}` (so `e^δ f = 1`) and attains
  the bound with equality at every step.
- `critical_bounded_iff`: for `r >= 0`, the critical chain is bounded exactly when `r` is summable.
- `critical_unbounded`: a constant `ρ > 0` exceeds every bound. Under contraction the same `ρ` stays below
  `ρ/(1 - q)` (a).

**(c) Sign preservation.**
- `sign_transport`: `m n <= M n`, `|N n - M n| <= e n < m n` give `N n >= m n - e n > 0`.
- `sign_of_bounded`: (a) + (c), a uniform margin `μ > e 0 + R/(1 - q)` certifies the sign at every step.
- `sign_of_critical`: (b) + (c), `e 0 + Σ_{j<n} r j < m n` certifies the sign at step `n`.

**Zero slack, exactly.**
- `relative_transport`: if `e (i + 1) <= s i e i + r i` and `E (i + 1) = s i E i` with `E > 0`, then `e/E` is a
  transport with floor 0 and factor 1 (cost = floor), fresh uncertainty `r i / E (i + 1)`.
- `relative_critical`: `e n / E n <= e 0 / E 0 + Σ_{j<n} r j / E (j + 1)`.

---

## 3. The three bridges in transport form (`TransportBridges.lean`)

Each bridge has four parts: the uncertainty (defined exactly), the DB it crosses, the factors and fresh uncertainty, and
the margin.

### 3.1 Yang-Mills: the boundary uncertainty through the slab chain

**The uncertainty** [Lean, definitions].
- `twistCert Ω K u`: at every end-face outside, `|Z_{e=1}| <= u Z_{e=0}` for the slab kernel `K`. The least such `u`
  is the boundary-uniform electric factor. It measures how much the box's twist sector can depend on the outside:
  the boundary uncertainty.
- `elecDeficit c = (√2 - 1) - c`: the electric-side deficit of a slab with pointwise twist ratio `c`, how far the ratio
  is below the self-dual point. The first slab's uncertainty is `u₀ = elec(c)` (`sector_of_twist`).

**The DB.** The shared end face where two slabs are joined.

**Factors and fresh uncertainty.**
- Slab geometry, `ym_slab_transport` [Lean, from `elec_submul`]: joining layer `i + 1` multiplies the uncertainty by the
  layer's own factor `ρ i` and adds **nothing** (`r = 0`, zero join loss).
- Box geometry, `SeamTransport Ω T ρ σ` [named, **open**]: the same with a fresh `σ i` per join, the cost of the seam of
  the twist sheet along the side outside. `seamTransport_slab` [Lean]: it holds with `σ = 0` in the slab geometry.

**The margin.** `ym_O1_of_cert` [Lean]: `μ u <= 1` is O1 in sector form, `μ |Z_{e=1}| <= Z_{e=0}` at every outside.

**The bridge.** `ym_bridge` [Lean, from `SeamTransport`]: nonnegative layers, first uncertainty `u₀`, factor `θ < 1`,
seam `σ`: O1 at `μ` after `n` joins once `μ (θ^n u₀ + σ/(1 - θ)) <= 1`.

**The deficit.**
- `elec_le_of_deficit` [Lean]: deficit `<= 0` puts the factor at or below `√2 - 1`, the input of `three_slabs_O1`
  (three slabs, every `μ <= 14`).
- `ym_layers_needed` [Lean]: any ratio `c` in `(0, 1]` for every layer, slab geometry: for every `μ` there is `N` with
  O1 after more than `N` layers. On a fixed lattice a positive deficit only costs layers.

**What is open, in these terms.**
1. **The cost above the floor, uniform in the cutoff.** `N` layers have a fixed physical length only if `c` is bounded
   below uniformly in the lattice spacing at a fixed physical layer length. The single-layer floor gives
   `c >= e^{-2 βN}` (`kchain_tanh`), which tends to 0 in the continuum. For the three-hand-over form of O1 the
   requirement is deficit `<= 0` at the hand-over slab, uniformly over end-face outsides. **[open]**
2. **The side seam** (box geometry). For three slabs at the self-dual factor (`θ = u₀ = √2 - 1`, two joins) the exact
   transported value is `θ^3 + (1 + θ) σ` (`acc_const`). O1 at `μ` then needs a seam cost per join of at most
   `(1/μ - θ^3)/√2`: about `0.185` at `μ = 3`, `0.051` at `μ = 7`, `2.6e-4` at `μ = 14` [arithmetic]. With many
   layers the requirement relaxes toward `σ < (1 - θ)/μ`, at the price of length. **[open]**
3. Whether the tube chain accepts slabs in place of boxes is the step-1 question of `JOIN-LOSS.md` section 5. **[open]**

### 3.2 GRH: the explicit formula's remainder along the scale steps

**The setting** [classical]. On a grid of cells, Weil's form is a Toeplitz matrix in the grid moments. Its sections grow
one scale at a time. The margin of the section at scale `n` is the Szego prediction error `E n`, and
`E (n + 1) = (1 - |k n|^2) E n` with the reflection coefficient `k n` (Szego recursion, Levinson;
`rh-guide/grh/INDUCTION.md`). Zeta's moments give `E` with factors `s n`. The finite model of the ledger
(`grh_instance`, `ZeroModel`) gives `Ê` with factors `ŝ n = 1 - |k̂ n|^2`. The explicit formula identifies zeta's
prime-side moments with Weil's zero pairing ("toy = not-toy").

**The uncertainty** [Lean, definitions].
- `relUnc E Ê n = |E n - Ê n| / Ê n`: how far zeta's margin is from the model's, as a fraction of the model's.
- `relRem s ŝ n = |s n - ŝ n| / ŝ n`: the explicit formula's remainder as it enters scale `n`, the relative difference
  of the two Szego factors.

**The DB.** The scale step: the new corner entry of the Toeplitz section, where toy and not-toy are compared.

**Factors and fresh uncertainty.**
- `grh_abs_step` [Lean]: `|E - Ê|` is carried with the model's factor `ŝ n = 1 - |k̂ n|^2` (floor 0) and gets the fresh
  uncertainty `|s n - ŝ n| |E n|`.
- `grh_rel_step` [Lean]: `1 + relUnc (n + 1) <= (1 + relRem n)(1 + relUnc n)`.
- `grh_log_transport` [Lean]: `log (1 + relUnc)` is a transport with floor 0 and **factor exactly 1**: cost = floor,
  zero slack. The fresh uncertainty is `log (1 + relRem n)`. By (b) nothing is damped and the bound is sharp in the
  model (`critical_sharp`).

**The margin.** Zeta's margin is positive when the uncertainty is below the model's margin, `relUnc < 1`.

**The bridge.**
- `grh_sign` [Lean]: if `log (1 + relUnc 0) + Σ_{j<n} log (1 + relRem j) < log 2`, then `E n > 0`, `relUnc n < 1`,
  and `E n >= (1 - relUnc n) Ê n`.
- `grh_sign_of_sum` [Lean]: from equal start, `Σ_{j<n} relRem j < log 2` suffices.
- `grh_sign_szego` [Lean]: the same with the model's factors written as `szego (k̂ n)`, `‖k̂ n‖ < 1` (`Encoder.lean`).
- `grh_sign_step` [Lean]: **the sign alone is decided step by step.** `relRem n < 1` keeps zeta's factor positive.
  What the transport adds is the size of the margin, and there the remainders add up with no damping.

**Proved, classical, external, open.**

| part | status |
|---|---|
| the transport law, zero slack, the sign and size certificates above | [Lean] |
| the finite model's sign (`grh_instance`); its margins vanish past the number of its zeros, so a model certifies only up to its size and the bridge needs a growing family of models | [Lean] |
| Szego recursion, `E (n+1) = (1 - k^2) E n`; a remainder `δt` in the corner moment shifts `k n` by `δt / E (n-1)` | [classical], not formalised |
| the explicit formula on the ledger's test class ("toy = not-toy") | [classical], not in Mathlib |
| RH for zeta and GRH for Dirichlet L-functions | [external] (`ExtRH`, `ExtDirichletGRH`, audit list in `GRH-TIE-IN.md` 2.3) |
| the margin collapses (`λ_min` about `1e-11`), and the prime weights must be exact to about the margin | [numerical] (`INDUCTION.md`) |
| a bound on `relRem` from the primes alone; GRH beyond Dirichlet | **[open]** |

**What is open, in these terms.** The remainder is measured against a margin that collapses, so a fixed absolute
remainder becomes an ever larger relative one. The chain has zero slack, so no step damps it. For the margin to be
certified with size, the relative remainders must be summable with total below `log 2`. For the sign alone, each must
stay below 1. That is the precise reason the sign is hard: the remainder must shrink faster than the margin
collapses, and nothing in the chain helps. For zeta and Dirichlet L-functions the sign itself comes from the external
proofs, so the transport is not needed there. The open uses are GRH beyond Dirichlet and the independent route from the
prime side.

### 3.3 NP: the hidden information across the two-party split

**The uncertainty** [Lean, definitions].
- `hiddenQuantum G = (pointer bits of G) · log 2`: the hidden information per variable in nats. For the Index gadget it
  is `log m`, `m` the size of Bob's table (`indGadget_quantum`).

**The DB.** The two-party split: Alice's pointer on one side, Bob's table on the other. A refutation crosses it once for
each hidden variable it must resolve, `w + 1` of them for a formula of resolution width above `w`.

**Factors and fresh uncertainty.**
- `HiddenTransport R q W` [Lean, definition]: every refutation's line count is carried across `W` hidden variables. Each
  crossing keeps at most the share `e^{-q}` (`Pays` with cost `q`, floor 0, no fresh uncertainty), and one line is left
  at the end.
- `hiddenTransport_iff_size` [Lean]: this is exactly the size bound `e^{W q} <= |P|`.

**The bridge.**
- `liftCP_hiddenTransport` [Lean, from the named **external** `LiftCP`]: `q = c log n` per hidden variable,
  `W = w + 1`. For Index with `m` about `n^δ`, `c log n` is about `(c/δ) log m`: each crossing costs a fixed fraction
  of the variable's hidden information [arithmetic; reading].
- `liftCPConst_hiddenTransport` [Lean, from the named **open** `LiftCPConst`]: `q = c`, free of `n`.
- `costAboveFloor_const_iff` [Lean]: a constant cost per variable is a cost above the floor exactly when `c > 0`.
- `hiding_accumulates` [Lean]: per-block hiding errors `ε`, carried with factor 1 across `n` blocks, total exactly `n ε`
  (critical case) and exceed every margin.

**What is open, in these terms.**
1. **`LiftCPConst`.** A fixed gadget, so a constant quantum, with a constant positive cost per hidden variable, uniform
   in `n`. Open for every constant-size gadget (`NP-LIFTING.md` 1.5, 2.3). **[open]**
2. **Why known proofs need a growing gadget** [reading, recalled; to be checked against the sources before the paper
   says it]. The lifting proofs pay a per-block error (how far a block is from hiding perfectly) and add it over all `n`
   blocks, a union bound. In transport terms that is the critical case: no damping between blocks, so the total `n ε`
   must stay below a constant margin. That forces `ε < margin/n`, hence a gadget growing with `n`
   (`m = n^{1+eps}` in Mertz-Pitassi). A constant quantum needs a mechanism that damps the per-block errors across
   blocks (a factor below 1 between blocks) instead of adding them.
3. Hiding alone is not the cost: XOR hides perfectly and lifts badly (`NP-LIFTING.md` section 5). In these terms,
   hiding controls the fresh uncertainty; the factor per crossing must be shown positive on its own. [reading]
4. `WidthToCP` for all CNFs is false (pigeonhole, classical), so any gadget-free version must restrict the class.

---

## 4. The theorem is not empty (`TransportInstances.lean`) [Lean]

**A model where everything is proved: a perturbed two-state Markov chain.**
- The chain with flip rates `α, β` acts on the law `p = P(state 1)` by `step2 α β p = (1 - p) α + p (1 - β)`. A
  perturbed chain uses `α' n, β' n`.
- The **uncertainty** is `|q n - p n|`, the **fresh uncertainty** is `|α' n - α| + |β' n - β|`, the **factor** is
  Doeblin's `|1 - α - β|`.
- `doeblin_step`, `doeblin_transports`: the distance is a `Transports` with floor 0.
- **(a) and (c):** `doeblin_example`. Rates `1/4, 1/4` (factor `1/2`), perturbations of total size at most `1/10` per
  step, both chains started at `1/2`. Then for every `n`, `3/10 <= q n <= 7/10`. The uncertainty stays below
  `(1/10)/(1 - 1/2) = 1/5`, below the margin `1/2` of each state, so both states keep positive probability at every
  step.
- **The critical case:** `ident_chain`, `ident_margin_lost`, `ident_is_critical`. With no mixing (`α = β = 0`, factor
  1, cost = floor) and the perturbation `α' = ρ`, `P(state 0) = (1/2)(1 - ρ)^n`, which falls below every `ε > 0`. A
  perturbation of the same size that Doeblin mixing absorbs erases the whole margin here.
- **(b) is sharp:** `critical_sharp` (in `Transport.lean`): the chain `e₀ + Σ r` is a critical transport attaining the
  bound at every step.
- **Yang-Mills slab with the single-layer floor:** `ym_slab_transport` with `kchain_tanh`'s hypothesis is a proved
  instance with `r = 0`. Its factor `tanh(βN)` is below 1 at every coupling, so (a) and (c) apply on every finite slab
  chain (`ym_layers_needed`).

**CPU check** (`transport_check.py`, refute-only, 0 failures) [numerical]:
- (a) on 2000 random chains: worst ratio of the uncertainty to the bound 0.998;
- (b) attained exactly;
- the GRH relative step on 200000 random instances, any real `s`;
- the GRH sign under the `log 2` budget on 2000 random scale chains;
- the Doeblin example under adversarial perturbations: the law stayed in `[0.383, 0.622]`, inside the Lean bound
  `[0.3, 0.7]`;
- the identity chain at `ρ = 0.1`: `P(state 0) = 3.5e-10` after 200 steps.

---

## 5. Status table

| | uncertainty (defined exactly) | DB | factor / fresh | margin | proved | classical / external | open |
|---|---|---|---|---|---|---|---|
| **Yang-Mills** | boundary uncertainty `twistCert`; deficit `elecDeficit` | shared end face of two slabs | layer factor `elec(c)`; fresh: 0 (slab), seam `σ` (box) | `1/μ` (O1 sector form) | transport, zero join loss, `ym_bridge`, `ym_layers_needed` [Lean] | Birkhoff-Hopf at strong coupling; centre symmetry of the slab [classical] | `c` uniform in the cutoff at fixed length; side seam; slabs in the tube chain |
| **GRH** | `relUnc` (zeta's margin vs the model's) | scale step (corner of the section) | Szego `1 - abs(k)^2`; relative/log: factor 1 (zero slack); fresh `relRem` | `relUnc < 1` | zero-slack transport, `grh_sign`, per-step sign [Lean]; finite model [Lean] | Szego recursion, explicit formula [classical]; RH, Dirichlet GRH [external] | bound on `relRem` from the primes; GRH beyond Dirichlet |
| **NP** | `hiddenQuantum` (log m bits per variable) | two-party split | `e^{-q}` per hidden variable; fresh 0; hiding errors add at cost = floor | one line left | `HiddenTransport` = size bound; ties to `LiftCP`, `LiftCPConst` [Lean] | `LiftCP` (GGKS) [external] | `LiftCPConst` for a constant gadget |

---

## 6. DMP identifications [reading]

- **The DB** is the boundary each step crosses: the shared slab face (Yang-Mills), the new scale of the section (GRH),
  the two-party split (NP). It is the encoder's boundary (`ENCODER.md`).
- **The uncertainty** is the error bar of existence: it sits on the bridge to the real object, never on the finite
  model, which asserts only itself (PREP, "The toy only asserts its own DMP-complete existence").
- **Transport** is the ledger law with one fresh term. With `r = 0` it is DMP's terminal ledger (`ETM.md` 3); every DMP
  ledger is a transport (`ETM.Ledger.transports`).
- **Zero slack** is cost = floor (`relative_transport`): the margin and the uncertainty pay the same cost, so nothing is
  left over to damp the uncertainty.
- **The three columns:** Yang-Mills is the contracting case with a possible fresh term (the seam). GRH is the critical
  case. NP is the size reading of the contracting case, with fresh errors in the known proofs that add up critically.

---

## 7. What this does not do

- It does not prove O1, the GRH sign beyond Dirichlet, or a crossing cost for strong proof systems. Each enters as a
  named hypothesis (`SeamTransport`, a bound on `relRem`, `LiftCP`, `LiftCPConst`) or as a hypothesis of a theorem
  (the ratio `c` uniform in the cutoff).
- The GRH bridge is stated on the margins and their Szego factors. Their link to the moment remainder (Levinson's
  recursion, the explicit formula) is classical and not formalised.
- The NP reading of the known lifting proofs (union bound over blocks) is recalled, not re-read in this round.

## 8. Files

- `docs/mass-gap/formal/ProofPhase/Unified/Transport.lean`: the theorem, sections 1 to 6.
- `docs/mass-gap/formal/ProofPhase/Unified/TransportBridges.lean`: the three bridges.
- `docs/mass-gap/formal/ProofPhase/Unified/TransportInstances.lean`: the perturbed Markov chain, the critical chain.
- `docs/unified/axioms-transport.sh`, `axioms-transport.log`: 68 declarations, `[propext, Classical.choice,
  Quot.sound]`, no `sorry`/`admit`/`native_decide`/`axiom`.
- `docs/unified/transport_check.py`, `transport_check.log`: refute-only CPU check.
