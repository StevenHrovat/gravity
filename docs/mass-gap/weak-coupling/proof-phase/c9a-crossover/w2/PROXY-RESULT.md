# Single-link proxy for the two-level bad-set classification on the W2 snapshots (diagnostic), 2026-11-23

**Status: DIAGNOSTIC.** Not part of the pre-registered W2 verdict, and not a bound on any stated hypothesis (`RESULT.md`, table of
measured quantities). Method: `lever_proxy.py` (module docstring); data: the chain-A snapshots of the narrow run (samples of
`K(Y, ·)` at the unperturbed outside), 1088 configurations (8 pairs per start per box, at `T/2` and at the end; 34 boxes), with
their outside and block field. CPU: 6 processes, 1565-1837 s each, **2.9 CPU-hours** in total. Output:
`runs/narrow/proxy_launch_*.json`.

## Result

| | β = 2.3 | β = 3.5 |
|---|---|---|
| `κ̃_b` per block (outside influence per box link, single-link, Pinsker): median [5 %, 95 %], minimum | 5.85 [5.48, 6.46], 4.93 | 5.70 [5.42, 6.93], 5.05 |
| `D_b` per block (Dobrushin column sum inside the block): median, minimum | 10.1, 7.5 | 9.7, 7.8 |
| two-block cubes: `κ̃` median, `D` median | 3.0, 21.5 | 3.0, 19.4 |
| fraction of blocks with `κ̃_b ≥ 0.5` (also `≥ 1`, `≥ 2`) | 1.000 | 1.000 |
| fine-plaquette roughness (max of `1 − ½ tr` per block): median; fraction above 1.0 | 1.49; 0.99 | 0.96; 0.45 |
| block-plaquette roughness from `Y`: median; fraction above 1.0 | 1.12; 0.59 | 0.56; 0.21 |
| correlation per block of `κ̃_b` with the fine roughness | 0.41 | 0.71 |

Per class (block means of `κ̃_b`; fine roughness): β = 3.5: sampled 5.62 (0.90), A1 6.33 (1.35), A2 6.85 (1.52), A3 5.90 (1.09),
A4 5.63 (0.91), A6 5.68 (0.95); β = 2.3 similar, smaller spread.

## Reading

1. **The single-link proxy saturates at both couplings.** Every block of every snapshot has single-link column sums far above 1,
   so a classification "fails to contract" by this proxy marks everything bad. This is the known failure of single-site
   Dobrushin conditions for SU(2) above β ≈ 0.25 (c8b), now seen at the actual configurations, with the block field fixed: the soft
   constraint at κ = 16 does not bring single-link influences down enough. **The lever of `INFLUENCE-BAD.md` cannot be evaluated
   with a single-link quantity; it needs the box influence** (the full local computation on the 272-box subsample, which needs a
   separate OK; about 70 CPU-hours, `PROJECTION.md` 7).
2. **What the proxy does carry is a ranking**, which follows the field roughness (correlation 0.41 at β = 2.3, 0.71 at β = 3.5):
   rough blocks have larger single-link influences. This is the field-size classification again, not a new one.
3. **Field-size badness by fine plaquettes is not rare at these couplings:** at β = 2.3, 99 % of the blocks have a fine plaquette
   with `1 − ½ tr > 1`, at β = 3.5, 45 %. Block plaquettes from the noisy block field (κ = 16) are rough too (59 %, 21 %). So the
   field-size classification of `WL.md` 5 at threshold `t = 1` makes almost everything bad at β = 2.3: rarity in M1's sense is absent
   there, as `WL.md` 10 anticipated for the middle of the crossover.
4. A side observation: the flat block field A1 makes the fine field rougher (fine roughness 1.35 against 0.90 for sampled `Y` at
   β = 3.5), because the constraint pulls the fine links towards the identity against the equilibrium outside.
