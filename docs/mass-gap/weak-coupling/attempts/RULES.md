# Rules for the attempt round (2026-11-21)

Shared by the five proof attempts on the open hypothesis `UniformGDS` (see `../PREP.md`, sections "Guiding principle", "Decision rule",
"Lead route"; `../BLUEPRINT-REDUCTION.md`; `../PROOF-NOTE.md`; `../../formal/OneScale/CorollaryB.lean` for the exact Lean statement).

1. **Goal:** a precise lemma towards the hypothesis (proved, or reduced to a sharper statement), or a documented failure with the reason.
   Ideas that come out go into the record either way.
2. **Unit tests, mandatory:** any claimed bound must FAIL for 4D U(1) at weak coupling (massless photon, the photon test) and for 4D Z2
   at weak coupling (gap but no confinement). Check your argument against both explicitly; if it would also prove a reach for them, it
   is wrong.
3. **Honesty:** separate proved / proved with a stated gap / heuristic / conjecture. No claim beyond what is shown.
4. **Built by us:** others' work is reference only (cite ideas; copy no code).
5. **Resources (the owner):** the laptop is busy (GPU production runs, CPU control runs, other agents). Be delicate: no heavy simulations
   to re-verify established numbers with established mechanisms; small numerical experiments only when they test something new, CPU only,
   at most 2 processes, `CUDA_VISIBLE_DEVICES=-1`, a few minutes each. Lean builds only in your own WSL folder, one build at a time.
   Do not touch the GPU, the GPU queue, `lattice/runs-gpu/`, or other agents' folders.
6. **Files:** write only in your own folder `attempts/<route>/` (a note `NOTE.md`, plus scripts if any) and, for Lean, new files under
   `../../formal/Attempts/<Route>/` built in your own WSL folder. No German umlauts (transliterate names). Do not commit or push.
7. **Report:** what you tried, what holds (with statements), what fails and why, the photon/Z2 check, and the single most promising next
   step.

## Round 2 additions (2026-11-21)

- **Unit tests, refined after round 1:** the photon test is unchanged (no claim may give U(1) at weak coupling a gap or a reach). The Z₂
  test applies to **confinement-type** claims (area law, boundary-uniform GDS): they must fail for weak-coupling Z₂. A **gap-only** claim
  (torus decay, a uniform ratio bound) must instead *hold* for weak-coupling Z₂, which has a gap, and must not imply an area law for it.
- **Read first:** `ROUND-1.md`, `../H1-OPENAI.md`, `../H2-CURVATURE.md`, `../followups/PREREG-FOLLOWUPS.md` (Result section), and
  `../PREP.md` (the effective-theory split H1/H2 and the owner's readings). The Lean reduction now runs through
  `OneScale.Effective.gap_of_effective_W` (H1 `EffectiveConvergence` + H2 `LimitGDS_W`).
- **Numerics:** tests of something new only, pre-registered in your folder before running, CPU only, one process, at most 15 minutes per
  run. The GPU runs Leg B overnight; its data will be fed in when available.
