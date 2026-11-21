/-
Reflection positivity of the Wilson lattice gauge measure (positivity project, 2026-11-21). Released under Apache 2.0.

Reflection positivity of the Wilson action is due to Osterwalder and Seiler (Ann. Phys. 110 (1978) 440); see also
Glimm–Jaffe, *Quantum Physics*, ch. 6 and 10. This library is an independent formalisation in the framework of
`AreaLaw` (lattice, connections, product Haar measure, `xp`, `LinkDep`). No code is taken from other projects.

- `Positivity.Abstract`: the abstract lemma on `X × C × X` (real, complex, Cauchy–Schwarz), and Gram positivity and
  Cauchy–Schwarz for any positive symmetric reflected form.
- `Positivity.Product`: reflection positivity for product measures over a finite index set split as
  fixed ⊕ positive ⊕ mirror(positive).
- `Positivity.Reflection`, `Positivity.Wilson`, `Positivity.Concrete`: the site reflection `t ↦ −t` of (ℤ/Nℤ)^d,
  `N` even; the Wilson measure is reflection positive for every real `β` (`wilson_rp`, `wilson_rp_normalized`,
  `wilson_rp_symm`, `wilson_rp_cs`, `wilson_rp_gram`); Haar measure on a compact group is inversion invariant;
  SU(2) and U(n) (`wilson_rp_SU2`, `wilson_rp_Un`, `wilson_rp_gram_SU2`, `wilson_rp_gram_Un`).
- `Positivity.General`, `Positivity.Admissible`: site reflection for any plaquette weight `∏_p φ(Re tr U_p)` with `φ ≥ 0` measurable (`rp_plaquette_weight`, `rp_plaquette_weight_gram`; `wilson_rp_of_general` recovers `wilson_rp`), link reflection for exponential crossing plaquettes with arbitrary other plaquettes (`rp_plaquette_weight_link`), and the admissible Wilson measure `exp(β Re tr U_p) 1[n - Re tr U_p <= ε]` (`admissible_rp`, `admissible_rp_SU2`, `admissible_rp_Un`, `admissible_rp_SUn`).
- `Positivity.Kernel`, `Positivity.LinkReflection`, `Positivity.LinkWilson`: the link reflection `t ↦ −1 − t`; the
  kernel `exp (β ∑ gⱼ(a) gⱼ(b))` is positive definite; splitting the crossing links preserves the product Haar measure;
  the Wilson measure is reflection positive for `β ≥ 0` (`wilson_rp_link`, `wilson_rp_link_SU2`, `wilson_rp_link_Un`).
-/

import Positivity.Abstract
import Positivity.Product
import Positivity.Reflection
import Positivity.Wilson
import Positivity.Concrete
import Positivity.Kernel
import Positivity.LinkReflection
import Positivity.LinkWilson
import Positivity.General
import Positivity.Admissible
