/-
The form layer as one API: the G0 link, charge quantisation discharged (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/API.md` (section "What the G0 link gives every instance"), `docs/unified/GU-SCOPING.md` section 8.
-/

import ProofPhase.API
import ProofPhase.General.GUCharge

/-!
# The G0 link: every label on the phase field has an integer charge

The core API (`API.lean`) names the statement `ChargeQuantisation` (every continuous character of `Circle` is `z ↦ z ^ n`)
and takes it as an `External` hypothesis. The proof is the GU round's `circle_char` (`General/GUCharge.lean`, from
Parseval on `AddCircle`; classical). This file discharges the hypothesis, so that an instance can use quantisation
with no hypothesis at all. Nothing is duplicated here.

For extraction into a standalone package, the part of `GUCharge.lean` that proves `circle_char` needs Mathlib only (its
import of `General/GUCentre` serves the later items 3 and 4); that part is what moves into the core (`docs/unified/API.md`).
-/

namespace ProofPhase.API

/-- **Charge quantisation, proved**: `ChargeQuantisation` from the GU round's `circle_char`. -/
theorem chargeQuantisation : ChargeQuantisation := fun χ hc => ProofPhase.General.GU.circle_char χ hc

/-- **Every label on the phase field has an integer charge**, with no hypothesis. -/
theorem PhaseLabel.integer_charge (L : PhaseLabel) : ∃ n : ℤ, ∀ z, L.χ z = z ^ n :=
  L.charge chargeQuantisation

end ProofPhase.API
