/-
Break model for the no-lockout clause (T3b, C18, C25; part 2 of the verifying session). The axioms as modelled hold (T24 as `Standing.update`:
one witness tightens), and the clause fails: a half's reach to an action, read as a standing level that counts its routes, is lowered from
one to zero by one witness, and nothing in K1 to K3 or T24 refuses it, because the modelled axioms have no route. Routes.lean states and
proves the theorem the clause needs in a model that has one.
-/
import Dmp.Standing
import Dmp.Routes

namespace Dmp

/-- One witness lowers the route count from one to zero: a tightening, allowed by T24 as modelled. The last route is gone. -/
theorem lockout_breaks_in_the_modelled_axioms : update 1 0 true false = 0 := by decide

/-- With routes modelled, the same act is refused: the last route stays. -/
def oneRoute : Reach := ⟨fun _ => [1]⟩

theorem lockout_refused_with_routes : oneRoute.removeRoute 0 1 = none := by decide

end Dmp
