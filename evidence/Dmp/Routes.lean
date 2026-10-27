/-
T3b (no lockout), C18 (whatever spoke to CMOS keeps a route) and C25 (a deployment that would remove the last route is refused): the
missing theorem their Coverage lines name, in the smallest model that has a route. A half holds, per action, the routes by which it reaches that
action's channel; an act that removes a route (a tightening, a retire, a deployment) is refused when it would remove the last one; so after
any single act every half keeps at least one route to every action it had a route to. The ratchet of C25 (the list of known gaps only
shrinks) is the same statement over the set of actions without a route.
-/
namespace Dmp

/-- The routes a half holds: per action, the routes by which it reaches the action's channel (a command line, a console, a client). -/
structure Reach where
  routes : Nat → List Nat

/-- A half has a route to an action. -/
def Reach.hasRoute (r : Reach) (action : Nat) : Prop := r.routes action ≠ []

/-- An act that removes one route: refused (`none`) when it would remove the last route for the action; otherwise the reach without it. -/
def Reach.removeRoute (r : Reach) (action route : Nat) : Option Reach :=
  if (r.routes action).erase route = [] then none
  else some { routes := fun a => if a = action then (r.routes action).erase route else r.routes a }

/-- No single act removes a half's last route: whenever the act goes through, every action keeps a route it had. -/
theorem after_single_act_route_remains (r r' : Reach) (action route : Nat) (h : r.removeRoute action route = some r') :
    ∀ a, r.hasRoute a → r'.hasRoute a := by
  intro a ha
  unfold Reach.removeRoute at h
  split at h
  · cases h
  · rename_i hleft
    simp only [Option.some.injEq] at h
    subst h
    unfold Reach.hasRoute
    by_cases hc : a = action
    · subst hc; simp [hleft]
    · simp [hc]; exact ha

/-- The act that would remove the last route is refused before it runs (C25). -/
theorem last_route_removal_refused (r : Reach) (action route : Nat) (h : (r.routes action).erase route = []) :
    r.removeRoute action route = none := by
  simp [Reach.removeRoute, h]

/-- The known gaps (the actions without a route) only shrink: an act that goes through adds no gap. -/
theorem gaps_only_shrink (r r' : Reach) (action route : Nat) (h : r.removeRoute action route = some r') :
    ∀ a, ¬ r'.hasRoute a → ¬ r.hasRoute a :=
  fun a hn ha => hn (after_single_act_route_remains r r' action route h a ha)

end Dmp
