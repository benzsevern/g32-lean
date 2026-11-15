import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers
import Mathlib.GroupTheory.OrderOfElement

/-! # Actual complex automorphisms with the specified exact deck period -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A periodic complex deck morphism with no shorter identity return gives an
actual complex automorphism of exactly that order. -/
theorem s2e_c1_periodic_complex_aut
    (X : Over (Spec ↧ℂ)) (d : X ⟶ X) (m : ℕ) (hm : 0 < m)
    (hpow : End.of d ^ m = 1)
    (hfaith : ∀ n, n < m → End.of d ^ n = 1 → n = 0) :
    ∃ u : Aut X, u.asIso.hom = d ∧ orderOf u = m := by
  haveI : IsIso d := (isUnit_iff_isIso _).mp
    (IsUnit.of_pow_eq_one hpow (Nat.ne_of_gt hm))
  let u : Aut X := Aut.of (asIso d)
  refine ⟨u, rfl, ?_⟩
  let F : Aut X →* End X := {
    toFun := fun v => End.of v.asIso.hom
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hF : Function.Injective F := by
    intro a b hab
    apply Aut.ext
    apply Iso.ext
    exact congrArg End.asHom hab
  apply (orderOf_eq_iff hm).mpr
  constructor
  · apply hF
    rw [map_pow, map_one]
    exact hpow
  · intro n hn hnpos hret
    have he := congrArg F hret
    simp only [map_pow, map_one] at he
    exact (Nat.ne_of_gt hnpos) (hfaith n hn he)

end HodgeLean.Foundations.Program
