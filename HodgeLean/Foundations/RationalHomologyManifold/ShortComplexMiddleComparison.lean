import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Actual short-complex homology comparison from the middle component.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual short-complex maps with the same middle component induce the same map on homology.
Source: Weibel, An Introduction to Homological Algebra, section 1.2; homology on actual cycles modulo boundaries.
HC no distance; AV milestone no distance.
-/
theorem shortComplex_homologyMap_eq_of_middle {C : Type*} [Category* C] [Abelian C]
    {S T : ShortComplex C} (f g : S ⟶ T) (h : f.τ₂ = g.τ₂) :
    ShortComplex.homologyMap f = ShortComplex.homologyMap g := by
  apply (cancel_epi S.homologyπ).mp
  apply (cancel_mono T.homologyι).mp
  simp only [Category.assoc, ShortComplex.π_homologyMap_ι]
  rw [h]

#print axioms shortComplex_homologyMap_eq_of_middle
/-- The exact rational forgetful functor detects actual short-complex quasi-isomorphisms.
Source: Weibel, An Introduction to Homological Algebra, section 1.3; exact conservative forgetting of rational scalar structure.
HC no distance; AV milestone no distance.
-/
theorem rationalShortComplex_quasiIso_of_forget {S T : ShortComplex (ModuleCat.{0} ℚ)}
    (f : S ⟶ T)
    (hf : ShortComplex.QuasiIso ((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapShortComplex.map f)) :
    ShortComplex.QuasiIso f := by
  exact (ShortComplex.quasiIso_map_iff_of_preservesLeftHomology
    (forget₂ (ModuleCat ℚ) AddCommGrpCat) f).mp hf

#print axioms rationalShortComplex_quasiIso_of_forget
end HodgeLean.Foundations.RationalHomologyManifold
