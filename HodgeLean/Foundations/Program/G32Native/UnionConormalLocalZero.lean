import HodgeLean.Foundations.AlgebraicGeometry.ConormalLocalIsomorphism
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Detecting zero modules on open neighborhoods -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
namespace HodgeLean.Foundations.Program.G32Native

/-- A module vanishing on a neighborhood of each point is zero. -/
lemma unionConormal_isZero_of_open_neighborhoods {X : Scheme.{0}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj M)) : IsZero M := by
  have hi : IsIso (0 : M ⟶ 0) := by
    apply AlgebraicGeometry.Conormal.moduleMap_isIso_of_open_neighborhoods
    intro x
    obtain ⟨U, hx, hU⟩ := h x
    have hM : IsZero ((Scheme.Modules.pullback U.ι).obj M) :=
      hU.of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M)
    refine ⟨U, hx, hM.isIso ?_ _⟩
    exact (Scheme.Modules.pullback U.ι).map_isZero (isZero_zero X.Modules)
  exact (isZero_zero X.Modules).of_iso (asIso (0 : M ⟶ 0))

end HodgeLean.Foundations.Program.G32Native
