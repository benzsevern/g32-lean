import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Dominance from an integral scheme to a reduced scheme gives injective stalk maps.
Source: injectivity of sections under dominance and injectivity of germs on integral schemes. -/
theorem s0_dominant_stalkMap_injective
    {X Y : Scheme} [IsIntegral X] [IsReduced Y]
    (f : X ⟶ Y) [QuasiCompact f] [IsDominant f] (x : X) :
    Function.Injective (f.stalkMap x) := by
  letI : IsSchemeTheoreticallyDominant f := .of_isDominant f
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) (by simp)
  apply hU.stalkMap_injective f x hxU
  intro g hg
  rw [f.germ_stalkMap_apply] at hg
  have hg' : f.app U g = 0 :=
    (germ_injective_of_isIntegral X x hxU) (hg.trans (map_zero _).symm)
  have hg0 : g = 0 := (f.app_injective U) (hg'.trans (map_zero _).symm)
  simp [hg0]

#print axioms s0_dominant_stalkMap_injective
end HodgeLean.Foundations.Program
