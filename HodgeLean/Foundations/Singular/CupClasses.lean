import HodgeLean.Foundations.Singular.Cup

/-! Cup products on specified actual singular cocycle representatives. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicTopology.Simplicial
open scoped Simplicial
namespace HodgeLean.Foundations.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The cup of represented singular classes is represented by their specified cup cochain.
Source: Hatcher, Algebraic Topology, §3.2, definition of the cohomology cup product. -/
theorem cup_classes {R : Type} [CommRing R] (Y : TopCat.{0}) (p q : ℕ)
    (φ : Cocycle R (TopCat.toSSet.obj Y) p) (ψ : Cocycle R (TopCat.toSSet.obj Y) q)
    (χ : Cocycle R (TopCat.toSSet.obj Y) (p + q))
    (hχ : χ.1 = cupCochain Y p q φ.1 ψ.1) :
    cup Y rfl (cohomologyClass Y p φ) (cohomologyClass Y q ψ) =
      cohomologyClass Y (p + q) χ := by
  let κ : Cocycle R (TopCat.toSSet.obj Y) (p + q) := ⟨cupCochain Y p q φ.1 ψ.1, by
    change coboundary R (p + q) (cupCochain Y p q φ.1 ψ.1) = 0
    rw [coboundary_cupCochain, show coboundary R p φ.1 = 0 from φ.property,
      show coboundary R q ψ.1 = 0 from ψ.property]
    simp⟩
  have hk : cup Y rfl (cohomologyClass Y p φ) (cohomologyClass Y q ψ) =
      cohomologyClass Y (p + q) κ := by
    dsimp [cup, cohomologyClass, LinearMap.comp_apply]
    erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  exact hk.trans (congrArg (cohomologyClass Y (p + q)) (Subtype.ext hχ.symm))

#print axioms cup_classes
end HodgeLean.Foundations.Singular
