import HodgeLean.Foundations.BundleResolution.ChernCocyclePairingHelpers

/-! # Ordinary cup products on singular representatives

The existing ordinary cohomology cup product uses the actual
Alexander–Whitney cocycle product.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

attribute [local implicit_reducible] ShortComplex.moduleCatMk

variable (R : Type) [CommRing R] (X : TopCat) (p q : ℕ)

def i1_cupCocycle (φ : Cocycle R (TopCat.toSSet.obj X) p)
    (ψ : Cocycle R (TopCat.toSSet.obj X) q) : Cocycle R (TopCat.toSSet.obj X) (p + q) :=
  ⟨cupCochain X p q φ.val ψ.val, by
    change coboundary R (p + q) (cupCochain X p q φ.val ψ.val) = 0
    rw [coboundary_cupCochain, φ.property, ψ.property]
    simp only [map_zero, LinearMap.zero_apply, LinearMap.zero_comp, smul_zero, add_zero]⟩

set_option backward.isDefEq.respectTransparency false in
theorem i1_cup_on_class (φ : Cocycle R (TopCat.toSSet.obj X) p)
    (ψ : Cocycle R (TopCat.toSSet.obj X) q) :
    cup X rfl (cohomologyClass X p φ) (cohomologyClass X q ψ) =
      cohomologyClass X (p + q) (i1_cupCocycle R X p q φ ψ) := by
  simp only [cup, cohomologyClass, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  rfl

end HodgeLean.Foundations.BundleResolution
