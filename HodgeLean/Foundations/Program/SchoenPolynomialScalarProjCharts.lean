import HodgeLean.Foundations.Program.SchoenPolynomialScalarChartIso
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial HomogeneousLocalization CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Polynomial scalar extension induces an isomorphism on each actual relative Proj chart. -/
theorem s2_polynomialRelativeProjChart_isIso (R ι : Type) [CommRing R] (i : ι) :
    IsIso (b54_relativeProjChart (s2_polynomialIntegralCoordinates R ι) (X i)) := by
  let f := s2_polynomialIntegralCoordinates R ι
  let φ := b54_relativeChartMap f (X i)
  let e := b54_affineProductIso (homogeneousSubmodule ι R 0)
    (Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i))
  have he : b54_relativeProjChart f (X i) ≫ e.hom =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    dsimp only [e, b54_affineProductIso, Iso.trans_hom, asIso_hom]
    apply (cancel_mono (pullbackSpecIso ℤ _ _).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [b54_relativeProjChart, Category.assoc, pullback.map,
        pullback.lift_fst, Category.comp_id]
      rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext c
      simp [φ, b54_relativeChartMap]
    · simp only [b54_relativeProjChart, Category.assoc, pullback.map,
        pullback.lift_snd, Category.comp_id]
      rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext d
      simp [φ, b54_relativeChartMap]
  have : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    isIso_SpecMap_iff.mpr (s2_polynomialScalarChartMap_bijective R ι i)
  have : IsIso (b54_relativeProjChart f (X i) ≫ e.hom) := he ▸ this
  exact (isIso_comp_right_iff _ e.hom).mp this

end HodgeLean.Foundations.Program
