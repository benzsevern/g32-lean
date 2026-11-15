import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveFibers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The polynomial description of a projective chart preserves its coefficient morphism. -/
theorem s0_projective_chart_fiber_iso_over
    (R : Type) [CommRing R] [Algebra (ULift.{0} ℤ) R] {n : ℕ} (i : Fin (n + 1)) :
    (s0_projective_chart_fiber_iso R i).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial {j : Fin (n + 1) // j ≠ i} R))) =
      pullback.fst (terminal.from (Spec ↧R))
        (terminal.from (Spec ↧(HomogeneousLocalization.Away
          (UniversalGrading.{0} n) (MvPolynomial.X i)))) := by
  letI : Algebra (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
    (s0_projective_chart_base i).toAlgebra
  letI : Module (ULift.{0} ℤ) R := Algebra.toModule
  letI : Module (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
  let E := s0_projective_chart_baseChange_equiv R i
  have hE : (Scheme.Spec.mapIso E.toRingEquiv.symm.toCommRingCatIso.op).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial {j : Fin (n + 1) // j ≠ i} R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R _)) := by
    change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact E.symm.commutes r
  dsimp only [s0_projective_chart_fiber_iso, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, hE, pullbackSpecIso_hom_fst']
  simp only [asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id]

#print axioms s0_projective_chart_fiber_iso_over
end HodgeLean.Foundations.Program
