import HodgeLean.Foundations.Program.SchoenCycleU1ConstantDualPoint
import HodgeLean.Foundations.Program.SchoenCycleU1PolynomialDualParameter

/-! # The actual complex residue point of the dual-number scheme -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual complex point of the specified dual-number scheme induced by
its residue algebra map.
Source: Hartshorne, Algebraic Geometry, II.8, residue of a tangent vector. -/
def s2e_u1_dualResiduePoint : ComplexPoint (s2e_u1_specOver (DualNumber ℂ)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (by
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

/-- The actual residue point of the dual-number parameter maps to the actual
zero point of the polynomial parameter scheme.
Source: Hartshorne, Algebraic Geometry, II.8, reduction of a tangent vector. -/
theorem s2e_u1_dualResiduePoint_polynomialParameter :
    Point.map s2e_u1_polynomialDualParameter s2e_u1_dualResiduePoint =
      s2e_u1_polynomialParameterPoint 0 := by
  apply Over.OverMorphism.ext
  simp only [Point.map, Over.comp_left, s2e_u1_polynomialDualParameter,
    s2e_u1_dualResiduePoint, s2e_u1_specOverMap, s2e_u1_polynomialParameterPoint,
    Over.homMk_left]
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change ((Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ))
      (Polynomial.C c)).fst = (Polynomial.aeval (0 : ℂ)) (Polynomial.C c)
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · change ((Polynomial.aeval (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ))
      Polynomial.X).fst = (Polynomial.aeval (0 : ℂ)) Polynomial.X
    simp

end HodgeLean.Foundations.Program
