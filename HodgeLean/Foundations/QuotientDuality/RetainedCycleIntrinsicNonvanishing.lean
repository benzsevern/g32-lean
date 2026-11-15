import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicClassProperties
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSingularProperDegree

/-! Nonvanishing of intrinsic classes and their positive-degree proper images. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified intrinsic top generator of an integral projective scheme is nonzero. -/
lemma retained_intrinsic_class_ne_zero
    (V : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsProjective V.hom]
    (d : ℕ) (hdim : topologicalKrullDim V.left = (d : ℕ)) :
    properCycle_intrinsic_class V d hdim ≠ 0 := by
  intro h
  have hinj := (properCycle_intrinsic_class_generates V d hdim).1
  have he : LinearMap.toSpanSingleton ℚ
      (Homology ℚ (a3b4_an V.hom) (2*d)) (properCycle_intrinsic_class V d hdim) 1 =
    LinearMap.toSpanSingleton ℚ
      (Homology ℚ (a3b4_an V.hom) (2*d)) (properCycle_intrinsic_class V d hdim) 0 := by
    simp only [LinearMap.toSpanSingleton_apply, h, smul_zero]
  exact one_ne_zero (hinj he)

/-- Positive actual proper residue degree retains a nonzero intrinsic fundamental-class image. -/
lemma retained_intrinsic_proper_image_ne_zero
    (V W : Over (Spec ↧ℂ)) [IsIntegral V.left] [IsIntegral W.left]
    [IsProjective V.hom] [IsProjective W.hom] (f : V ⟶ W) [IsProper f.left]
    (d : ℕ) (hdV : topologicalKrullDim V.left = (d : ℕ))
    (hdW : topologicalKrullDim W.left = (d : ℕ))
    (hg : f.left (genericPoint V.left) = genericPoint W.left)
    (hdeg : 0 < a1p_degree f.left (genericPoint V.left)) :
    homologyMap ℚ (2*d) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_class V d hdV) ≠ 0 := by
  rw [properCycle_intrinsic_proper_generic_degree V W f d hdV hdW hg hdeg]
  exact smul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hdeg))
    (retained_intrinsic_class_ne_zero W d hdW)

end HodgeLean.Foundations.QuotientDuality
