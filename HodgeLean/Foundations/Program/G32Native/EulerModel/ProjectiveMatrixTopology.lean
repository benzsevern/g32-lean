import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassLinearInvariance
import Mathlib.Topology.CompactOpen

/-! # Continuous matrix actions on the actual homogeneous projective quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual projective action of the specified invertible homogeneous matrix. -/
def projectiveCoordinateMatrixMap (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0) :
    Projectivization ℂ (CoordinateSpace k) → Projectivization ℂ (CoordinateSpace k) :=
  Projectivization.map A.mulVecLin (A.mulVec_injective_of_det_ne_zero hA)

/-- The homogeneous matrix action is continuous for the actual quotient topology. -/
theorem continuous_projectiveCoordinateMatrixMap (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0) :
    Continuous (projectiveCoordinateMatrixMap k A hA) := by
  apply continuous_coinduced_dom.mpr
  exact isQuotientMap_quotient_mk'.continuous.comp
    ((A.mulVecLin.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk
      (fun v => by
        intro h
        apply v.2
        apply A.mulVec_injective_of_det_ne_zero hA
        change A.mulVec v.1 = 0 at h
        simpa only [Matrix.mulVec_zero] using h))

#print axioms projectiveCoordinateMatrixMap
#print axioms continuous_projectiveCoordinateMatrixMap
/-- The projective matrix action is jointly continuous along the actual invertible matrix path. -/
theorem continuous_projectiveCoordinateMatrixPath (k : ℕ)
    {A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (H : Matrix.ComplexIsotopyToOne A) :
    Continuous (fun tp : unitInterval × Projectivization ℂ (CoordinateSpace k) =>
      projectiveCoordinateMatrixMap k (H.path tp.1) (H.det_ne_zero tp.1) tp.2) := by
  let π : {v : CoordinateSpace k // v ≠ 0} → Projectivization ℂ (CoordinateSpace k) :=
    fun v => Projectivization.mk ℂ v.1 v.2
  have hπ : Topology.IsQuotientMap π := isQuotientMap_quotient_mk'
  apply hπ.continuous_lift_prod_right
  have hv : Continuous (fun tv : unitInterval × {v : CoordinateSpace k // v ≠ 0} =>
      (H.path tv.1).mulVec tv.2.1) :=
    (AlgebraicTopology.Singular.continuous_complexMatrixPath_mulVec (k + 1) H.path).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact hπ.continuous.comp (hv.subtype_mk (fun tv => by
    intro hz
    apply tv.2.2
    apply (H.path tv.1).mulVec_injective_of_det_ne_zero (H.det_ne_zero tv.1)
    simpa only [Matrix.mulVec_zero] using hz))

#print axioms continuous_projectiveCoordinateMatrixPath
/-- The actual projective matrix map retains the specified homogeneous matrix-vector formula. -/
theorem projectiveCoordinateMatrixMap_mk (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0)
    (v : CoordinateSpace k) (hv : v ≠ 0) :
    projectiveCoordinateMatrixMap k A hA (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (A.mulVec v) (by
        intro hz
        apply hv
        apply A.mulVec_injective_of_det_ne_zero hA
        simpa only [Matrix.mulVec_zero] using hz) := by
  rfl

#print axioms projectiveCoordinateMatrixMap_mk
end HodgeLean.Foundations.Program.G32Native.EulerModel
