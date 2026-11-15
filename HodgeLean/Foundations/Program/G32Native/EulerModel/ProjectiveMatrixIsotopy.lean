import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveMatrixTopology
import Other.AlgebraicTopology.Singular.SupportNaturality

/-! # Actual homogeneous matrix paths and projective cohomology -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry.ComplexProjectiveSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual projective matrix action is homotopic to the identity along the specified invertible matrix path. -/
def projectiveCoordinateMatrixHomotopy (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0)
    (H : Matrix.ComplexIsotopyToOne A) :
    ContinuousMap.Homotopy (ContinuousMap.id (Projectivization ℂ (CoordinateSpace k)))
      ⟨projectiveCoordinateMatrixMap k A hA, continuous_projectiveCoordinateMatrixMap k A hA⟩ where
  toFun tp := projectiveCoordinateMatrixMap k (H.path tp.1) (H.det_ne_zero tp.1) tp.2
  continuous_toFun := continuous_projectiveCoordinateMatrixPath k H
  map_zero_left p := by
    induction p using Projectivization.ind with
    | h v hv =>
      change projectiveCoordinateMatrixMap k (H.path 0) (H.det_ne_zero 0)
        (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ v hv
      rw [projectiveCoordinateMatrixMap_mk]
      simp only [H.map_zero, Matrix.one_mulVec]
  map_one_left p := by
    change projectiveCoordinateMatrixMap k (H.path 1) (H.det_ne_zero 1) p =
      projectiveCoordinateMatrixMap k A hA p
    simp only [H.map_one]

#print axioms projectiveCoordinateMatrixHomotopy
/-- Every invertible complex homogeneous matrix acts identically on actual projective rational cohomology. -/
theorem projectiveCoordinateMatrix_cohomology (k n : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0)
    (α : Cohomology ℚ (TopCat.of (Projectivization ℂ (CoordinateSpace k))) n) :
    cohomologyMap ℚ n (TopCat.ofHom
      ⟨projectiveCoordinateMatrixMap k A hA, continuous_projectiveCoordinateMatrixMap k A hA⟩) α = α := by
  obtain ⟨H⟩ := Matrix.nonempty_complexIsotopyToOne A hA
  have he := cohomologyMap_eq_of_homotopy ℚ n
    (f := 𝟙 (TopCat.of (Projectivization ℂ (CoordinateSpace k))))
    (g := TopCat.ofHom
      ⟨projectiveCoordinateMatrixMap k A hA, continuous_projectiveCoordinateMatrixMap k A hA⟩)
    (projectiveCoordinateMatrixHomotopy k A hA H)
  rw [cohomologyMap_id] at he
  exact (congrArg (fun f => f α) he).symm

#print axioms projectiveCoordinateMatrix_cohomology
end HodgeLean.Foundations.Program.G32Native.EulerModel
