import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveMatrixIsotopy
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # Specified homogeneous matrix actions on native projective complex points -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified homogeneous matrix action on the actual native projective complex points. -/
def nativeProjectiveMatrixMap (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0) :
    C(ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))),
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) :=
  ContinuousMap.comp
    ⟨s2e_projectivePointHomeomorph k, (s2e_projectivePointHomeomorph k).continuous⟩
    (ContinuousMap.comp
      ⟨projectiveCoordinateMatrixMap k A hA, continuous_projectiveCoordinateMatrixMap k A hA⟩
      ⟨(s2e_projectivePointHomeomorph k).symm, (s2e_projectivePointHomeomorph k).symm.continuous⟩)

#print axioms nativeProjectiveMatrixMap
/-- The actual native projective matrix action follows the specified invertible matrix homotopy. -/
def nativeProjectiveMatrixHomotopy (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0)
    (H : Matrix.ComplexIsotopyToOne A) :
    ContinuousMap.Homotopy
      (ContinuousMap.id (ComplexPoint (Over.mk
        (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))))
      (nativeProjectiveMatrixMap k A hA) where
  toFun tp := s2e_projectivePointHomeomorph k
    (projectiveCoordinateMatrixHomotopy k A hA H
      (tp.1, (s2e_projectivePointHomeomorph k).symm tp.2))
  continuous_toFun := (s2e_projectivePointHomeomorph k).continuous.comp
    ((projectiveCoordinateMatrixHomotopy k A hA H).continuous.comp
      (continuous_fst.prodMk
        ((s2e_projectivePointHomeomorph k).symm.continuous.comp continuous_snd)))
  map_zero_left p := by
    exact (congrArg (s2e_projectivePointHomeomorph k)
      ((projectiveCoordinateMatrixHomotopy k A hA H).map_zero_left
        ((s2e_projectivePointHomeomorph k).symm p))).trans
          ((s2e_projectivePointHomeomorph k).apply_symm_apply p)
  map_one_left p := by
    exact congrArg (s2e_projectivePointHomeomorph k)
      ((projectiveCoordinateMatrixHomotopy k A hA H).map_one_left
        ((s2e_projectivePointHomeomorph k).symm p))

#print axioms nativeProjectiveMatrixHomotopy
/-- Every specified invertible homogeneous matrix acts identically on native projective rational cohomology. -/
theorem nativeProjectiveMatrix_cohomology (k n : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0)
    (α : Cohomology ℚ (TopCat.of (ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))) n) :
    cohomologyMap ℚ n (TopCat.ofHom (nativeProjectiveMatrixMap k A hA)) α = α := by
  obtain ⟨H⟩ := Matrix.nonempty_complexIsotopyToOne A hA
  have he := cohomologyMap_eq_of_homotopy ℚ n
    (f := 𝟙 (TopCat.of (ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))))
    (g := TopCat.ofHom (nativeProjectiveMatrixMap k A hA))
    (nativeProjectiveMatrixHomotopy k A hA H)
  rw [cohomologyMap_id] at he
  exact (congrArg (fun f => f α) he).symm

#print axioms nativeProjectiveMatrix_cohomology
/-- The actual native matrix action retains the exact specified homogeneous vector at every point. -/
theorem nativeProjectiveMatrixMap_point (k : ℕ)
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hA : A.det ≠ 0)
    (v : CoordinateSpace k) (hv : v ≠ 0) :
    nativeProjectiveMatrixMap k A hA (vectorToComplexPoint v hv) =
      vectorToComplexPoint (A.mulVec v) (by
        intro hz
        apply hv
        apply A.mulVec_injective_of_det_ne_zero hA
        simpa only [Matrix.mulVec_zero] using hz) := by
  change s2e_projectivePointHomeomorph k
    (projectiveCoordinateMatrixMap k A hA
      ((s2e_projectivePointHomeomorph k).symm
        (s2e_projectivePointHomeomorph k (Projectivization.mk ℂ v hv)))) = _
  rw [(s2e_projectivePointHomeomorph k).symm_apply_apply,
    projectiveCoordinateMatrixMap_mk]
  rfl

#print axioms nativeProjectiveMatrixMap_point
end HodgeLean.Foundations.Program.G32Native.EulerModel
