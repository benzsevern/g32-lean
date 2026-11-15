import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinatePermutation
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # Actual regular coordinate ratios under specified coordinate permutations -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual degree-zero localization map retains the specified permuted denominator. -/
def projectiveCoordinateChartMap (k : ℕ) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    HomogeneousLocalization.Away (UniversalGrading k) (X j) →+*
      HomogeneousLocalization.Away (UniversalGrading k) (X (e.symm j)) :=
  HomogeneousLocalization.map (projectiveCoordinateRename e.symm) (by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, by simp only [map_pow, projectiveCoordinateRename_X]⟩)

#print axioms projectiveCoordinateChartMap
/-- The actual regular coordinate ratios retain both specified permuted indices. -/
theorem projectiveCoordinateChartMap_coordinate (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (j l : Fin (k + 1)) :
    projectiveCoordinateChartMap k e j (chartCoordinate j l) =
      chartCoordinate (e.symm j) (e.symm l) := by
  rw [HomogeneousLocalization.ext_iff_val]
  change Localization.mk
    (projectiveCoordinateRename e.symm (X l))
    ⟨projectiveCoordinateRename e.symm (X j ^ 1), _⟩ = _
  simp only [projectiveCoordinateRename_X, chartCoordinate,
    HomogeneousLocalization.Away.val_mk, pow_one]

#print axioms projectiveCoordinateChartMap_coordinate
/-- Evaluation of the permuted chart map retains every original affine coordinate value. -/
theorem projectiveCoordinateChartMap_evaluation (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (v : CoordinateSpace k)
    (j : Fin (k + 1)) (hj : v (e.symm j) ≠ 0) :
    (awayCoordinateEvaluation v (e.symm j) hj).comp
        (projectiveCoordinateChartMap k e j) =
      awayCoordinateEvaluation (v ∘ e.symm) j hj := by
  apply awayRingHom_ext j
  · intro a
    exact DFunLike.congr_fun (degreeZero_ringHom_unique
      (((awayCoordinateEvaluation v (e.symm j) hj).comp
        (projectiveCoordinateChartMap k e j)).comp
          (HomogeneousLocalization.fromZeroRingHom (UniversalGrading k)
            (Submonoid.powers (X j))))
      ((awayCoordinateEvaluation (v ∘ e.symm) j hj).comp
        (HomogeneousLocalization.fromZeroRingHom (UniversalGrading k)
          (Submonoid.powers (X j))))) a
  · intro l
    simp only [RingHom.comp_apply, projectiveCoordinateChartMap_coordinate]
    rw [s2e_projective_chartCoordinate_eval, s2e_projective_chartCoordinate_eval]
    rfl

#print axioms projectiveCoordinateChartMap_evaluation
/-- The actual regular chart map is the restriction of the specified integral projective coordinate isomorphism. -/
theorem projectiveCoordinateChartMap_awayι (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 1)) :
    Spec.map (CommRingCat.ofHom (projectiveCoordinateChartMap k e j)) ≫
        Proj.awayι (UniversalGrading k) (X j) (isHomogeneous_X _ _) zero_lt_one =
      Proj.awayι (UniversalGrading k) (X (e.symm j))
        (isHomogeneous_X _ _) zero_lt_one ≫ (integralProjectiveCoordinateIso e).hom := by
  let g := projectiveCoordinateRename e.symm
  have aux (q : UniversalRing k) (hq : q ∈ UniversalGrading k 1)
      (heq : g (X j) = q) :
      Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.map g (P := Submonoid.powers (X j))
          (Q := Submonoid.powers q) (by
            rintro _ ⟨m, rfl⟩
            exact ⟨m, by simp only [map_pow, heq]⟩))) ≫
          Proj.awayι (UniversalGrading k) (X j) (isHomogeneous_X _ _) zero_lt_one =
        Proj.awayι (UniversalGrading k) q hq zero_lt_one ≫
          (integralProjectiveCoordinateIso e).hom := by
    subst q
    exact (Proj.awayι_comp_map g (projectiveCoordinateRename_irrelevant e.symm)
      zero_lt_one (X j) (isHomogeneous_X (ULift ℤ) j)).symm
  exact aux (X (e.symm j)) (isHomogeneous_X _ _) (projectiveCoordinateRename_X e.symm j)

#print axioms projectiveCoordinateChartMap_awayι
end HodgeLean.Foundations.Program.G32Native.EulerModel
