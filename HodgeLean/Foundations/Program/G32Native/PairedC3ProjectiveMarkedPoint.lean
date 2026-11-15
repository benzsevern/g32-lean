import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ProjectiveLineReciprocalPoints

/-! # The common diagonal point of the two projective charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- The value one in either affine chart is the same specified diagonal
point of the actual projective line. -/
theorem pairedC3_projective_marked_chart_eq (i : Fin 2) :
    (projectiveLineChart i (1 : ℂ)).left = (projectiveLineChart 1 (1 : ℂ)).left := by
  fin_cases i
  · let x : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap ℂ)) :=
      Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 _
        change 𝟙 _ ≫ Spec.map (𝟙 _) = 𝟙 _
        rw [Spec.map_id, Category.id_comp])
    have h := projectiveLineChart_reciprocal_points (1 : ℂ) (1 : ℂ) x x
      (by simp only [map_one, one_mul])
    haveI : IsIso x.left := by
      change IsIso (𝟙 _)
      infer_instance
    apply (cancel_epi x.left).mp
    exact congrArg Over.Hom.left h.symm
  · rfl

#print axioms pairedC3_projective_marked_chart_eq
end HodgeLean.Foundations.Program.G32Native
