import HodgeLean.Foundations.QuotientDuality.ProperCyclePullbackPoints
import HodgeLean.Foundations.Program.SchoenTowerT11bRealImageFormula

/-! # Actual Boolean images of original closed projective subschemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original closed projective subscheme has its literal image in the specified Euclidean Boolean projective model represented by a Boolean formula.
Source: properCycle_affine_chart_projective_image; properCycle_over_pullback_point_lift; s2v_t11b_finite_union_formula.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_closed_boolean_image (n : ℕ) (Z : Over (Spec ↧ℂ))
    (j : Z ⟶ Over.mk (ProjectiveSpace.toBase (Fin (n+1)) (Spec ↧ℂ)))
    [IsClosedImmersion j.left] :
    ∃ B : s2v_t11b_Formula (Fintype.card
      ((Fin (n+1) × Fin (n+1)) ⊕ (Fin (n+1) × Fin (n+1)))),
      B.realize = Set.range (fun z : ComplexPoint Z =>
        (properCycle_projective_boolean_homeomorph n (Point.map j z)).val) := by
  classical
  let α (i : Fin (n+1)) : Over.mk (complexAffineSpace (Fin (n+1)) ↘ Spec ↧ℂ) ⟶
      Over.mk (ProjectiveSpace.toBase (Fin (n+1)) (Spec ↧ℂ)) :=
    Over.homMk (chartAffineToProjectiveSpace i) (chartAffineToProjectiveSpace_over i)
  letI : IsAffine (Over.mk (complexAffineSpace (Fin (n+1)) ↘ Spec ↧ℂ)).left :=
    inferInstanceAs (IsAffine (complexAffineSpace (Fin (n+1))))
  let X (i : Fin (n+1)) := properCycle_over_pullback (α i) j
  letI (i : Fin (n+1)) : IsAffine (X i).left :=
    inferInstanceAs (IsAffine (Limits.pullback (α i).left j.left))
  letI (i : Fin (n+1)) : LocallyOfFiniteType (X i).hom :=
    inferInstanceAs (LocallyOfFiniteType
      (Limits.pullback.fst (α i).left j.left ≫ (complexAffineSpace (Fin (n+1)) ↘ Spec ↧ℂ)))
  choose B hB using fun i => properCycle_affine_chart_projective_image n i (X i)
    (properCycle_over_pullback_fst (α i) j)
  obtain ⟨C, hC⟩ := s2v_t11b_finite_union_formula B
  refine ⟨C, ?_⟩
  ext y
  rw [hC]
  constructor
  · rintro ⟨i, hi⟩
    rw [hB i] at hi
    obtain ⟨w, hw⟩ := hi
    refine ⟨Point.map (properCycle_over_pullback_snd (α i) j) w, ?_⟩
    have hp : properCycle_over_pullback_fst (α i) j ≫ α i =
        properCycle_over_pullback_snd (α i) j ≫ j := by
      apply Over.OverMorphism.ext
      exact Limits.pullback.condition
    have he : chartAffineComplexPointMap i
        (Point.map (properCycle_over_pullback_fst (α i) j) w) =
        Point.map j (Point.map (properCycle_over_pullback_snd (α i) j) w) := by
      change Point.map (α i) _ = _
      rw [← Point.map_comp_apply, ← Point.map_comp_apply, hp]
    dsimp only
    rw [← he]
    exact hw
  · rintro ⟨z, hz⟩
    obtain ⟨v, hv⟩ := surjective_vectorToComplexPoint (Point.map j z)
    obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v.val v.property
    let x := vectorChartToAffinePoint i ⟨v.val, hi⟩
    have he : Point.map (α i) x = Point.map j z := by
      change chartAffineComplexPointMap i (vectorChartToAffinePoint i ⟨v.val, hi⟩) = _
      rw [chartVectorToComplexPoint_eq]
      exact hv
    obtain ⟨w, hw, _⟩ := properCycle_over_pullback_point_lift (α i) j x z he
    refine ⟨i, ?_⟩
    rw [hB i]
    refine ⟨w, ?_⟩
    dsimp only
    rw [hw]
    change (properCycle_projective_boolean_homeomorph n (Point.map (α i) x)).val = y
    rw [he]
    exact hz

end HodgeLean.Foundations.QuotientDuality
