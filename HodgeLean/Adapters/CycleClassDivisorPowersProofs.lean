import HodgeLean.Adapters.CycleClassDivisorPowersDefs
import HodgeLean.Adapters.AbelianHodgeDischarge
import HodgeLean.Adapters.Connected

/-! # Proof obligations for the divisor-first interface
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Adapters

open scoped CategoryTheory.MonObj TensorProduct in
theorem ccm8_translation_pullback_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (t : ComplexPoint X) (n : ℕ) (a : HQ X n) :
    homPullback (GrpObj.mulRight t).hom n a = a := by
  letI : PathConnectedSpace (ComplexPoint X) := pathConnectedSpace_complexPoint X
  let pathToOne : Path t (1 : ComplexPoint X) := PathConnectedSpace.somePath t 1
  let H : ContinuousMap.Homotopy
      (Point.continuousMap (GrpObj.mulRight t).hom) (ContinuousMap.id _) :=
    { toFun := fun x => x.2 * pathToOne x.1
      continuous_toFun := by fun_prop
      map_zero_left := fun x => by
        simp only [pathToOne, Path.source]
        change CartesianMonoidalCategory.lift x t ≫ MonObj.mul =
          x ≫ CartesianMonoidalCategory.lift (𝟙 X)
            (SemiCartesianMonoidalCategory.toUnit X ≫ t) ≫ MonObj.mul
        rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
        congr 1
        ext <;> simp
      map_one_left := fun x => by simp }
  have h := cohomologyMap_eq_of_homotopy
    (f := TopCat.ofHom (Point.continuousMap (GrpObj.mulRight t).hom)) (g := 𝟙 _) H n
  unfold homPullback
  simp only [LinearMap.comp_apply]
  rw [h, cohomologyMap_id, LinearMap.id_apply]
  change (cupComparison X n).symm ((cupComparison X n) a) = a
  exact (cupComparison X n).symm_apply_apply a

theorem ccm8_hdg_le_span_g1_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (hT : TorusCohomology μ)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  intro p
  rcases p with _ | _ | p
  · exact hodge_degree_zero_unconditional X
  · exact h11
  · intro a _
    have hsub : Subsingleton (HQ X (2 * (p + 2))) :=
      (vanishingAboveTop_of_torusCohomology hT).subsingleton (2 * (p + 2)) (by omega)
    have ha : a = 0 := hsub.elim a 0
    rw [ha]
    exact Submodule.zero_mem _

theorem ccm8_hdg_le_span_g2_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (hT : TorusCohomology μ) (η : HQ X 2)
    (hpow : cupPow X μ η 2 ∈ algebraicCycleClassSpan X 2)
    (hne : cupPow X μ η 2 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  letI := hT.finite
  letI := (finiteBetti_of_torusCohomology hT).finite 4
  intro p
  rcases p with _ | _ | _ | p
  · exact hodge_degree_zero_unconditional X
  · exact h11
  · have hfin : Module.finrank ℚ (HQ X 4) = 1 := by
      rw [finrank_HQ_abelian, hg]
      norm_num
    have hrank : Module.rank ℚ (HQ X 4) ≤ 1 := by
      rw [← Module.finrank_eq_rank, hfin]
      norm_num
    have hspan : Submodule.span ℚ {cupPow X μ η 2} = ⊤ :=
      span_singleton_eq_top_of_rank_le_one hrank hne
    change Hdg^2(X; ℚ) ≤ algebraicCycleClassSpan X 2
    have htop : (⊤ : Submodule ℚ (HQ X 4)) ≤ algebraicCycleClassSpan X 2 := by
      rw [← hspan]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr hpow
    exact le_trans le_top htop
  · intro x _
    have hx : x = 0 :=
      ((vanishingAboveTop_abelian X).subsingleton (2 * (p + 3)) (by omega)).elim x 0
    rw [hx]
    exact Submodule.zero_mem _

theorem ccm8_hdg_le_span_g3_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (hT : TorusCohomology μ) (η : HQ X 2)
    (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (hC : CupFiltered X μ) (hηH : η ∈ Hdg^1(X; ℚ))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  intro p b hb
  have low : ∀ j, j ≤ 1 → Hdg^j(X; ℚ) ≤ algebraicCycleClassSpan X j := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact hodge_degree_zero complexPointsPreconnected X
    · exact h11
  by_cases hp1 : p ≤ 1
  · exact low p hp1 hb
  by_cases hpn : dim X.left < p
  · have := (vanishingAboveTop_of_torusCohomology hT).subsingleton (2 * p) (by omega)
    obtain rfl : b = 0 := Subsingleton.elim ( α := HQ X (2 * p)) b 0
    exact Submodule.zero_mem _
  let hB := HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X
  let hD := hodgeDecomposition_of_abelian X
  have hR : LefschetzReflectsHodge X μ η :=
    lefschetzReflectsHodge_of_cupFiltered hB hD hC hL hηH
  obtain ⟨j, hj⟩ : ∃ j, j = dim X.left - p := ⟨_, rfl⟩
  have hk : 2 * j ≤ dim X.left := by omega
  have h : 2 * j + 2 * (dim X.left - 2 * j) = 2 * p := by omega
  obtain ⟨a, rfl⟩ := (hL.bijective hk h).2 b
  have ha : a ∈ Hdg^j(X; ℚ) := hR.reflects h (by omega) a hb
  exact lefschetzPow_mem_algebraicCycleClassSpan hA _ j p h a (low j (by omega) ha)

end HodgeLean.Adapters
