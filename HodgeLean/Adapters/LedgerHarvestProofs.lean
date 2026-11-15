import HodgeLean.RealDefs.TopDegreeRank
import HodgeLean.RealDefs.CupFiltered
import HodgeLean.RealDefs.Filtration
import HodgeLean.Adapters.DegreeZeroUnconditional
import HodgeLean.Adapters.CupProductOf

/-! # Proof obligations for the ledger harvest specification

One obligation per statement of `HodgeLean.Adapters.LedgerHarvest`. All nine are proved, by two parallel provers. Spec doc:
`docs/specs/LedgerHarvest.md`.

Intended routes:
* curves (`dim X.left = 1`): `j5d_algebraicCycleClassSpan_one_eq_top` (with
  `SmoothOfRelativeDimension.of_isIntegral` rewritten by `dim X.left = 1`),
  `algebraicCycleClassSpan_zero_eq_top_unconditional`, and `j5d_vanishingAboveTop` for every
  degree above two;
* `Hdg^0(X; ℚ) = ⊤`: `hodgeFiltration_eq_top_of_nonpos` for `F^0` and its conjugate;
* Hard Lefschetz on a curve: `rank_H0_le_one` with `complexPointsPreconnected`,
  `CupProduct.unitClass_ne_zero`, `CupProduct.cup_one` and `j5d_finrank_HQ_two`;
* the milestones: `hodgeConjectureInDimensionLE_three` (and its two variants) applied to
  `complexPointsPreconnected` and `j5d_vanishingAboveTop`, with the inputs in dimension at most
  one supplied by the statements above. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- On a curve, every class of even degree `2 * n` is in the span of codimension-`n` cycle classes:
`n = 0` and `n = 1` are spans equal to `⊤`, and `H^(2n)` vanishes for `n ≥ 2`. -/
theorem harvest_mem_algebraicCycleClassSpan_curve (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (h1 : dim X.left = 1) :
    ∀ (n : ℕ) (x : H^(2 * n)(X; ℚ)), x ∈ algebraicCycleClassSpan X n
  | 0, x => by
    rw [algebraicCycleClassSpan_zero_eq_top_unconditional X]
    exact Submodule.mem_top
  | 1, x => by
    have : SmoothOfRelativeDimension 1 X.hom := by rw [← h1]; infer_instance
    have htop := j5d_algebraicCycleClassSpan_one_eq_top complexPointsPreconnected X
    exact htop ▸ Submodule.mem_top
  | n + 2, x => by
    have : Subsingleton (H^(2 * (n + 2))(X; ℚ)) :=
      (j5d_vanishingAboveTop X).subsingleton (2 * (n + 2)) (by omega)
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _

theorem harvest_cycleClassMultiplicative_curve_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (h1 : dim X.left = 1) (μ : CupProduct X) :
    CycleClassMultiplicative μ :=
  ⟨fun {p q} _ _ _ _ _ => harvest_mem_algebraicCycleClassSpan_curve X h1 (p + q) _⟩

theorem harvest_algebraicTimesDivisor_curve_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (h1 : dim X.left = 1) (μ : CupProduct X) (η : HQ X 2) :
    AlgebraicTimesDivisor X μ η :=
  ⟨harvest_mem_algebraicCycleClassSpan_curve X h1 1 η,
    fun {p} _ _ _ => harvest_mem_algebraicCycleClassSpan_curve X h1 (p + 1) _⟩

/-- Every class of `H^0` is a Hodge class: `F^0 = ⊤`, so its conjugate is `⊤` too. -/
theorem harvest_mem_hodgeClasses_zero (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (a : H^(2 * 0)(X; ℚ)) : a ∈ Hdg^0(X; ℚ) := by
  have htop : F^((0 : ℕ) : ℤ) H_dR^(((2 * 0 : ℕ)) : ℤ)(X) = ⊤ :=
    hodgeFiltration_eq_top_of_nonpos X (by simp) _
  show fieldToDeRhamCohomologyLinear ℚ X (2 * 0) a ∈
    hodgePiece X ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) ((2 * 0 : ℕ) : ℤ)
  refine ⟨?_, ?_⟩
  · rw [htop]
    trivial
  · show deRhamConjSemilinear X _ _ ∈ F^((0 : ℕ) : ℤ) H_dR^(((2 * 0 : ℕ)) : ℤ)(X)
    rw [htop]
    trivial

theorem harvest_lefschetzReflectsHodge_of_dim_le_one_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (h1 : dim X.left ≤ 1) (μ : CupProduct X) (η : HQ X 2) :
    LefschetzReflectsHodge X μ η := by
  refine ⟨fun {p r m} h hr a _ => ?_⟩
  obtain rfl : p = 0 := by omega
  exact harvest_mem_hodgeClasses_zero X a

/-- The zeroth Lefschetz power is bijective. -/
theorem harvest_lefschetzPow_zero_bijective {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (μ : CupProduct X) (η : HQ X 2) {k m : ℕ} (h : k + 2 * 0 = m) :
    Function.Bijective (lefschetzPow X μ η 0 h) := by
  obtain rfl : m = k := by omega
  have : lefschetzPow X μ η 0 h = LinearMap.id := LinearMap.ext (lefschetzPow_zero μ η h)
  rw [this]
  exact Function.bijective_id

/-- On a curve, `L : H^0 → H^2` is bijective for `η ≠ 0`: `H^0` is spanned by the unit class,
and `H^2` has rank one. -/
theorem harvest_lefschetzPow_one_bijective_curve {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (h1 : dim X.left = 1) (μ : CupProduct X) {η : HQ X 2}
    (hη : η ≠ 0) {m : ℕ} (h : 0 + 2 * 1 = m) :
    Function.Bijective (lefschetzPow X μ η 1 h) := by
  subst h
  have : SmoothOfRelativeDimension 1 X.hom := by rw [← h1]; infer_instance
  have := complexPointsPreconnected.preconnected X
  set u : HQ X 0 := unitClass X with hu
  have hL : ∀ c : ℚ, lefschetzPow X μ η 1 rfl (c • u) = c • η := by
    intro c
    rw [map_smul]
    congr 1
    exact (lefschetzPow_succ μ η 0 _ rfl rfl u).trans (μ.cup_one η)
  have hr : Module.rank ℚ (HQ X 0) ≤ 1 := rank_H0_le_one X
  have hu0 : u ≠ 0 := μ.unitClass_ne_zero
  have hspan := span_singleton_eq_top_of_rank_le_one hr hu0
  have hc : ∀ a : HQ X 0, ∃ c : ℚ, c • u = a := fun a =>
    Submodule.mem_span_singleton.mp (hspan ▸ Submodule.mem_top)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun a ha => ?_, fun b => ?_⟩
  · obtain ⟨c, rfl⟩ := hc a
    rw [hL, smul_eq_zero] at ha
    rcases ha with rfl | ha
    · exact zero_smul _ _
    · exact absurd ha hη
  · obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' η hη).mp
      (j5d_finrank_HQ_two complexPointsPreconnected X) b
    exact ⟨c • u, hL c⟩

theorem harvest_hardLefschetz_curve_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (h1 : dim X.left = 1) (μ : CupProduct X) {η : HQ X 2}
    (hη : η ≠ 0) :
    HardLefschetz X μ η := by
  refine ⟨fun {k m} hk h => ?_⟩
  generalize hr : dim X.left - k = r at h ⊢
  rcases (show k = 0 ∧ r = 1 ∨ r = 0 by omega) with ⟨rfl, rfl⟩ | rfl
  · exact harvest_lefschetzPow_one_bijective_curve h1 μ hη h
  · exact harvest_lefschetzPow_zero_bijective μ η h

theorem harvest_exists_lefschetzInputs_of_dim_le_one_aux :
    ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      dim X.left ≤ 1 → ∃ (μ : CupProduct X) (η : HQ X 2),
        HardLefschetz X μ η ∧ AlgebraicTimesDivisor X μ η ∧ LefschetzReflectsHodge X μ η := by
  intro X _ _ _ h1
  rcases Nat.lt_or_ge (dim X.left) 1 with h0 | h0
  · refine ⟨cupProductOf X, 0, ⟨fun {k m} hk h => ?_⟩, ⟨zero_mem _, fun {p} _ a _ => ?_⟩,
      harvest_lefschetzReflectsHodge_of_dim_le_one_aux X h1 _ 0⟩
    · generalize hr : dim X.left - k = r at h ⊢
      obtain rfl : r = 0 := by omega
      exact harvest_lefschetzPow_zero_bijective _ 0 h
    · have : Subsingleton (H^(2 * (p + 1))(X; ℚ)) :=
        (j5d_vanishingAboveTop X).subsingleton (2 * (p + 1)) (by omega)
      refine (fun (x : H^(2 * (p + 1))(X; ℚ)) => ?_) _
      rw [Subsingleton.elim x 0]
      exact zero_mem _
  · have h1' : dim X.left = 1 := by omega
    have : SmoothOfRelativeDimension 1 X.hom := by rw [← h1']; infer_instance
    have : Nontrivial (HQ X 2) := Module.nontrivial_of_finrank_eq_succ
      (j5d_finrank_HQ_two complexPointsPreconnected X)
    obtain ⟨η, hη⟩ := exists_ne (0 : HQ X 2)
    exact ⟨cupProductOf X, η, harvest_hardLefschetz_curve_aux X h1' _ hη,
      harvest_algebraicTimesDivisor_curve_aux X h1' _ η,
      harvest_lefschetzReflectsHodge_of_dim_le_one_aux X h1 _ η⟩

theorem harvest_hodgeConjectureInDimensionLE_one_aux : HodgeConjectureInDimensionLE 1 := by
  intro X _ _ _ hX p b hb
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact hodge_degree_zero_unconditional X hb
  by_cases hpn : dim X.left < p
  · have := (j5d_vanishingAboveTop X).subsingleton (2 * p) (by omega)
    obtain rfl : b = 0 := Subsingleton.elim (α := HQ X (2 * p)) b 0
    exact Submodule.zero_mem _
  obtain rfl : p = 1 := by omega
  have h1 : dim X.left = 1 := by omega
  have : SmoothOfRelativeDimension 1 X.hom := by
    have := SmoothOfRelativeDimension.of_isIntegral (X := X.left) (f := X.hom)
    rwa [h1] at this
  rw [j5d_algebraicCycleClassSpan_one_eq_top complexPointsPreconnected X]
  exact Submodule.mem_top

theorem harvest_hodgeConjectureInDimensionLE_three_aux
    (h11 : LefschetzOneOneHyp)
    (hops : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      2 ≤ dim X.left → dim X.left ≤ 3 → ∃ (μ : CupProduct X) (η : HQ X 2),
        HardLefschetz X μ η ∧ AlgebraicTimesDivisor X μ η ∧ LefschetzReflectsHodge X μ η) :
    HodgeConjectureInDimensionLE 3 := by
  refine hodgeConjectureInDimensionLE_three h11 complexPointsPreconnected
    (fun X _ _ _ hX => ?_) j5d_vanishingAboveTop
  by_cases h2 : 2 ≤ dim X.left
  · exact hops X h2 hX
  · exact harvest_exists_lefschetzInputs_of_dim_le_one_aux X (by omega)

theorem harvest_hodgeConjectureForAbelianVarietiesInDimensionLE_three_aux
    (h11 : LefschetzOneOneHyp)
    (hops : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      2 ≤ dim X.left → dim X.left ≤ 3 → ∃ (μ : CupProduct X) (η : HQ X 2),
        HardLefschetz X μ η ∧ AlgebraicTimesDivisor X μ η ∧ LefschetzReflectsHodge X μ η) :
    HodgeConjectureForAbelianVarietiesInDimensionLE 3 :=
  hodgeConjectureForAbelianVarietiesInDimensionLE_of_inDimensionLE
    (harvest_hodgeConjectureInDimensionLE_three_aux h11 hops)

theorem harvest_hodgeConjectureInDimensionLE_three_of_cupFiltered_aux
    (h11 : LefschetzOneOneHyp)
    (hops : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      2 ≤ dim X.left → dim X.left ≤ 3 → ∃ (μ : CupProduct X) (η : HQ X 2),
        HardLefschetz X μ η ∧ AlgebraicTimesDivisor X μ η ∧ CupFiltered X μ)
    (hB : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      BettiDeRhamIso X)
    (hD : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HodgeDecomposition X)
    (hcyc : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      CycleClassIsHodge X) :
    HodgeConjectureInDimensionLE 3 := by
  refine harvest_hodgeConjectureInDimensionLE_three_aux h11 (fun X _ _ _ h2 h3 => ?_)
  obtain ⟨μ, η, hL, hA, hC⟩ := hops X h2 h3
  exact ⟨μ, η, hL, hA, lefschetzReflectsHodge_of_cupFiltered (hB X) (hD X) hC hL
    ((hcyc X).le 1 hA.η_mem)⟩

end HodgeLean.Adapters
