import HodgeLean.Foundations.QuotientDuality.ProperCycleChartNormal
import HodgeLean.Foundations.QuotientDuality.ProperCycleProductPurity

/-! # Supported purity from ambient local homology and actual product charts -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Ambient concentration supplies normal vanishing in cofinal product charts below the shifted degree.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, support localization and normal models.
HC no distance; AV milestone no distance. -/
lemma properCycle_ambient_product_charts_relative_vanishes
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : X,
      Subsingleton (orientationGroup X j x))
    (S : Closeds X) (n : ℕ)
    (hcharts : ∀ x ∈ S, ∀ V : Opens X, x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        ∃ (r : ℕ) (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ ((Fin r → ℂ) × Y)),
          (∀ w : W, (w : X) ∈ S ↔ (e w).2 = y) ∧ n + 2 * r < N)
    (U : Opens X) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set X) (S : Set X)) n) := by
  apply properCycle_product_charts_relative_vanishes X S n ?_ U
  intro j hj x hxS V hxV
  obtain ⟨W, hWV, hxW, r, Y, y, e, he, hbound⟩ := hcharts x hxS V hxV
  refine ⟨W, hWV, hxW, r, Y, y, e, he, ?_⟩
  let w : W := ⟨x, hxW⟩
  have hy : (e w).2 = y := (he w).mp hxS
  letI : T1Space ((Fin r → ℂ) × Y) := e.t1Space
  letI : T1Space Y := t1Space_of_injective_of_continuous
    (f := fun y : Y => ((0 : Fin r → ℂ), y))
    (fun a b h => congrArg Prod.snd h) (continuous_const.prodMk continuous_id)
  rw [← hy]
  exact properCycle_chart_normal_homology_subsingleton X W r Y e w j
    (hvan (j + 2 * r) (by omega) x)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Product charts are needed only at supported points of the analytic open being calculated.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, cofinal supported localization.
HC no distance; AV milestone no distance. -/
lemma properCycle_ambient_product_charts_open_relative_vanishes
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : X,
      Subsingleton (orientationGroup X j x))
    (S : Closeds X) (n : ℕ) (U : Opens X)
    (hcharts : ∀ x ∈ S, x ∈ U → ∀ V : Opens X, x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        ∃ (r : ℕ) (Y : TopCat.{0}) (y : Y) (e : W ≃ₜ ((Fin r → ℂ) × Y)),
          (∀ w : W, (w : X) ∈ S ↔ (e w).2 = y) ∧ n + 2 * r < N) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set X) (S : Set X)) n) := by
  apply a3b4a_classRelative_vanishing_of_cofinal_local_vanishing X S U n
  intro j hj x hxU V hxV
  by_cases hxS : x ∈ S
  · obtain ⟨W, hWV, hxW, r, Y, y, e, he, hbound⟩ := hcharts x hxS hxU V hxV
    refine ⟨W, hWV, hxW, ?_⟩
    let w : W := ⟨x, hxW⟩
    have hy : (e w).2 = y := (he w).mp hxS
    letI : T1Space ((Fin r → ℂ) × Y) := e.t1Space
    letI : T1Space Y := t1Space_of_injective_of_continuous
      (f := fun y : Y => ((0 : Fin r → ℂ), y))
      (fun a b h => congrArg Prod.snd h) (continuous_const.prodMk continuous_id)
    have hnormal : Subsingleton (orientationGroup Y j y) := by
      rw [← hy]
      exact properCycle_chart_normal_homology_subsingleton X W r Y e w j
        (hvan (j + 2 * r) (by omega) x)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (properCycle_product_chart_support_subsingleton X S W (Fin r → ℂ) Y y e he j hnormal)
  · let W : Opens X := V ⊓ S.compl
    refine ⟨W, inf_le_left, ⟨hxV, hxS⟩, ?_⟩
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (neighborhoodSupportRelativeCohomology_subsingleton X S j W (fun _ hy => hy.2))


end HodgeLean.Foundations.QuotientDuality
