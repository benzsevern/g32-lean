import HodgeLean.Foundations.QuotientDuality.ProperCycleChartRestriction
import HodgeLean.Adapters.NormalConeB4aClassNormalization

/-! # Actual local scalar coordinates around a normalized chart point -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every original supported class is locally a scalar multiple of a normalized class at a holomorphic normal-chart point of nonzero multiplicity.
Source: Hatcher, Algebraic Topology, section 3.1, universal coefficients;
Fulton, Intersection Theory, section 19.1, the exact local normal coclass.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_proportionality_at_chart
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (a b : s2e_supportedClass X γ k) (ha : a3b4_IsCycleClass X.hom γ k a)
    (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom γ ↔ (e y).2 = 0)
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source)
    (hxS : x ∈ a3b4_cycleSupport X.hom γ) (hm : a3b4_multiplicity X.hom γ x ≠ 0) :
    ∃ (V : Opens (ComplexPoint X)), x ∈ V ∧ (V : Set (ComplexPoint X)) ⊆ e.source ∧
      ∃ q : ℚ, relativeCohomologyMap ℚ (2 * k)
          (a3b4_neighborhoodPairMap (V : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom γ)) b =
        q • relativeCohomologyMap ℚ (2 * k)
          (a3b4_neighborhoodPairMap (V : Set (ComplexPoint X)) (a3b4_cycleSupport X.hom γ)) a := by
  let S := a3b4_cycleSupport X.hom γ
  obtain ⟨W, hW, hWo, hxW, hnorm⟩ := ha r e hS x hx hxS he
  let O : Opens (ComplexPoint X) := ⟨W, hWo⟩
  let e' := e.restrOpen (O : Set (ComplexPoint X)) O.isOpen
  have hx' : x ∈ e'.source := ⟨hx, hxW⟩
  have hS' : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0 := fun y hy => hS y hy.1
  let V := flattenedSupportNeighborhood (Fin r → ℂ) k e' x hx'
  have hVe : (V : Set (ComplexPoint X)) ⊆ e'.source :=
    flattenedSupportNeighborhood_subset_source (Fin r → ℂ) k e' x hx'
  have hVO : (V : Set (ComplexPoint X)) ⊆ W := fun y hy => (hVe hy).2
  let bV := relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap (V : Set (ComplexPoint X)) S) b
  let t := relativeCohomologyEquivDualHomology ℚ _ (2 * k) bV
    (flattenedSupportNormalClass (Fin r → ℂ) k e' x hx' S hS' ((hS' x hx').mp hxS))
  have hbV := a3b4a_classLocal_eq_smul_normalCoclass e' S hS' x hx' hxS bV t rfl
  have haV := a3b4a_classLocal_normalization_mono e S hS hVO hW a _ hnorm
  have heq : chartNormalProjectionCoclass (Fin r → ℂ) k e' S hS' (V : Set (ComplexPoint X)) hVe =
      chartNormalProjectionCoclass (Fin r → ℂ) k e S hS (V : Set (ComplexPoint X)) (fun y hy => (hVe hy).1) :=
    properCycle_chart_normal_coclass_restrOpen k e S hS O V hVe
  rw [heq] at hbV
  refine ⟨V, mem_flattenedSupportNeighborhood (Fin r → ℂ) k e' x hx',
    fun y hy => (hVe hy).1, t / a3b4_multiplicity X.hom γ x, ?_⟩
  rw [haV, smul_smul, div_mul_cancel₀ _ hm]
  exact hbV

end HodgeLean.Foundations.QuotientDuality
