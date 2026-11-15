import HodgeLean.Foundations.QuotientDuality.ProperCycleCollectedLocalNormalization
import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundaryNormalization
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.SingularMultiplicityLocal

/-! Original collected normalization in singular ambient schemes. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- An exact collected lift retains every original complex chart normalization in a singular ambient scheme. -/
lemma retained_collected_lift_normalized
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → Order.coheight ξ = k)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (s : s2e_supportedClass X (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k)
    (hs : enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) (2 * k) s =
      SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
        (fun i => a3b4_cycleSupport X.hom (γ i))
        (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) q
        (fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩) a) :
    a3b4_IsCycleClass X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k s := by
  classical
  let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
  let S := a3b4_cycleSupport X.hom Γ
  let B := properCycle_family_regular_boundary X γ q k ⊓ a3b4a_classAlgebraicSupport X.hom Γ
  have hlow : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ :=
    fun i ξ hi => (hcodim i ξ hi).ge
  have hΓ : ∀ ξ ∈ Γ.support, Order.coheight ξ = k := by
    intro ξ hξ
    obtain ⟨i, _, hi⟩ := properCycle_collected_component_occurs γ q ξ hξ
    exact hcodim i ξ hi
  have hgen : ∀ ξ ∈ Γ.support, ξ ∉ B := by
    intro ξ hξ hb
    have h := properCycle_family_regular_boundary_coheight X γ q k hlow ξ hb.1
    rw [hΓ ξ hξ] at h
    have hn : k + 1 ≤ k := by exact_mod_cast h
    omega
  apply properCycle_normalized_of_off_boundary_chart_models X k hk hdim hvan Γ
    (fun ξ hξ => (hΓ ξ hξ).ge) B inf_le_right hgen s
  intro r e heS x hx hxS he
  obtain ⟨V₀, hVe, hxV, hmult⟩ :=
    AlgebraicGeometry.SingularCycles.singular_chart_multiplicity_locally_constant
      X.hom Γ e he heS x hx hxS
  let V : Opens (ComplexPoint X) := V₀
  refine ⟨V, hxV, hVe, ?_⟩
  intro y hyV hyB
  by_cases hyS : y ∈ S
  · have hyFB : y.underlying ∉ properCycle_family_regular_boundary X γ q k :=
      fun hb => hyB ⟨hb, hyS⟩
    obtain ⟨_, ξ, _, _, _, hyξ, _, hother⟩ := properCycle_family_regular_boundary_isolation
      X γ q k hlow y (properCycle_collected_support_subset X γ q hyS) hyFB
    obtain ⟨W, hWe, hyW, hW⟩ := properCycle_collected_lift_normalization_at_isolated_point
      X k γ q a ha s hs r e heS he y (hVe hyV) hyS ξ hyξ hother
    have hW' : relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap (W : Set (ComplexPoint X)) S) s =
        a3b4_multiplicity X.hom Γ y •
          chartNormalProjectionCoclass (Fin r → ℂ) k e S heS W hWe := hW
    let J := V ⊓ W
    have hyJ : y ∈ J := ⟨hyV, hyW⟩
    have hJ := congrArg (relativeCohomologyMap ℚ (2 * k)
      (neighborhoodSupportInclusionPairMap (show J ≤ W from inf_le_right) S)) hW'
    have hJW := a3b4a_classLocal_restriction_comp S
      (show (J : Set (ComplexPoint X)) ⊆ W from fun _ h => h.2) (2 * k) s
    have hJ' := hJW.symm.trans hJ
    simp only [map_smul, chartNormalProjectionCoclass_restrict] at hJ'
    rw [hmult y hyV hyS] at hJ'
    apply supportRelativeCohomologyGerm_eq_of_restrict_eq (a3b4_an X.hom) S (2 * k)
      (show J ≤ V from inf_le_left) (show J ≤ V from inf_le_left) y hyJ
    have hJV := a3b4a_classLocal_restriction_comp S
      (show (J : Set (ComplexPoint X)) ⊆ V from fun _ h => h.1) (2 * k) s
    exact hJV.trans (hJ'.trans (by
      rw [map_smul, chartNormalProjectionCoclass_restrict]))
  · exact (supportRelativeCohomologyGerm_eq_zero_of_not_mem (a3b4_an X.hom) S (2 * k)
      (a3b4a_classSupport_isClosed X.hom Γ) V y hyV hyS _).trans
      (supportRelativeCohomologyGerm_eq_zero_of_not_mem (a3b4_an X.hom) S (2 * k)
        (a3b4a_classSupport_isClosed X.hom Γ) V y hyV hyS _).symm

end HodgeLean.Foundations.QuotientDuality
