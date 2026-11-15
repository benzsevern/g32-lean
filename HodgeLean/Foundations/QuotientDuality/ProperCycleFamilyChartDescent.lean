import HodgeLean.Foundations.QuotientDuality.ProperCycleFamilyBoundaryGerms
import HodgeLean.Foundations.QuotientDuality.ProperCycleAnchorCancellation

/-! # Exact finite-family support descent from regular-point chart coverage -/

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

/-- Normalized independent representatives descend exactly to their collected support when one active representative has a normal chart at each active point off the constructed common boundary.
Source: Fulton, Intersection Theory, sections 1.5 and 19.1; Bredon, Sheaf Theory, second edition, II.10 and V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_collected_supported_lift_of_regular_chart_cover
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (hcover : ∀ x : ComplexPoint X,
      x ∈ ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i) →
      x.underlying ∉ properCycle_family_regular_boundary X γ q k →
      ∃ (i : I), q i ≠ 0 ∧ ∃ (r : ℕ)
        (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ))),
        (∀ y ∈ e.source, y ∈ a3b4_cycleSupport X.hom (γ i) ↔ (e y).2 = 0) ∧
        a3b4_IsHolChart X.hom e ∧ x ∈ e.source ∧ x ∈ a3b4_cycleSupport X.hom (γ i)) :
    let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
    let T : Set (ComplexPoint X) := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
    let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
      fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩
    ∃ s : s2e_supportedClass X Γ k,
      enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) (2 * k) s =
        SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
          (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a := by
  classical
  dsimp only
  let Γ : AlgebraicCycle X.left ℚ := ∑ i, (γ i).mapRange (q i * ·) (mul_zero _)
  let T : Set (ComplexPoint X) := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
  let hT : ∀ i, q i ≠ 0 → a3b4_cycleSupport X.hom (γ i) ⊆ T :=
    fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩
  let A := SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
    (fun i => a3b4_cycleSupport X.hom (γ i)) T q hT a
  let S : Closeds (ComplexPoint X) :=
    ⟨a3b4_cycleSupport X.hom Γ, a3b4a_classSupport_isClosed X.hom Γ⟩
  let U := S.compl
  apply properCycle_active_union_descent_off_family_boundary X k hk hdim hvan γ q hcodim
    (S : Set (ComplexPoint X)) S.isClosed (properCycle_collected_support_subset X γ q) A
  intro x hxU hxB
  change supportRelativeCohomologyGerm (a3b4_an X.hom) T (2 * k) U x hxU
    (relativeCohomologyMap ℚ (2 * k)
      (a3b4_neighborhoodPairMap (U : Set (ComplexPoint X)) T) A) = 0
  by_cases hxT : x ∈ T
  · obtain ⟨_, ξ, _, _, _, hxξ, _, hother⟩ :=
      properCycle_family_regular_boundary_isolation X γ q k hcodim x hxT hxB
    obtain ⟨i, hi, r, e, heS, he, hxe, hxi⟩ := hcover x hxT hxB
    have hξi : ξ ∈ (γ i).support := by
      obtain ⟨η, hη, hxη⟩ := Set.mem_iUnion₂.mp hxi
      have hηξ : η = ξ := by
        by_contra hn
        exact hother i η hη hn hxη
      exact hηξ ▸ hη
    have hcancel : Γ ξ = 0 := by
      by_contra hn
      exact hxU (Set.mem_iUnion₂.mpr ⟨ξ, hn, hxξ⟩)
    obtain ⟨W, hWe, hxW, hW⟩ := properCycle_weighted_anchor_chart_cancellation
      X k γ a ha q i hi ξ hξi r e heS he x hxe hxξ hother hcancel
    let V := W ⊓ U
    have hxV : x ∈ V := ⟨hxW, hxU⟩
    have hV : relativeCohomologyMap ℚ (2 * k)
        (a3b4_neighborhoodPairMap (V : Set (ComplexPoint X)) T) A = 0 := by
      rw [← a3b4a_classLocal_restriction_comp T
        (show (V : Set (ComplexPoint X)) ⊆ W from fun _ h => h.1) (2 * k) A, hW, map_zero]
    rw [← supportRelativeCohomologyGerm_restrict (a3b4_an X.hom) T (2 * k)
      (show V ≤ U from inf_le_right) x hxV]
    have hr : relativeCohomologyMap ℚ (2 * k)
        (neighborhoodSupportInclusionPairMap (show V ≤ U from inf_le_right) T)
        (relativeCohomologyMap ℚ (2 * k)
          (a3b4_neighborhoodPairMap (U : Set (ComplexPoint X)) T) A) = 0 :=
      (a3b4a_classLocal_restriction_comp T
        (show (V : Set (ComplexPoint X)) ⊆ U from fun _ h => h.2) (2 * k) A).trans hV
    exact (congrArg (supportRelativeCohomologyGerm (a3b4_an X.hom) T (2 * k) V x hxV) hr).trans
      (by simp only [supportRelativeCohomologyGerm, map_zero])
  · have hclosed : IsClosed T := by
      dsimp only [T]
      rw [← properCycle_unsigned_family_analytic_support X γ q]
      exact a3b4a_classSupport_isClosed X.hom (properCycle_unsigned_family γ q)
    exact supportRelativeCohomologyGerm_eq_zero_of_not_mem (a3b4_an X.hom) T (2 * k)
      hclosed U x hxU hxT _

end HodgeLean.Foundations.QuotientDuality
