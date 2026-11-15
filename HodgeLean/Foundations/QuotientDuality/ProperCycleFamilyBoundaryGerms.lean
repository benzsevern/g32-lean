import HodgeLean.Foundations.QuotientDuality.ProperCycleSupportShrinking
import HodgeLean.Foundations.QuotientDuality.ProperCycleTopology
import HodgeLean.Foundations.QuotientDuality.ProperCycleFamilyRegularBoundary
import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalModelDetection

/-! # Actual active-union detection off the constructed common family boundary -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual active-union relative classes vanish when their germs vanish off the constructed smaller common algebraic boundary.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9, support localization and stalk detection.
HC no distance; AV milestone no distance. -/
lemma properCycle_active_union_relative_zero_off_family_boundary
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ)
    (U : Opens (a3b4_an X.hom))
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set (a3b4_an X.hom))
      (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i))) (2 * k))
    (ha : ∀ (x : a3b4_an X.hom) (hx : x ∈ U),
      x.underlying ∉ properCycle_family_regular_boundary X γ q k →
      supportRelativeCohomologyGerm (a3b4_an X.hom)
        (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) (2 * k) U x hx a = 0) :
    a = 0 := by
  letI : LocallyOfFiniteType X.hom := inferInstance
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI (V : Opens (ComplexPoint X)) : ParacompactSpace V := properCycle_open_paracompact X V
  let δ := properCycle_unsigned_family γ q
  let S := a3b4a_classAlgebraicSupport X.hom δ
  let B := properCycle_family_regular_boundary X γ q k
  have hδ := properCycle_unsigned_family_coheight γ q k hcodim
  have hdimS : topologicalKrullDim S ≤ (k : ℕ) := by
    have h := properCycle_closed_support_dimension_le_of_coheight X S k
      (a3b4a_classAlgebraicSupport_coheight X.hom δ k hδ)
    rw [hdim, show 2 * k - k = k by omega] at h
    exact h
  have hBS : B ≤ S := inf_le_right
  have hdimB := properCycle_family_regular_boundary_dimension X k hdim γ q hcodim
  revert a
  rw [← properCycle_unsigned_family_analytic_support X γ q]
  intro a ha
  apply properCycle_relative_eq_of_off_boundary_germs X S B hBS k (k - 1) hdimS hdimB
    (2 * (2 * k)) hvan (2 * k) (by omega) (by omega) U a 0
  intro x hx hxb
  change supportRelativeCohomologyGerm (a3b4_an X.hom)
    (a3b4_cycleSupport X.hom (properCycle_unsigned_family γ q)) (2 * k) U x hx a =
    supportRelativeCohomologyGerm (a3b4_an X.hom)
    (a3b4_cycleSupport X.hom (properCycle_unsigned_family γ q)) (2 * k) U x hx 0
  simpa only [supportRelativeCohomologyGerm, map_zero] using ha x hx hxb

/-- Exact support descent requires complement germ cancellation only away from the actual common family boundary.
Source: Bredon, Sheaf Theory, second edition, II.10 and V.9; Hatcher, Algebraic Topology, section 3.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_active_union_descent_off_family_boundary
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → (k : ℕ∞) ≤ Order.coheight ξ)
    (S : Set (a3b4_an X.hom)) (hS : IsClosed S)
    (hST : S ⊆ ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) :
    let T := ⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)
    let U : Opens (a3b4_an X.hom) := ⟨Sᶜ, hS.isOpen_compl⟩
    ∀ (a : CohomologyWithSupport ℚ (a3b4_an X.hom) T (2 * k)),
      (∀ (x : a3b4_an X.hom) (hx : x ∈ U),
        x.underlying ∉ properCycle_family_regular_boundary X γ q k →
        supportRelativeCohomologyGerm (a3b4_an X.hom) T (2 * k) U x hx
          (cohomologyWithSupportMap ℚ (2 * k) (TopPair.ofSubset Sᶜ).map T a) = 0) →
      ∃ b : CohomologyWithSupport ℚ (a3b4_an X.hom) S (2 * k),
        enlargeSupport ℚ (a3b4_an X.hom) hST (2 * k) b = a := by
  dsimp only
  intro a ha
  apply properCycle_supported_descent_of_restriction_zero (a3b4_an X.hom) S _ hST (2 * k) a
  exact properCycle_active_union_relative_zero_off_family_boundary X k hk hdim hvan γ q hcodim
    ⟨Sᶜ, hS.isOpen_compl⟩ _ ha

end HodgeLean.Foundations.QuotientDuality
