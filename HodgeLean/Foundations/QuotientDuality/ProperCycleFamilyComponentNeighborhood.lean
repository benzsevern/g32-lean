import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalization

/-! # Actual common component neighborhoods for arbitrary finite cycle families -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A common neighborhood simultaneously identifies every family support with the selected component or with the empty set when that component is absent.
Source: Fulton, Intersection Theory, section 1.5, finite component supports;
Bredon, Sheaf Theory, second edition, I.6, neighborhoods of closed supports.
HC no distance; AV milestone no distance. -/
lemma properCycle_family_component_neighborhood
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ)
    (ξ : X.left) (x : ComplexPoint X)
    (hother : ∀ i η, η ∈ (γ i).support → η ≠ ξ →
      x.underlying ∉ closure ({η} : Set X.left))
    (P : Opens (ComplexPoint X)) (hxP : x ∈ P) :
    ∃ W : Opens (ComplexPoint X), W ≤ P ∧ x ∈ W ∧
      ∀ i y, y ∈ W → (y ∈ a3b4_cycleSupport X.hom (γ i) ↔
        ξ ∈ (γ i).support ∧ y.underlying ∈ closure ({ξ} : Set X.left)) := by
  classical
  have hlocal (i : I) : ∃ V : Opens (ComplexPoint X), x ∈ V ∧
      ∀ y ∈ V, y ∈ a3b4_cycleSupport X.hom (γ i) ↔
        ξ ∈ (γ i).support ∧ y.underlying ∈ closure ({ξ} : Set X.left) := by
    by_cases hξ : ξ ∈ (γ i).support
    · obtain ⟨V, _, hxV, hV⟩ := a3b4a_classSupport_local_eq_component X.hom (γ i) ξ hξ x
        (hother i) ⊤ (by trivial)
      refine ⟨V, hxV, ?_⟩
      intro y hy
      exact (hV y hy).trans (by simp only [hξ, true_and])
    · have hxnot : x ∉ a3b4_cycleSupport X.hom (γ i) := by
        intro hxS
        obtain ⟨η, hη, hxη⟩ := Set.mem_iUnion₂.mp hxS
        exact hother i η hη (fun he => hξ (he ▸ hη)) hxη
      let V : Opens (ComplexPoint X) :=
        ⟨(a3b4_cycleSupport X.hom (γ i))ᶜ, (a3b4a_classSupport_isClosed X.hom (γ i)).isOpen_compl⟩
      refine ⟨V, hxnot, ?_⟩
      intro y hy
      exact iff_of_false hy (fun hh => hξ hh.1)
  choose V hxV hV using hlocal
  let W : Opens (ComplexPoint X) :=
    ⟨(P : Set (ComplexPoint X)) ∩ ⋂ i, (V i : Set (ComplexPoint X)),
      P.isOpen.inter (isOpen_iInter_of_finite fun i => (V i).isOpen)⟩
  refine ⟨W, Set.inter_subset_left, ⟨hxP, Set.mem_iInter.mpr hxV⟩, ?_⟩
  intro i y hy
  exact hV i y (Set.mem_iInter.mp hy.2 i)

end HodgeLean.Foundations.QuotientDuality
