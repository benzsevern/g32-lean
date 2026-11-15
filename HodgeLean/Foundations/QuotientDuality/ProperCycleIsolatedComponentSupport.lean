import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentSupportMap

/-! # Actual isolated component neighborhoods inside literal cycle supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual component map into cycle support has exactly the original prime's analytic support as its range.
Source: range_map_of_closedImmersion; range_cycleComponentι.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_support_map_range
    (X : Over (Spec ↧ℂ)) (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) :
    Set.range (properCycle_component_support_map X γ ξ hξ) =
      {z : a3b4_cycleSupport X.hom γ | z.val.underlying ∈ closure ({ξ} : Set X.left)} := by
  let i := properCycle_component_over_inclusion X ξ
  letI : IsClosedImmersion i.left := by
    change IsClosedImmersion (cycleComponentι X.left ξ)
    infer_instance
  have hr : Set.range (Point.map i) =
      {z : ComplexPoint X | z.underlying ∈ closure ({ξ} : Set X.left)} := by
    rw [range_map_of_closedImmersion]
    change Point.underlying ⁻¹' Set.range (cycleComponentι X.left ξ) = _
    rw [range_cycleComponentι]
    rfl
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    have hm : Point.map i u ∈ Set.range (Point.map i) := ⟨u, rfl⟩
    rwa [hr] at hm
  · intro hz
    have hm : z.val ∈ Set.range (Point.map i) := by rw [hr]; exact hz
    obtain ⟨u, hu⟩ := hm
    exact ⟨u, Subtype.ext hu⟩

/-- Away from every other original prime support, the actual component map has neighborhood image inside the literal cycle support.
Source: Fulton, Intersection Theory, section 1.5, finite prime supports and their separated open pieces.
HC no distance; AV milestone no distance. -/
lemma properCycle_isolated_component_support_neighborhood
    (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom] (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) (z : a3b4_cycleSupport X.hom γ)
    (hother : ∀ η ∈ γ.support, η ≠ ξ → z.val.underlying ∉ closure ({η} : Set X.left)) :
    Set.range (properCycle_component_support_map X γ ξ hξ) ∈ 𝓝 z := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  let F : Set X.left := γ.support \ {ξ}
  have hF : F.Finite := (a3b2_support_finite γ).subset Set.diff_subset
  let B : Set X.left := ⋃ η ∈ F, closure ({η} : Set X.left)
  have hB : IsClosed B := hF.isClosed_biUnion (fun _ _ => isClosed_closure)
  let O : Set (a3b4_cycleSupport X.hom γ) :=
    {w | w.val.underlying ∉ B}
  have hO : IsOpen O := hB.isOpen_compl.preimage
    ((continuous_underlying_to_zariski X).comp continuous_subtype_val)
  have hzO : z ∈ O := by
    intro hzB
    obtain ⟨η, hη, hzη⟩ := Set.mem_iUnion₂.mp hzB
    exact hother η hη.1 (by simpa only [Set.mem_singleton_iff] using hη.2) hzη
  have hsub : O ⊆ Set.range (properCycle_component_support_map X γ ξ hξ) := by
    intro w hw
    have hwS : w.val.underlying ∈ ⋃ η ∈ γ.support, closure ({η} : Set X.left) := w.property
    obtain ⟨η, hη, hwη⟩ := Set.mem_iUnion₂.mp hwS
    have he : η = ξ := by
      by_contra hn
      exact hw (Set.mem_iUnion₂.mpr ⟨η, ⟨hη, by simpa only [Set.mem_singleton_iff] using hn⟩, hwη⟩)
    subst η
    rw [properCycle_component_support_map_range]
    exact hwη
  exact Filter.mem_of_superset (hO.mem_nhds hzO) hsub

end HodgeLean.Foundations.QuotientDuality
