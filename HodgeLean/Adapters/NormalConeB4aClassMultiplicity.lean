import HodgeLean.Adapters.NormalConeB4aClassComponentNeighborhood

/-! # The frozen multiplicity on a separated regular component

Route: the selected component contains the support in a neighborhood. Every
other component misses the point, so none can contain such a neighborhood.
Only the selected coefficient contributes to the frozen finite sum.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- At a point lying on exactly one cycle component, the frozen multiplicity
is that component's coefficient. -/
theorem a3b4a_classMultiplicity_eq_component
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [QuasiCompact q]
    (γ : AlgebraicCycle Z ℚ) (ξ : Z) (hξ : ξ ∈ γ.support)
    (x : ComplexPoint (Over.mk q)) (hxξ : x.underlying ∈ closure ({ξ} : Set Z))
    (hother : ∀ η ∈ γ.support, η ≠ ξ → x.underlying ∉ closure ({η} : Set Z)) :
    a3b4_multiplicity q γ x = γ ξ := by
  classical
  letI : CompactSpace Z := a3b4_compactSpace q
  have hxS : x ∈ a3b4_cycleSupport q γ := Set.mem_iUnion₂.mpr ⟨ξ, hξ, hxξ⟩
  obtain ⟨W, _, hxW, hW⟩ := a3b4a_classSupport_local_eq_component q γ ξ hξ x hother ⊤ (by trivial)
  have hlocal : ∃ U : Set (ComplexPoint (Over.mk q)), IsOpen U ∧ x ∈ U ∧
      U ∩ a3b4_cycleSupport q γ ⊆ Point.underlying ⁻¹' closure {ξ} :=
    ⟨W, W.isOpen, hxW, fun y hy => (hW y hy.1).mp hy.2⟩
  unfold a3b4_multiplicity
  rw [Finset.sum_eq_single ξ]
  · exact if_pos hlocal
  · intro η hη hne
    have hn : ¬ ∃ U : Set (ComplexPoint (Over.mk q)), IsOpen U ∧ x ∈ U ∧
        U ∩ a3b4_cycleSupport q γ ⊆ Point.underlying ⁻¹' closure {η} := by
      rintro ⟨U, _, hxU, hU⟩
      exact hother η ((a3b2_support_finite γ).mem_toFinset.mp hη) hne (hU ⟨hxU, hxS⟩)
    exact if_neg hn
  · intro hnot
    exact (hnot ((a3b2_support_finite γ).mem_toFinset.mpr hξ)).elim

end HodgeLean.Adapters
