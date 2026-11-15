import HodgeLean.Foundations.Program.SchoenTransferQ3LocalEquality

/-! Extend local normalization of the actual class across the algebraic boundary. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Local normalization outside a boundary of strict codimension gain gives
normalization of the original supported class everywhere it is tested. -/
theorem s4_q3_normalized_of_normalized_off_boundary
    {Z : Scheme.{0}} (q : Z ⟶ Spec ↧ℂ) [Smooth q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) (k : ℕ)
    (hc : ∀ p ∈ γ.support, (k : ℕ∞) ≤ Order.coheight p)
    (B : Closeds Z) (hBS : B ≤ a3b4a_classAlgebraicSupport q γ)
    (hBc : ∀ p ∈ B, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight p)
    (hcharts : ∀ x ∈ a3b4_cycleSupport q γ, x.underlying ∉ B →
      ∃ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
        ((Fin r → ℂ) × (Fin k → ℂ))), x ∈ e.source ∧ a3b4_IsHolChart q e ∧
        ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * k))
    (hnorm : ∀ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin k → ℂ)))
      (hS : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0)
      (x : ComplexPoint (Over.mk q)), x ∈ e.source → x ∈ a3b4_cycleSupport q γ →
      x.underlying ∉ B → a3b4_IsHolChart q e →
      ∃ (V : Set (ComplexPoint (Over.mk q))) (hV : V ⊆ e.source), IsOpen V ∧ x ∈ V ∧
        relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap V (a3b4_cycleSupport q γ)) β =
        a3b4_multiplicity q γ x • chartNormalProjectionCoclass (Fin r → ℂ) k e
          (a3b4_cycleSupport q γ) hS V hV) :
    a3b4_IsCycleClass q γ k β := by
  obtain ⟨β', hβ'⟩ := a3b4a_cycleClass_exists_of_codimension q γ k hc
  have heq : β = β' := by
    apply s4_q3_supported_eq_of_boundary_local_equality q γ k hc B hBS hBc β β'
    intro x hx hxB
    obtain ⟨r, e, hxe, he, hS⟩ := hcharts x hx hxB
    obtain ⟨V, hVe, hVo, hxV, hV⟩ := hnorm r e hS x hxe hx hxB he
    obtain ⟨V', hV'e, hV'o, hxV', hV'⟩ := hβ' r e hS x hxe hx he
    refine ⟨V ∩ V', hVo.inter hV'o, ⟨hxV, hxV'⟩, ?_⟩
    rw [map_sub,
      a3b4a_classLocal_normalization_mono e _ hS Set.inter_subset_left hVe β _ hV,
      a3b4a_classLocal_normalization_mono e _ hS Set.inter_subset_right hV'e β' _ hV',
      sub_self]
  rw [heq]
  exact hβ'

end HodgeLean.Foundations.Program
