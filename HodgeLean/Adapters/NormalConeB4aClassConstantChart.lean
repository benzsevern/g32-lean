import HodgeLean.Adapters.NormalConeB4aClassRegularBoundaryCharts
import HodgeLean.Adapters.NormalConeB4aClassMultiplicity

/-! # Constant multiplicity charts on the regular support

Route: isolate a smooth component and restrict its normal chart to the
boundary complement. Every support point in the restricted chart belongs to
that same component alone.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- The regular support has normal charts on which its multiplicity is constant. -/
theorem a3b4a_classRegularBoundary_constantChart
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (x : ComplexPoint (Over.mk q)) (hx : x ∈ a3b4_cycleSupport q γ)
    (hxB : x.underlying ∉ a3b4a_classRegularBoundary q γ c) :
    ∃ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
      ((Fin r → ℂ) × (Fin c → ℂ))),
      x ∈ e.source ∧ a3b4_IsHolChart q e ∧
      (∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0) ∧
      (∀ y ∈ e.source, y.underlying ∉ a3b4a_classRegularBoundary q γ c) ∧
      (∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ →
        a3b4_multiplicity q γ y = a3b4_multiplicity q γ x) := by
  letI : Smooth (Over.mk q).hom := ‹Smooth q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  obtain ⟨ξ, hξ, hcξ, hxξ, hreg, hother⟩ :=
    a3b4a_classRegularBoundary_unique_component q γ c hc x.underlying hx hxB
  obtain ⟨r, e, hxe, he, hflat⟩ :=
    a3b4a_classComponent_exists_holomorphic_flattening_local (Over.mk q) c ξ hcξ x hxξ hreg
  obtain ⟨W, hW, hxW, hsupport⟩ := a3b4a_classSupport_local_eq_component
    q γ ξ hξ x hother ⟨e.source, e.open_source⟩ hxe
  let B : Closeds (ComplexPoint (Over.mk q)) :=
    (a3b4a_classRegularBoundary q γ c).preimage
      (ComplexPoint.continuous_underlying_to_zariski (Over.mk q))
  let V : Opens (ComplexPoint (Over.mk q)) := W ⊓ B.compl
  refine ⟨r, e.restrOpen V V.isOpen, ⟨hxe, hxW, hxB⟩, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.1 j)
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.2 j)
  · intro y hy
    exact (hsupport y hy.2.1).trans (hflat y hy.1)
  · intro y hy
    exact hy.2.2
  · intro y hy hyS
    have hyξ := (hsupport y hy.2.1).mp hyS
    obtain ⟨η, hη, _, _, _, hothers⟩ :=
      a3b4a_classRegularBoundary_unique_component q γ c hc y.underlying hyS hy.2.2
    have hηξ : η = ξ := by
      by_contra hne
      exact hothers ξ hξ (Ne.symm hne) hyξ
    subst η
    rw [a3b4a_classMultiplicity_eq_component q γ ξ hξ y hyξ hothers,
      a3b4a_classMultiplicity_eq_component q γ ξ hξ x hxξ hother]

end HodgeLean.Adapters
