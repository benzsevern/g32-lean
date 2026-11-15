import HodgeLean.Adapters.NormalConeB4aClassComponentChartsLocal
import HodgeLean.Adapters.NormalConeB4aClassComponentNeighborhood

/-! # Holomorphic charts off the regular boundary

Route: the boundary complement isolates one smooth component of exact
codimension. Shrink its normal chart to exclude all other components.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- Outside the explicit higher-codimension boundary, the entire cycle support
has holomorphic flattening charts with `c` normal coordinates. -/
theorem a3b4a_classRegularBoundary_charts
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [Smooth q]
    [QuasiCompact q] [IsSeparated q] (γ : AlgebraicCycle Z ℚ) (c : ℕ)
    (hc : ∀ ξ ∈ γ.support, (c : ℕ∞) ≤ Order.coheight ξ)
    (x : ComplexPoint (Over.mk q)) (hx : x ∈ a3b4_cycleSupport q γ)
    (hxB : x.underlying ∉ a3b4a_classRegularBoundary q γ c) :
    ∃ (r : ℕ) (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
      ((Fin r → ℂ) × (Fin c → ℂ))),
      x ∈ e.source ∧ a3b4_IsHolChart q e ∧
      ∀ y ∈ e.source, y ∈ a3b4_cycleSupport q γ ↔ (e y).2 = 0 := by
  letI : Smooth (Over.mk q).hom := ‹Smooth q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  obtain ⟨ξ, hξ, hcξ, hxξ, hreg, hother⟩ :=
    a3b4a_classRegularBoundary_unique_component q γ c hc x.underlying hx hxB
  obtain ⟨r, e, hxe, he, hflat⟩ :=
    a3b4a_classComponent_exists_holomorphic_flattening_local (Over.mk q) c ξ hcξ x hxξ hreg
  obtain ⟨W, hW, hxW, hsupport⟩ := a3b4a_classSupport_local_eq_component
    q γ ξ hξ x hother ⟨e.source, e.open_source⟩ hxe
  refine ⟨r, e.restrOpen W W.isOpen, ⟨hxe, hxW⟩, ?_, ?_⟩
  · constructor
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.1 j)
    · intro j
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk q))
        (fun _ h => h.1) (he.2 j)
  · intro y hy
    exact (hsupport y hy.2).trans (hflat y hy.1)

end HodgeLean.Adapters
