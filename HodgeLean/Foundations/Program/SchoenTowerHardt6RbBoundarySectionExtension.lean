import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundaryPolynomialFiber
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundedGraphClosure
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCompactGraphSection

/-! Continuous extension of bounded root sections through nondegenerate boundary fibers. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_bounded_polynomial_section_extension {E : Type*} [MetricSpace E]
    (C : Set E) (hC : IsCompact (closure C)) (f : E → ℝ) (hf : ContinuousOn f C)
    (l u : ℝ) (hbound : ∀ x ∈ C, f x ∈ Set.Icc l u)
    (hlocal : ∀ a ∈ closure C, ∀ ε : ℝ, 0 < ε → IsPreconnected (C ∩ Metric.ball a ε))
    (P : E × ℝ → ℝ) (hP : ContinuousOn P (closure C ×ˢ Set.univ))
    (hroot : ∀ x ∈ C, P (x, f x) = 0)
    (hspec : ∀ a ∈ closure C, ∃ p : Polynomial ℝ, p ≠ 0 ∧ ∀ t, P (a, t) = p.eval t) :
    ∃ g : closure C → ℝ, Continuous g ∧
      (∀ x : C, g ⟨x.val, subset_closure x.property⟩ = f x.val) ∧
      (∀ a : closure C, ∀ t : ℝ,
        (a.val, t) ∈ closure ((fun x => (x, f x)) '' C) ↔ t = g a) := by
  obtain ⟨hcompact, hproj⟩ := s2v_hardt6rb_bounded_graph_closure C hC f l u hbound
  have hunique : ∀ a ∈ closure C,
      Set.Subsingleton {t : ℝ | (a, t) ∈ closure ((fun x => (x, f x)) '' C)} := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := hspec a ha
    exact s2v_hardt6rb_polynomial_boundary_fiber_unique C f hf a (hlocal a ha) P hP hroot p hp hpa
  obtain ⟨g, hg, hgraph⟩ := s2v_hardt6rb_compact_graph_section (closure C)
    (closure ((fun x => (x, f x)) '' C)) hcompact hproj hunique
  refine ⟨g, hg, ?_, hgraph⟩
  intro x
  exact ((hgraph ⟨x.val, subset_closure x.property⟩ (f x.val)).mp
    (subset_closure ⟨x.val, x.property, rfl⟩)).symm

end HodgeLean.Foundations.Program
