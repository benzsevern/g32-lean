import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBoundarySectionExtension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenHullTopology

/-! Bounded root sections on intrinsic simplex interiors extend over their actual geometric hulls. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_section_extension {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (f : E → ℝ)
    (hf : ContinuousOn f (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))))
    (l u : ℝ) (hbound : ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)), f x ∈ Set.Icc l u)
    (P : E × ℝ → ℝ) (hP : ContinuousOn P (convexHull ℝ (↑s : Set E) ×ˢ Set.univ))
    (hroot : ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)), P (x, f x) = 0)
    (hspec : ∀ a ∈ convexHull ℝ (↑s : Set E), ∃ p : Polynomial ℝ,
      p ≠ 0 ∧ ∀ t, P (a, t) = p.eval t) :
    ∃ g : convexHull ℝ (↑s : Set E) → ℝ, Continuous g ∧
      (∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)),
        g ⟨x.val, intrinsicInterior_subset x.property⟩ = f x.val) ∧
      (∀ a : convexHull ℝ (↑s : Set E), ∀ t : ℝ,
        (a.val, t) ∈ closure ((fun x => (x, f x)) ''
          intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) ↔ t = g a) := by
  obtain ⟨hclosure, hlocal⟩ := s2v_hardt6rb_open_hull_topology s
  have hcompact : IsCompact (closure (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)))) := by
    rw [hclosure]
    exact s.finite_toSet.isCompact_convexHull ℝ
  obtain ⟨g, hg, hagree, hgraph⟩ := s2v_hardt6rb_bounded_polynomial_section_extension
    (intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))) hcompact f hf l u hbound
    (fun a _ ε _ => hlocal a ε) P (by simpa only [hclosure] using hP) hroot
    (by simpa only [hclosure] using hspec)
  let e := Homeomorph.setCongr hclosure.symm
  refine ⟨fun x => g (e x), hg.comp e.continuous, ?_, ?_⟩
  · intro x
    exact hagree x
  · intro a t
    exact hgraph (e a) t

end HodgeLean.Foundations.Program
