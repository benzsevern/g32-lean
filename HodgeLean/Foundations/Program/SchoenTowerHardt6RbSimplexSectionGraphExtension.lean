import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexSectionExtension
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSectionClosureGraph

/-! Bounded root sections extend over geometric simplices with their actual Boolean graphs. -/
noncomputable section

set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_simplex_section_graph_extension {n : ℕ}
    (s : Finset (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContinuousOn f (intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))))
    (l u : ℝ) (hbound : ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))), f x ∈ Set.Icc l u)
    (P : EuclideanSpace ℝ (Fin n) × ℝ → ℝ)
    (hP : ContinuousOn P (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) ×ˢ Set.univ))
    (hroot : ∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))), P (x, f x) = 0)
    (hspec : ∀ a ∈ convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))), ∃ p : Polynomial ℝ,
      p ≠ 0 ∧ ∀ t, P (a, t) = p.eval t)
    (G : s2v_t11b_Formula (n + 1))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
      (∀ i, z i.succ = x.val i) ∧ z 0 = f x.val) :
    ∃ g : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))) → ℝ, Continuous g ∧
      (∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n)))),
        g ⟨x.val, intrinsicInterior_subset x.property⟩ = f x.val) ∧
      ∃ H : s2v_t11b_Formula (n + 1), H.realize = closure G.realize ∧
        ∀ z, z ∈ H.realize ↔ ∃ a : convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))),
          (∀ i, z i.succ = a.val i) ∧ z 0 = g a := by
  obtain ⟨g, hg, hagree, hgraph⟩ := s2v_hardt6rb_simplex_section_extension s f hf l u hbound P hP hroot hspec
  have hclosure := (s2v_hardt6rb_open_hull_topology s).1
  let e := Homeomorph.setCongr hclosure
  let g₀ : closure (intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))) → ℝ := fun a => g (e a)
  have hgraph₀ : ∀ a : closure (intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))), ∀ t : ℝ,
      (a.val, t) ∈ closure ((fun x => (x, f x)) '' intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))) ↔
        t = g₀ a := fun a t => hgraph (e a) t
  obtain ⟨H, hHclosure, hH⟩ := s2v_hardt6rb_section_closure_graph
    (intrinsicInterior ℝ (convexHull ℝ (↑s : Set (EuclideanSpace ℝ (Fin n))))) f g₀ hgraph₀ G hG
  refine ⟨g, hg, hagree, H, hHclosure, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha, ht⟩ := (hH z).mp hz
    exact ⟨e a, ha, ht⟩
  · rintro ⟨a, ha, ht⟩
    apply (hH z).mpr
    exact ⟨e.symm a, ha, by simpa only [g₀, e.apply_symm_apply] using ht⟩

end HodgeLean.Foundations.Program
