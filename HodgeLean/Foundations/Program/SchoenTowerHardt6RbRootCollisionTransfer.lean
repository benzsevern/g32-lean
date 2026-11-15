import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceCover
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbOpenFaceContainment
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Shared root restriction labels preserve all collisions and strict comparisons on whole hulls. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_root_collision_transfer {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (r : L.faces → ℕ)
    (f g : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => f s a x))
    (hg : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => g s a x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρf : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      f s a x = f t (ρ s t hts a) x)
    (hρg : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      g s a x = g t (ρ s t hts a) x) :
    ∀ s a b x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) →
      (g s a x = g s b x ↔ f s a x = f s b x) ∧
      (g s a x < g s b x ↔ f s a x < f s b x) := by
  intro s a b x hx
  obtain ⟨T, hT, hxT⟩ := s2v_hardt6rb_mem_open_face L (L.convexHull_subset_space s.property hx)
  let t : L.faces := ⟨T, hT⟩
  have hts : t.val ⊆ s.val :=
    s2v_hardt6rb_open_face_subset_of_mem_face L T s.val hT s.property hxT hx
  have hxth : x ∈ convexHull ℝ (t.val : Set _) := intrinsicInterior_subset hxT
  rw [hρg s t hts a x hxth, hρg s t hts b x hxth,
    hρf s t hts a x hxth, hρf s t hts b x hxth]
  exact ⟨(hg t x hxT).injective.eq_iff.trans (hf t x hxT).injective.eq_iff.symm,
    (hg t x hxT).lt_iff_lt.trans (hf t x hxT).lt_iff_lt.symm⟩

end HodgeLean.Foundations.Program
