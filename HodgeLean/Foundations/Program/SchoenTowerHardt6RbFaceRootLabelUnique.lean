import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexInteriorConnected
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Strict root ordering on an intrinsic face determines every whole-face restriction label uniquely. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_root_label_unique {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hs : ∀ s x, x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
      StrictMono (fun a => f s a x))
    (s t : L.faces) (ρ σ : Fin (r s) → Fin (r t))
    (hρ : ∀ a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) → f s a x = f t (ρ a) x)
    (hσ : ∀ a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) → f s a x = f t (σ a) x) :
    ρ = σ := by
  obtain ⟨x, hx⟩ := (s2v_hardt6rb_simplex_interior_connected t.val
    (L.nonempty_of_mem_faces t.property)).nonempty
  funext a
  apply (hs t x hx).injective
  exact (hρ a x (intrinsicInterior_subset hx)).symm.trans (hσ a x (intrinsicInterior_subset hx))

end HodgeLean.Foundations.Program
