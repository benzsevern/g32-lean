import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientAffineInterpolation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAffineHullAgreement
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexAffineOrder
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Coherent root values construct ambient affine source models agreeing on every nested face. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_affine_root_models {n : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (r : L.faces → ℕ)
    (f : (s : L.faces) → Fin (r s) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => f s a x))
    (ρ : ∀ s t : L.faces, t.val ⊆ s.val → Fin (r s) → Fin (r t))
    (hρ : ∀ s t hts a x, x ∈ convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))) →
      f s a x = f t (ρ s t hts a) x) :
    ∃ A : (s : L.faces) → Fin (r s) → (EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ),
      (∀ s a, Continuous (A s a)) ∧
      (∀ s a (x : s.val), A s a x.val = f s a x.val) ∧
      (∀ s x, x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => A s a x)) ∧
      (∀ s t hts a, Set.EqOn (A s a) (A t (ρ s t hts a))
        (convexHull ℝ (t.val : Set (EuclideanSpace ℝ (Fin n))))) := by
  classical
  choose A hA using fun (s : L.faces) (a : Fin (r s)) =>
    s2v_hardt6rb_ambient_affine_interpolation s.val (L.indep s.property) (fun x => f s a x.val)
  refine ⟨A, ?_, hA, ?_, ?_⟩
  · intro s a
    rw [(A s a).decomp]
    exact (A s a).linear.continuous_of_finiteDimensional.add continuous_const
  · intro s x hx a b hab
    change A s a x ≤ A s b x
    apply s2v_hardt6rb_simplex_affine_order s.val (A s a) (A s b) ?_ ?_ ?_ x hx
    · exact fun w => s2v_hardt6rb_affine_simplex_evaluation ((↑) : s.val → _) (A s a) w
    · exact fun w => s2v_hardt6rb_affine_simplex_evaluation ((↑) : s.val → _) (A s b) w
    · intro y hy
      rw [hA s a ⟨y, hy⟩, hA s b ⟨y, hy⟩]
      exact hm s y (subset_convexHull ℝ _ hy) hab
  · intro s t hts a
    apply s2v_hardt6rb_affine_hull_agreement t.val (A s a) (A t (ρ s t hts a))
    intro x hx
    rw [hA s a ⟨x, hts hx⟩, hA t (ρ s t hts a) ⟨x, hx⟩]
    exact hρ s t hts a x (subset_convexHull ℝ _ hx)

end HodgeLean.Foundations.Program
