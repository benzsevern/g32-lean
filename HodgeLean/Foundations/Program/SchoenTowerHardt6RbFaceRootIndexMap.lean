import HodgeLean.Foundations.Program.SchoenTowerHardt6RbConnectedRootLabel
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexInteriorConnected
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexInteriorDense
import Mathlib.Topology.DenseEmbedding

/-! Ordered root families induce monotone boundary index maps with exact whole-face agreement. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_root_index_map {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {r t : ℕ} (s : Finset E) (hs : s.Nonempty)
    (f : Fin r → convexHull ℝ (↑s : Set E) → ℝ)
    (g : Fin t → convexHull ℝ (↑s : Set E) → ℝ)
    (hf : ∀ i, Continuous (f i)) (hg : ∀ j, Continuous (g j))
    (horder : ∀ x, Monotone (fun i => f i x))
    (hstrict : ∀ x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set E)),
      StrictMono (fun j => g j ⟨x.val, intrinsicInterior_subset x.property⟩))
    (hcover : ∀ i (x : intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))), ∃ j,
      f i ⟨x.val, intrinsicInterior_subset x.property⟩ =
        g j ⟨x.val, intrinsicInterior_subset x.property⟩) :
    ∃ ρ : Fin r → Fin t, Monotone ρ ∧ ∀ i x, f i x = g (ρ i) x := by
  let U := intrinsicInterior ℝ (convexHull ℝ (↑s : Set E))
  have hc := s2v_hardt6rb_simplex_interior_connected s hs
  letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hc
  choose ρ hρ using fun i => s2v_hardt6rb_connected_root_label
    (fun x : U => f i ⟨x.val, intrinsicInterior_subset x.property⟩)
    (fun j (x : U) => g j ⟨x.val, intrinsicInterior_subset x.property⟩)
    ((hf i).comp (continuous_inclusion intrinsicInterior_subset))
    (fun j => (hg j).comp (continuous_inclusion intrinsicInterior_subset))
    (fun x => (hstrict x).injective) (hcover i)
  obtain ⟨x₀, hx₀⟩ := hc.nonempty
  refine ⟨ρ, ?_, ?_⟩
  · intro i j hij
    apply (hstrict ⟨x₀, hx₀⟩).le_iff_le.mp
    rw [← hρ i ⟨x₀, hx₀⟩, ← hρ j ⟨x₀, hx₀⟩]
    exact horder _ hij
  · intro i x
    exact (s2v_hardt6rb_simplex_interior_dense s).induction_on x
      (isClosed_eq (hf i) (hg (ρ i))) (hρ i)

end HodgeLean.Foundations.Program
