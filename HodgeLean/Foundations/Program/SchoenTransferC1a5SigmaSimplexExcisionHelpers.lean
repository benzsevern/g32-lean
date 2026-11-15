import HodgeLean.Foundations.Program.SchoenTransferC1a5SigmaExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5RealizedDeformationHelpers

/-! Singular excision for arbitrary families of literal realized simplices.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- An arbitrary family of positive-dimensional realized simplex attachments has integral relative comparison.
Source: Hatcher §2.1, Theorem 2.20, disjoint-union simplex collars. -/
lemma c1a5_sigma_realized_simplex_excision (I : Type) (n : ℕ) {B D : TopCat.{0}}
    (t : TopCat.of (Σ _ : I, SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet)) ⟶ B)
    (r : B ⟶ D) (b : TopCat.of (Σ _ : I, SSet.toTop.obj (Δ[n + 1] : SSet.{0})) ⟶ D)
    (sq : IsPushout t (c1a5_sigma_map (fun _ : I ↦
      SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι)) r b) :
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (c1a5_sigma_map (fun _ : I ↦
        SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι)))
      (TopCat.toSSet.map r) (TopCat.toSSet.map t) (TopCat.toSSet.map b) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
        exact congrArg TopCat.toSSet.map sq.w.symm)) := by
  generalize heq : c1a5_sigma_map (fun _ : I ↦
    SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι) = l at sq ⊢
  have hf : l = c1a5_sigma_map (fun _ : I ↦ c1a5_realized_boundary_to_collar n) ≫
      c1a5_sigma_map (fun _ : I ↦ c1a5_collar_to_realized_simplex n) := by
    rw [← heq, c1a5_sigma_map_comp]
    congr 1
    funext i
    exact (c1a5_realized_boundary_collar_factor n).symm
  clear heq
  subst l
  apply c1a5_sigma_collar_singular_excision
    (fun _ : I ↦ c1a5_realized_boundary_to_collar n)
    (fun _ : I ↦ c1a5_collar_to_realized_simplex n) t r b sq
    (fun _ ↦ c1a5_collar_to_realized_simplex_isOpenEmbedding n)
    (fun _ ↦ ?_) (fun _ ↦ ?_)
    (fun _ ↦ c1a5_collar_to_realized_boundary n)
    (fun _ ↦ c1a5_realized_boundary_collar_retract n)
    (fun _ ↦ c1a5_realized_boundary_collar_homotopy n)
    (fun _ ↦ c1a5_realized_boundary_collar_homotopy_fixed n)
  · rw [c1a5_realized_boundary_collar_factor]
    exact (c1a5_boundary_realization_isClosedEmbedding (n + 1)).injective
  · rw [c1a5_realized_boundary_collar_factor]
    exact (c1a5_boundary_realization_isClosedEmbedding (n + 1)).isClosed_range

end HodgeLean.Foundations.Program
