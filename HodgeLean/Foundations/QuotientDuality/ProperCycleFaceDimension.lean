import HodgeLean.Foundations.QuotientDuality.ProperCycleFaceVectorChart
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Dimensions of the actual logarithmic face coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual logarithmic-coordinate kernel has one fewer real dimension than its vertex index set.
Source: Axler, Linear Algebra Done Right, third edition, theorem 3.22, dimension of a kernel and range.
HC no distance; AV milestone no distance. -/
lemma properCycle_log_tangent_finrank {ι : Type} [Fintype ι] (j : ι) :
    Module.finrank ℝ (properCycle_log_tangent j) + 1 = Fintype.card ι := by
  let f : (ι → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  have hf : Function.Surjective f := fun r => ⟨fun _ => r, rfl⟩
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, Module.finrank_self, Module.finrank_pi] at h
  exact (Nat.add_comm _ _).trans h

/-- The selected positive-face chart has the expected real dimension.
Source: Munkres, Elements of Algebraic Topology, section 2, dimension of a simplex.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_vector_finrank {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (j : S) :
    Module.finrank ℝ (properCycle_log_tangent j) + 1 = S.card := by
  simpa only [Fintype.card_coe] using properCycle_log_tangent_finrank j

/-- Selecting a geometric face among a containing finite vertex set preserves its actual cardinality.
Source: Munkres, Elements of Algebraic Topology, section 2, vertex sets of faces.
HC no distance; AV milestone no distance. -/
lemma properCycle_selected_vertex_card {E : Type} [DecidableEq E]
    (V s : Finset E) (hsV : s ⊆ V) :
    (Finset.univ.filter (fun a : V => a.val ∈ s)).card = s.card := by
  let T : Finset V := Finset.univ.filter (fun a => a.val ∈ s)
  let e : T ≃ s :=
    { toFun := fun a => ⟨a.val.val, (Finset.mem_filter.mp a.property).2⟩
      invFun := fun a => ⟨⟨a.val, hsV a.property⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

/-- The vector factor used by the geometric-complex chart has real dimension equal to the face dimension.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric dimensions.
HC no distance; AV milestone no distance. -/
lemma properCycle_selected_face_vector_finrank {E : Type} [DecidableEq E]
    (V s : Finset E) (hsV : s ⊆ V)
    (j : Finset.univ.filter (fun a : V => a.val ∈ s)) :
    Module.finrank ℝ (properCycle_log_tangent j) + 1 = s.card := by
  exact (properCycle_face_vector_finrank _ j).trans (properCycle_selected_vertex_card V s hsV)

end HodgeLean.Foundations.QuotientDuality
