import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.EuclideanTruncation
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.TriangulatedNeighborhood

/-! Basis transfer from a triangulated Euclidean truncation.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology

lemma basis_of_triangulated_truncation {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (x : S) {r : ℝ} (hr : 0 < r)
    {d : ℕ} (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d)))
    (hK : K.faces.Finite) (h : ↥(S ∩ Metric.closedBall x.val r) ≃ₜ K.space)
    (U : Opens S) (hxU : x ∈ U) :
    ∃ V : Opens S, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  let T : Set S := Subtype.val ⁻¹' Metric.closedBall x.val r
  have hxT : x ∈ T := Metric.mem_closedBall_self hr.le
  have hT : T ∈ nhds x := continuous_subtype_val.continuousAt.preimage_mem_nhds
    (Metric.closedBall_mem_nhds _ hr)
  let e : T ≃ₜ ↥(S ∩ Metric.closedBall x.val r) :=
    { toFun := fun y => ⟨y.val.val, y.val.property, y.property⟩
      invFun := fun y => ⟨⟨y.val, y.property.1⟩, y.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact basis_of_triangulated_neighborhood T x hxT hT K hK (e.trans h) U hxU

end HodgeLean.Foundations.ComplexTopology
