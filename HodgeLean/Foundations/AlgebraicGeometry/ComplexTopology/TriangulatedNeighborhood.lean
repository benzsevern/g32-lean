import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Polyhedron
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.NeighborhoodTransfer

/-! Neighborhood bases supplied by a finite polyhedron model.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open Topology TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology

lemma basis_of_triangulated_neighborhood {S : Type*} [TopologicalSpace S]
    (T : Set S) (x : S) (hxT : x ∈ T) (hT : T ∈ nhds x)
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (h : T ≃ₜ K.space)
    (U : Opens S) (hxU : x ∈ U) :
    ∃ V : Opens S, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  apply basis_at_of_neighborhood_subtype T x hxT hT _ U hxU
  intro y O hyO
  let O' : Opens K.space := ⟨h.symm ⁻¹' O, O.isOpen.preimage h.symm.continuous⟩
  obtain ⟨V, hV, hyV, hVO, hcV⟩ :=
    polyhedron_open_basis n K hK (h y) O' (O'.isOpen.mem_nhds (by simpa [O'] using hyO))
  let W : Opens T := ⟨h ⁻¹' V, hV.preimage h.continuous⟩
  refine ⟨W, hyV, (h.sets rfl).contractibleSpace_iff.mpr hcV, ?_⟩
  intro z hz
  have hzO := hVO hz
  simpa [O'] using hzO

end HodgeLean.Foundations.ComplexTopology
