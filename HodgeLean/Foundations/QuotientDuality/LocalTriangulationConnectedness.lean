import HodgeLean.Foundations.Program.SchoenTransferQ2a1
import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs

/-! Connected finite triangulations have actual path-connected underlying spaces. -/
noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite-polyhedron local contractibility identifies connectedness with path connectedness.
Source: Hatcher, Algebraic Topology, Appendix A, local topology of polyhedra. -/
theorem triangulated_pathConnected (X : TopCat.{0}) [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) : PathConnectedSpace X := by
  letI : ConnectedSpace K.space :=
    eK.symm.surjective.connectedSpace eK.symm.continuous
  letI := HodgeLean.Foundations.Program.s4_q2a1_polyhedron a K hK
  letI : PathConnectedSpace K.space := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  exact eK.surjective.pathConnectedSpace eK.continuous

#print axioms triangulated_pathConnected
end HodgeLean.Foundations.QuotientDuality
