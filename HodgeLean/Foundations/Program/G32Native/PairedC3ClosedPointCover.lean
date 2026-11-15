import Mathlib.Topology.JacobsonSpace

/-! # Passing from closed-point chart neighborhoods to an open cover -/
namespace HodgeLean.Foundations.Program.G32Native

/-- An open set containing all closed points of a closed subset of a
Jacobson space contains that subset.
Source: Hartshorne, Algebraic Geometry, II.3. -/
theorem paired_c3_closed_point_cover
    {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {Z U : Set X} (hZ : IsClosed Z) (hU : IsOpen U)
    (h : ∀ x ∈ Z, IsClosed ({x} : Set X) → x ∈ U) : Z ⊆ U := by
  intro x hx
  by_contra hxu
  obtain ⟨y, ⟨hyZ, hyU⟩, hy⟩ := nonempty_inter_closedPoints
    (Z := Z \ U) ⟨x, hx, hxu⟩ (hZ.inter hU.isClosed_compl).isLocallyClosed
  exact hyU (h y hyZ hy)

#print axioms paired_c3_closed_point_cover
end HodgeLean.Foundations.Program.G32Native
