import Mathlib.Topology.JacobsonSpace

/-! # Extending residual chart coverage from closed points -/
namespace HodgeLean.Foundations.Program.G32Native

/-- An open set containing the closed points of a closed subset contains
the entire subset in a Jacobson space. This upgrades affine charts chosen
at complex points to a cover of the residual base. -/
theorem pairedC3_closed_subset_open_of_closed_points
    {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {D U : Set X} (hD : IsClosed D) (hU : IsOpen U)
    (h : ∀ x ∈ D, IsClosed ({x} : Set X) → x ∈ U) : D ⊆ U := by
  intro x hx
  by_contra hxu
  obtain ⟨y, ⟨hyD, hyU⟩, hy⟩ := nonempty_inter_closedPoints
    (Z := D ∩ Uᶜ) ⟨x, hx, hxu⟩ (hD.inter hU.isClosed_compl).isLocallyClosed
  exact hyU (h y hyD hy)

/-- A family of open chart neighbourhoods chosen at closed points covers
all of the residual base, including its nonclosed points. -/
theorem pairedC3_closed_subset_iUnion_of_closed_points
    {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    {D : Set X} (hD : IsClosed D) {ι : Sort*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i))
    (h : ∀ x ∈ D, IsClosed ({x} : Set X) → ∃ i, x ∈ U i) :
    D ⊆ ⋃ i, U i := by
  apply pairedC3_closed_subset_open_of_closed_points hD (isOpen_iUnion hU)
  intro x hx hc
  obtain ⟨i, hi⟩ := h x hx hc
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

#print axioms pairedC3_closed_subset_open_of_closed_points
#print axioms pairedC3_closed_subset_iUnion_of_closed_points
end HodgeLean.Foundations.Program.G32Native
