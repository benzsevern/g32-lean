import Mathlib.Topology.JacobsonSpace

/-! # Detection of open neighbourhoods at closed points -/
namespace HodgeLean.Foundations.Program

/-- An open subset of a Jacobson space containing every closed point is the whole space.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.3 and II.8. -/
theorem s2e_open_eq_top_of_contains_closed_points
    {X : Type*} [TopologicalSpace X] [JacobsonSpace X]
    (U : TopologicalSpace.Opens X)
    (h : ∀ x : X, IsClosed ({x} : Set X) → x ∈ U) : U = ⊤ := by
  apply top_unique
  intro x _
  by_contra hx
  obtain ⟨p, hp, hc⟩ := (jacobsonSpace_iff_locallyClosed.mp inferInstance)
    (U : Set X)ᶜ ⟨x, hx⟩ U.isOpen.isClosed_compl.isLocallyClosed
  exact hp (h p hc)

end HodgeLean.Foundations.Program
