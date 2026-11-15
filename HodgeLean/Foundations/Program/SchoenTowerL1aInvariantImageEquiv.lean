import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-! # Actual invariant-image algebra identifications

Implication from the actual injective invariant-image section map to its
coefficient-algebra identification with the actual fixed subalgebra.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An injective section algebra map with exactly the invariant image identifies
its source algebra with the actual fixed subalgebra, retaining that map.
Source: Stacks Project, tag 04A9, invariant section rings. -/
def s2v_l1a_invariantImageEquiv
    {K B D G : Type*} [CommRing K] [CommRing B] [CommRing D]
    [Algebra K B] [Algebra K D] [Group G] [MulSemiringAction G B]
    [SMulCommClass G K B] (q : D →ₐ[K] B) (hq : Function.Injective q)
    (himage : ∀ b : B, b ∈ Set.range q ↔ ∀ g : G, g • b = b) :
    D ≃ₐ[K] FixedPoints.subalgebra K B G := by
  let q' : D →ₐ[K] FixedPoints.subalgebra K B G := q.codRestrict _ (by
    intro d
    exact (himage (q d)).mp ⟨d, rfl⟩)
  apply AlgEquiv.ofBijective q'
  constructor
  · intro d e h
    exact hq (congrArg Subtype.val h)
  · intro b
    obtain ⟨d, hd⟩ := (himage b.val).mpr b.property
    exact ⟨d, Subtype.ext hd⟩

end HodgeLean.Foundations.Program
