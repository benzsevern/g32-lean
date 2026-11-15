import HodgeLean.Adapters.GagaMapsProofs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set
namespace HodgeLean.Foundations.Program

/-- Locally regular equations on complex points give a closed scheme carrier.
Source: Hartshorne, Algebraic Geometry, II, Section 2. -/
theorem b54_closed_carrier_of_local_equations (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X))
    (hlocal : ∀ p : ComplexPoint X, ∃ (U : X.left.Opens) (s : Set Γ(X.left, U)),
      p.underlying ∈ U ∧ ∀ q : ComplexPoint X, q.underlying ∈ U →
        (q ∈ Z ↔ q.underlying ∈ X.left.zeroLocus s)) :
    ∃ C : Set X.left, IsClosed C ∧ Z = Point.underlying ⁻¹' C := by
  refine ⟨closure (Point.underlying '' Z), isClosed_closure, ?_⟩
  ext p
  constructor
  · intro hp
    exact subset_closure ⟨p, hp, rfl⟩
  · intro hp
    obtain ⟨U, s, hpU, hs⟩ := hlocal p
    apply (hs p hpU).mpr
    apply closure_minimal ?_ (X.left.zeroLocus_isClosed s) hp
    rintro _ ⟨q, hq, rfl⟩
    by_cases hqU : q.underlying ∈ U
    · exact (hs q hqU).mp hq
    · rw [Scheme.mem_zeroLocus_iff]
      intro f hf hqf
      exact hqU (X.left.basicOpen_le f hqf)

end HodgeLean.Foundations.Program
