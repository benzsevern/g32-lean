import HodgeLean.Foundations.Program.SchoenCycleInverseIndexedInvariants

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Inverse indexing of all stabilizer invariants retains the ambient value of each invariant function.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_inverse_indexed_invariant_val
    {k R G : Type*} [CommRing k] [CommRing R] [Algebra k R] [Group G]
    (α : G → (R →ₐ[k] R))
    (x : (⨅ g, AlgHom.equalizer (α g) (AlgHom.id k R) : Subalgebra k R)) :
    (s2e_inverse_indexed_invariant_equiv α x).val = x.val := rfl

#print axioms s2e_inverse_indexed_invariant_val
end HodgeLean.Foundations.Program
