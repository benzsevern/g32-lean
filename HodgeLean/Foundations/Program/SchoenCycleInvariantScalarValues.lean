import HodgeLean.Foundations.Program.SchoenCycleInvariantScalarRestriction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Restriction to the prescribed scalar ring retains the actual ambient value of every simultaneous invariant element.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_restrict_scalars_val
    {k A B G : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    (α : G → B →ₐ[A] B)
    (x : (⨅ g, AlgHom.equalizer (α g) (AlgHom.id A B) : Subalgebra A B)) :
    (s2e_invariant_restrict_scalars_equiv (k := k) α x).val = x.val := rfl

#print axioms s2e_invariant_restrict_scalars_val
end HodgeLean.Foundations.Program
