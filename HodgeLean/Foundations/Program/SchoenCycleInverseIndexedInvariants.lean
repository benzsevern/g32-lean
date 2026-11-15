import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Indexing all stabilizer pullbacks by inverses retains the entire invariant algebra and its ambient function values.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_inverse_indexed_invariant_equiv
    {k R G : Type*} [CommRing k] [CommRing R] [Algebra k R] [Group G]
    (α : G → (R →ₐ[k] R)) :
    (⨅ g, AlgHom.equalizer (α g) (AlgHom.id k R) : Subalgebra k R) ≃ₐ[k]
      (⨅ g, AlgHom.equalizer (α g⁻¹) (AlgHom.id k R) : Subalgebra k R) := by
  apply Subalgebra.equivOfEq
  ext r
  simp only [Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
  constructor
  · intro h g
    exact h g⁻¹
  · intro h g
    simpa only [inv_inv] using h g⁻¹

#print axioms s2e_inverse_indexed_invariant_equiv
end HodgeLean.Foundations.Program
