import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Equivariant invariant coordinates retain the actual ambient algebra map on every invariant element.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_intertwining_invariant_coordinates_val
    {k A B G : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (a : G → A →ₐ[k] A) (b : G → B →ₐ[k] B)
    (h : ∀ g, (b g).comp e.toAlgHom = e.toAlgHom.comp (a g))
    (x : (⨅ g, AlgHom.equalizer (a g) (AlgHom.id k A) : Subalgebra k A)) :
    (s2e_intertwining_invariant_algebras_equiv e a b h x).val = e x.val := rfl

#print axioms s2e_intertwining_invariant_coordinates_val

/-- Inverse invariant coordinates retain the inverse ambient algebra map on every invariant element.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_intertwining_invariant_coordinates_symm_val
    {k A B G : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (a : G → A →ₐ[k] A) (b : G → B →ₐ[k] B)
    (h : ∀ g, (b g).comp e.toAlgHom = e.toAlgHom.comp (a g))
    (x : (⨅ g, AlgHom.equalizer (b g) (AlgHom.id k B) : Subalgebra k B)) :
    ((s2e_intertwining_invariant_algebras_equiv e a b h).symm x).val = e.symm x.val := by
  let D := s2e_intertwining_invariant_algebras_equiv e a b h
  apply e.injective
  rw [e.apply_symm_apply]
  exact (s2e_intertwining_invariant_coordinates_val e a b h (D.symm x)).symm.trans
    (congrArg Subtype.val (D.apply_symm_apply x))

#print axioms s2e_intertwining_invariant_coordinates_symm_val
end HodgeLean.Foundations.Program
