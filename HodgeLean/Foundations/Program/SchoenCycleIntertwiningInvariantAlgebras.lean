import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Multiplicative invariant comparison through equivariant coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Equivariant algebra coordinates identify simultaneous invariant subalgebras with their actual multiplication.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_intertwining_invariant_algebras_equiv
    {k A B G : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (a : G → A →ₐ[k] A) (b : G → B →ₐ[k] B)
    (h : ∀ g, (b g).comp e.toAlgHom = e.toAlgHom.comp (a g)) :
    (⨅ g, AlgHom.equalizer (a g) (AlgHom.id k A) : Subalgebra k A) ≃ₐ[k]
      (⨅ g, AlgHom.equalizer (b g) (AlgHom.id k B) : Subalgebra k B) := by
  let F : Subalgebra k A := ⨅ g, AlgHom.equalizer (a g) (AlgHom.id k A)
  let K : Subalgebra k B := ⨅ g, AlgHom.equalizer (b g) (AlgHom.id k B)
  have hmem (x : F) : e x.val ∈ K := by
    simp only [K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    intro g
    have hx := x.property
    simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply] at hx
    have he := DFunLike.congr_fun (h g) x.val
    change b g (e x.val) = e (a g x.val) at he
    rw [hx g] at he
    exact he
  let f : F →ₐ[k] K := (e.toAlgHom.comp F.val).codRestrict K hmem
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hxy)
  · intro y
    have hy := y.property
    simp only [K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply] at hy
    have hx : e.symm y.val ∈ F := by
      simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
      intro g
      apply e.injective
      have he := DFunLike.congr_fun (h g) (e.symm y.val)
      change b g (e (e.symm y.val)) = e (a g (e.symm y.val)) at he
      rw [e.apply_symm_apply, hy g] at he
      simpa only [e.apply_symm_apply] using he.symm
    exact ⟨⟨e.symm y.val, hx⟩, Subtype.ext (e.apply_symm_apply y.val)⟩

#print axioms s2e_intertwining_invariant_algebras_equiv
end HodgeLean.Foundations.Program
