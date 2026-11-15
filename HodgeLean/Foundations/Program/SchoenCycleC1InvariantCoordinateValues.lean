import HodgeLean.Foundations.Program.SchoenCycleIntertwiningInvariantAlgebras

/-! # Values under equivariant invariant algebra coordinates -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- The invariant algebra comparison uses the specified ambient coordinate
map on every invariant element. -/
theorem s2e_c1_intertwining_invariant_coordinates_val
    {k A B G : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (a : G → A →ₐ[k] A) (b : G → B →ₐ[k] B)
    (h : ∀ g, (b g).comp e.toAlgHom = e.toAlgHom.comp (a g))
    (z : (⨅ g, AlgHom.equalizer (a g) (AlgHom.id k A) : Subalgebra k A)) :
    (s2e_intertwining_invariant_algebras_equiv e a b h z).val = e z.val := by
  rfl

end HodgeLean.Foundations.Program
