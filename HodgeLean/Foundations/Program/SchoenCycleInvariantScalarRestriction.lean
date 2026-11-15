import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Restricting scalars retains the actual simultaneous invariant algebra and every invariant element.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_invariant_restrict_scalars_equiv
    {k A B G : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    (α : G → B →ₐ[A] B) :
    (⨅ g, AlgHom.equalizer (α g) (AlgHom.id A B) : Subalgebra A B) ≃ₐ[k]
      (⨅ g, AlgHom.equalizer ((α g).restrictScalars k) (AlgHom.id k B) : Subalgebra k B) := by
  let F : Subalgebra A B := ⨅ g, AlgHom.equalizer (α g) (AlgHom.id A B)
  let K : Subalgebra k B := ⨅ g, AlgHom.equalizer ((α g).restrictScalars k) (AlgHom.id k B)
  let f : F →ₐ[k] K := (F.val.restrictScalars k).codRestrict K (fun x => by
    simp only [K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    intro g
    exact Algebra.mem_iInf.mp x.property g)
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (congrArg (fun z : K => z.val) h)
  · intro y
    have hy : y.val ∈ F := by
      simp only [F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
      intro g
      exact Algebra.mem_iInf.mp y.property g
    exact ⟨⟨y.val, hy⟩, Subtype.ext rfl⟩

end HodgeLean.Foundations.Program
