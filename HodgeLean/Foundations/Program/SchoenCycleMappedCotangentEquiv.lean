import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Algebra.Equiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Algebra coordinates identify the actual ideal cotangent modules through their induced quotient maps.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8. -/
def s2e_mapped_ideal_cotangent_equiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (I : Ideal A) (e : A ≃ₐ[R] B) :
    I.Cotangent ≃ₗ[R] (I.map e.toRingHom).Cotangent := by
  let J := I.map e.toRingHom
  have hf : I ≤ J.comap e := fun _ ha => Ideal.mem_map_of_mem e.toRingHom ha
  have hg : J ≤ I.comap e.symm := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hb
    change e.symm (e a) ∈ I
    rwa [e.symm_apply_apply]
  let f := Ideal.mapCotangent I J e.toAlgHom hf
  let g := Ideal.mapCotangent J I e.symm.toAlgHom hg
  exact
    { f with
      invFun := g
      left_inv := fun x => by
        obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
        change I.toCotangent ⟨e.symm (e x.val), _⟩ = I.toCotangent x
        congr 1
        exact Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => by
        obtain ⟨y, rfl⟩ := J.toCotangent_surjective y
        change J.toCotangent ⟨e (e.symm y.val), _⟩ = J.toCotangent y
        congr 1
        exact Subtype.ext (e.apply_symm_apply y.val) }

#print axioms s2e_mapped_ideal_cotangent_equiv
end HodgeLean.Foundations.Program
