import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A group of filtered algebra automorphisms acts on the actual adic algebra by its finite quotient maps.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_group_algebra_action
    {k A G : Type*} [CommRing k] [CommRing A] [Algebra k A] [Group G]
    (I : Ideal A) (α : G →* (A ≃ₐ[k] A))
    (h : ∀ (g : G) (n : ℕ) (a : A), a ∈ I ^ n → α g a ∈ I ^ n) :
    G →* (AdicCompletion I A ≃ₐ[k] AdicCompletion I A) := by
  let f (g : G) := s2e_adic_algebra_map I I (α g).toAlgHom (h g)
  have hmul (g t : G) (a : A) : α g (α t a) = α (g * t) a := by
    rw [map_mul, AlgEquiv.mul_apply]
  have hone (a : A) : α 1 a = a := by rw [map_one, AlgEquiv.one_apply]
  have hcomp (g t : G) (x : AdicCompletion I A) : f g (f t x) = f (g * t) x := by
    apply AdicCompletion.ext
    intro n
    change Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal A) (α g).toAlgHom _
        (Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal A) (α t).toAlgHom _ (x.val n)) =
      Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal A) (α (g * t)).toAlgHom _ (x.val n)
    refine Quotient.inductionOn' (x.val n) (fun a => ?_)
    change Ideal.Quotient.mk _ (α g (α t a)) = Ideal.Quotient.mk _ (α (g * t) a)
    rw [hmul]
  have hident (x : AdicCompletion I A) : f 1 x = x := by
    apply AdicCompletion.ext
    intro n
    change Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal A) (α 1).toAlgHom _ (x.val n) = x.val n
    refine Quotient.inductionOn' (x.val n) (fun a => ?_)
    change Ideal.Quotient.mk _ (α 1 a) = Ideal.Quotient.mk _ a
    rw [hone]
  let E (g : G) : AdicCompletion I A ≃ₐ[k] AdicCompletion I A :=
    { f g with
      invFun := f g⁻¹
      left_inv := fun x => by
        change f g⁻¹ (f g x) = x
        rw [hcomp, inv_mul_cancel, hident]
      right_inv := fun x => by
        change f g (f g⁻¹ x) = x
        rw [hcomp, mul_inv_cancel, hident] }
  exact
    { toFun := E
      map_one' := by
        apply AlgEquiv.ext
        intro x
        exact hident x
      map_mul' := fun g t => by
        apply AlgEquiv.ext
        intro x
        exact (hcomp g t x).symm }

end HodgeLean.Foundations.Program
