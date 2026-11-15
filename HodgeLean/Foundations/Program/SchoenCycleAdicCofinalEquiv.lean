import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Cofinal ideal powers give an algebra identification of their actual adic rings.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_adic_cofinal_equiv
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (I J : Ideal A) (hJI : J ≤ I) (c : ℕ) (hc : 1 ≤ c) (hIJ : I ^ c ≤ J) :
    AdicCompletion I A ≃ₐ[k] AdicCompletion J A := by
  have hpow (n : ℕ) : I ^ (c * n) ≤ J ^ n := by
    rw [pow_mul]
    exact Ideal.pow_right_mono hIJ n
  have hp (n : ℕ) : (I ^ (c * n) • ⊤ : Ideal A) ≤
      (J ^ n • ⊤ : Ideal A).comap (AlgHom.id k A) := by
    simpa using hpow n
  let q (n : ℕ) := Ideal.quotientMapₐ (J ^ n • ⊤ : Ideal A) (AlgHom.id k A) (hp n)
  have hcompat {m n : ℕ} (hmn : m ≤ n) (z : A ⧸ (I ^ (c * n) • ⊤ : Ideal A)) :
      AdicCompletion.transitionMap J A hmn (q n z) =
        q m (AdicCompletion.transitionMap I A (Nat.mul_le_mul_left c hmn) z) := by
    refine Quotient.inductionOn' z (fun a => ?_)
    rfl
  let f : AdicCompletion I A →ₐ[k] AdicCompletion J A :=
    { toFun := fun x => ⟨fun n => q n (x.val (c * n)), fun hmn =>
        (hcompat hmn (x.val _)).trans (congrArg (q _) (x.property _))⟩
      map_zero' := AdicCompletion.ext (fun n => (q n).map_zero)
      map_one' := AdicCompletion.ext (fun n => (q n).map_one)
      map_add' := fun x y => AdicCompletion.ext (fun n => (q n).map_add _ _)
      map_mul' := fun x y => AdicCompletion.ext (fun n => (q n).map_mul _ _)
      commutes' := fun r => AdicCompletion.ext (fun n => (q n).commutes r) }
  let g := s2e_adic_algebra_map J I (AlgHom.id k A)
    (fun n a ha => (Ideal.pow_right_mono hJI n) ha)
  have hnc (n : ℕ) : n ≤ c * n := by simpa using Nat.mul_le_mul_right n hc
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply AdicCompletion.ext
    intro n
    change Ideal.quotientMapₐ (I ^ n • ⊤ : Ideal A) (AlgHom.id k A) _
      (q n (x.val (c * n))) = x.val n
    rw [← x.property (hnc n)]
    refine Quotient.inductionOn' (x.val (c * n)) (fun a => ?_)
    rfl
  · intro y
    apply AdicCompletion.ext
    intro n
    change q n (Ideal.quotientMapₐ (I ^ (c * n) • ⊤ : Ideal A) (AlgHom.id k A) _
      (y.val (c * n))) = y.val n
    rw [← y.property (hnc n)]
    refine Quotient.inductionOn' (y.val (c * n)) (fun a => ?_)
    rfl

#print axioms s2e_adic_cofinal_equiv
end HodgeLean.Foundations.Program
