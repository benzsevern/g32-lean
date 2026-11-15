import HodgeLean.Foundations.Program.SchoenCycleFiniteSupportJets
import Mathlib.RingTheory.AdicCompletion.Algebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite comaximal support family separates the actual adic algebra into all its formal factors.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
def s2e_finite_support_adic_product_equiv
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A] [Fintype ι]
    (I : ι → Ideal A) (h : Pairwise (fun i j => IsCoprime (I i) (I j))) :
    AdicCompletion (⨅ i, I i) A ≃ₐ[k] (∀ i, AdicCompletion (I i) A) := by
  let K := ⨅ i, I i
  let q (L : Ideal A) (n : ℕ) : (A ⧸ (L ^ n • ⊤ : Ideal A)) ≃ₐ[k] A ⧸ L ^ n :=
    Ideal.quotientEquivAlgOfEq k (by simp)
  let e (n : ℕ) := ((q K n).trans (s2e_finite_support_jet_equiv (k := k) I h n)).trans
    (AlgEquiv.piCongrRight (fun i => (q (I i) n).symm))
  have heval (n : ℕ) (a : A) : e n (Ideal.Quotient.mk _ a) =
      (fun i => Ideal.Quotient.mk (I i ^ n • ⊤ : Ideal A) a) := by
    funext i
    apply (q (I i) n).injective
    change q (I i) n ((q (I i) n).symm
      (s2e_finite_support_jet_equiv (k := k) I h n (q K n (Ideal.Quotient.mk _ a)) i)) = _
    rw [AlgEquiv.apply_symm_apply]
    simp only [q, Ideal.quotientEquivAlgOfEq_mk]
    change ((Ideal.quotEquivOfEq _).trans
      (Ideal.quotientInfRingEquivPiQuotient (fun i => I i ^ n) _))
      (Ideal.Quotient.mk _ a) i = _
    simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    rfl
  have hcompat {m n : ℕ} (hmn : m ≤ n) (z : A ⧸ (K ^ n • ⊤ : Ideal A)) :
      (fun i => AdicCompletion.transitionMap (I i) A hmn (e n z i)) =
        e m (AdicCompletion.transitionMap K A hmn z) := by
    refine Quotient.inductionOn' z (fun a => ?_)
    change (fun i => AdicCompletion.transitionMap (I i) A hmn
      (e n (Ideal.Quotient.mk _ a) i)) = e m (Ideal.Quotient.mk _ a)
    rw [heval, heval]
    rfl
  let f : AdicCompletion K A →ₐ[k] (∀ i, AdicCompletion (I i) A) :=
    { toFun := fun x i => ⟨fun n => e n (x.val n) i, fun hmn =>
        (congrFun (hcompat hmn (x.val _)) i).trans
          (congrArg (fun z => e _ z i) (x.property hmn))⟩
      map_zero' := funext (fun i => AdicCompletion.ext (fun n => congrFun (e n).map_zero i))
      map_one' := funext (fun i => AdicCompletion.ext (fun n => congrFun (e n).map_one i))
      map_add' := fun x y => funext (fun i =>
        AdicCompletion.ext (fun n => congrFun ((e n).map_add _ _) i))
      map_mul' := fun x y => funext (fun i =>
        AdicCompletion.ext (fun n => congrFun ((e n).map_mul _ _) i))
      commutes' := fun r => funext (fun i =>
        AdicCompletion.ext (fun n => congrFun ((e n).commutes r) i)) }
  let g : (∀ i, AdicCompletion (I i) A) → AdicCompletion K A := fun y =>
    ⟨fun n => (e n).symm (fun i => (y i).val n), fun hmn => by
      apply (e _).injective
      rw [AlgEquiv.apply_symm_apply]
      have hh := hcompat hmn ((e _).symm (fun i => (y i).val _))
      rw [AlgEquiv.apply_symm_apply] at hh
      rw [← hh]
      funext i
      exact (y i).property hmn⟩
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply AdicCompletion.ext
    intro n
    exact (e n).symm_apply_apply (x.val n)
  · intro y
    funext i
    apply AdicCompletion.ext
    intro n
    exact congrFun ((e n).apply_symm_apply (fun i => (y i).val n)) i

#print axioms s2e_finite_support_adic_product_equiv
end HodgeLean.Foundations.Program
