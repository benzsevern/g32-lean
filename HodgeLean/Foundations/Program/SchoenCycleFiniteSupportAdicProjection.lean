import HodgeLean.Foundations.Program.SchoenCycleFiniteSupportAdicProduct
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every formal factor projection is the canonical adic map on all formal sections.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
theorem s2e_finite_support_adic_product_projection
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A] [Fintype ι]
    (I : ι → Ideal A) (h : Pairwise (fun i j => IsCoprime (I i) (I j)))
    (x : AdicCompletion (⨅ i, I i) A) (i : ι) :
    s2e_finite_support_adic_product_equiv (k := k) I h x i =
      s2e_adic_algebra_map (⨅ j, I j) (I i) (AlgHom.id k A)
        (fun n a ha => (Ideal.pow_right_mono (iInf_le I i) n) ha) x := by
  apply AdicCompletion.ext
  intro n
  let q (L : Ideal A) : (A ⧸ (L ^ n • ⊤ : Ideal A)) ≃ₐ[k] A ⧸ L ^ n :=
    Ideal.quotientEquivAlgOfEq k (by simp)
  change (q (I i)).symm (s2e_finite_support_jet_equiv (k := k) I h n
    (q (⨅ j, I j) (x.val n)) i) =
      Ideal.quotientMapₐ (I i ^ n • ⊤ : Ideal A) (AlgHom.id k A) _ (x.val n)
  refine Quotient.inductionOn' (x.val n) (fun a => ?_)
  apply (q (I i)).injective
  rw [AlgEquiv.apply_symm_apply]
  simp only [q, Ideal.quotientEquivAlgOfEq_mk]
  change ((Ideal.quotEquivOfEq _).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun i => I i ^ n) _))
    (Ideal.Quotient.mk _ a) i = _
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

end HodgeLean.Foundations.Program
