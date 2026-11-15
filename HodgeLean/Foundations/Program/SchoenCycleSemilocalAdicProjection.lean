import HodgeLean.Foundations.Program.SchoenCycleFiniteSupportAdicProjection
import HodgeLean.Foundations.Program.SchoenCycleFiniteSupportPowers
import HodgeLean.Foundations.Program.SchoenCycleAdicCofinalEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finite formal support factors identify every formal section through its canonical projection, including sections outside the original ring's image.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
theorem s2e_semilocal_adic_factor_projections
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A] [Fintype ι]
    (J : Ideal A) (I : ι → Ideal A)
    (h : Pairwise (fun i j => IsCoprime (I i) (I j)))
    (hJI : ∀ i, J ≤ I i) (hfg : (⨅ i, I i).FG)
    (hcover : ∀ P : Ideal A, P.IsPrime → J ≤ P → ∃ i, I i ≤ P) :
    ∃ E : AdicCompletion J A ≃ₐ[k] (∀ i, AdicCompletion (I i) A),
      ∀ (x : AdicCompletion J A) (i : ι), E x i =
        s2e_adic_algebra_map J (I i) (AlgHom.id k A)
          (fun n a ha => (Ideal.pow_right_mono (hJI i) n) ha) x := by
  let K := ⨅ i, I i
  have hJK : J ≤ K := le_iInf hJI
  obtain ⟨c, hc⟩ := s2e_support_intersection_power_le J I hfg hcover
  have hc' : K ^ (c + 1) ≤ J := (Ideal.pow_le_pow_right (Nat.le_succ c)).trans hc
  let F := s2e_adic_cofinal_equiv (k := k) K J hJK (c + 1) (by omega) hc'
  let P := s2e_finite_support_adic_product_equiv (k := k) I h
  refine ⟨F.symm.trans P, ?_⟩
  intro x i
  change P (F.symm x) i = _
  rw [s2e_finite_support_adic_product_projection]
  apply AdicCompletion.ext
  intro n
  change Ideal.quotientMapₐ (I i ^ n • ⊤ : Ideal A) (AlgHom.id k A) _
      (Ideal.quotientMapₐ (K ^ n • ⊤ : Ideal A) (AlgHom.id k A) _ (x.val n)) =
    Ideal.quotientMapₐ (I i ^ n • ⊤ : Ideal A) (AlgHom.id k A) _ (x.val n)
  refine Quotient.inductionOn' (x.val n) (fun a => ?_)
  rfl

end HodgeLean.Foundations.Program
