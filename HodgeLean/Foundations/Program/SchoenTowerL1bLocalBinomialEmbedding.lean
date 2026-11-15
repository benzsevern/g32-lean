import HodgeLean.Foundations.Program.SchoenTowerL1bLocalBinomialMinpoly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A specified root of the generating binomial determines a base-preserving
embedding of the entire covering field. -/
theorem s2v_l1b_local_binomial_embedding
    {F E L : Type*} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [FiniteDimensional F E] (t : E) (m : ℕ) (c : F) (hm : m ≠ 0)
    (hgen : IntermediateField.adjoin F ({t} : Set E) = ⊤)
    (hdegree : Module.finrank F E = m) (hpow : t ^ m = algebraMap F E c)
    (x : L) (hx : x ^ m = algebraMap F L c) :
    ∃ ψ : E →ₐ[F] L, ψ t = x := by
  have ht : IsIntegral F t := Algebra.IsIntegral.isIntegral t
  let f := minpoly F t
  let e : AdjoinRoot f ≃ₐ[F] E :=
    (IntermediateField.adjoinRootEquivAdjoin F ht).trans
      ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  have heroot : e (AdjoinRoot.root f) = t := by
    change ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
      ((IntermediateField.adjoinRootEquivAdjoin F ht) (AdjoinRoot.root f)) = t
    rw [IntermediateField.adjoinRootEquivAdjoin_apply_root]
    rfl
  have hroot : Polynomial.eval₂ (Algebra.ofId F L) x f = 0 := by
    change Polynomial.aeval x (minpoly F t) = 0
    rw [s2v_l1b_local_binomial_minpoly t m c hm hgen hdegree hpow]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hx, sub_self]
  let g := AdjoinRoot.liftAlgHom f (Algebra.ofId F L) x hroot
  refine ⟨g.comp e.symm.toAlgHom, ?_⟩
  change g (e.symm t) = x
  rw [← heroot, e.symm_apply_apply]
  exact AdjoinRoot.lift_root hroot

end HodgeLean.Foundations.Program
