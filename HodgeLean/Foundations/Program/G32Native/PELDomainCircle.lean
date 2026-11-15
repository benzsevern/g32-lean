import HodgeLean.Foundations.Program.G32Native.PELDomainHodge
import HodgeLean.Foundations.Program.G32Native.PELPeriodConnectedCircle

noncomputable section
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The full Hodge circle in reference matrix coordinates. -/
theorem pelDomain_circle_matrix (R : PELSplitReference) (z : PELSplitDomain R) (c : Circle) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ R.basis)
      (Algebra.TensorProduct.basis ℂ R.basis)
      (g2_circleAction (pelDomainPieces R z) (pelDomainPieces_isInternal R z) c) =
      ((c : ℂ).re : ℂ) • 1 - ((c : ℂ).im : ℂ) • z.J.map (algebraMap ℝ ℂ) := by
  have he : g2_circleAction (pelDomainPieces R z) (pelDomainPieces_isInternal R z) c =
      ((c : ℂ).re : ℂ) • LinearMap.id - ((c : ℂ).im : ℂ) • pelDomainOperator R z := by
    apply linearMap_ext_of_isInternal (pelDomainPieces_isInternal R z)
    intro pq x hx
    by_cases hp : pq = (1, 0)
    · subst pq
      rw [g2_circleAction_apply_of_mem _ _ c hx]
      have hx := Module.End.mem_eigenspace_iff.mp
        (show x ∈ Module.End.eigenspace (pelDomainOperator R z) (-Complex.I) from hx)
      simp only [sub_zero, zpow_one, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, hx, smul_smul]
      rw [← sub_smul]
      congr 1
      apply Complex.ext <;> simp
    · by_cases hq : pq = (0, 1)
      · subst pq
        rw [g2_circleAction_apply_of_mem _ _ c hx]
        have hx := Module.End.mem_eigenspace_iff.mp
          (show x ∈ Module.End.eigenspace (pelDomainOperator R z) Complex.I from hx)
        simp only [show (0 : ℤ) - 1 = -1 by rfl, zpow_neg_one,
          LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hx, smul_smul]
        rw [← sub_smul]
        congr 1
        rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
        apply Complex.ext <;> simp
      · have hx0 : x = 0 := by
          simpa only [pelDomainPieces, if_neg hp, if_neg hq, Submodule.mem_bot] using hx
        subst x
        simp only [map_zero]
  rw [he, map_sub, map_smul, map_smul, LinearMap.toMatrix_id]
  simp only [pelDomainOperator, LinearMap.toMatrix_toLin]

/-- The period operator occurs at negative i on the Hodge circle. -/
theorem pelDomain_period_mem (R : PELSplitReference) (z : PELSplitDomain R) :
    pelPeriodMatrix R z ∈ pelDomainHodgeGroup R z := by
  apply g2_circleImage_subset_hodgeGroup (pelDomainPieces R z)
    (pelDomainPieces_isInternal R z) R.basis
  let c : Circle := ⟨-Complex.I, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_neg, Complex.norm_I]⟩
  refine ⟨c, ?_⟩
  rw [pelDomain_circle_matrix R z c]
  dsimp only [c]
  simp only [Complex.neg_re, Complex.I_re, neg_zero, Complex.ofReal_zero, zero_smul,
    Complex.neg_im, Complex.I_im, Complex.ofReal_neg, Complex.ofReal_one,
    neg_smul, one_smul, sub_neg_eq_add, zero_add]
  rfl

#print axioms pelDomain_circle_matrix
#print axioms pelDomain_period_mem
end HodgeLean.Foundations.Program.GeneralTypeIII
