import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSimplexSectionGraphExtension
import Mathlib.Topology.Algebra.MvPolynomial

/-! Polynomial families remain continuous after changing their base coordinates. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_polynomial_family_continuous {E σ : Type*} [TopologicalSpace E]
    (C : Set E) (k : E → σ → ℝ) (hk : ContinuousOn k C)
    (Q : Polynomial (MvPolynomial σ ℝ)) :
    ContinuousOn (fun z : E × ℝ => Q.eval₂ (MvPolynomial.eval (k z.1)) z.2)
      (C ×ˢ Set.univ) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    ext z
    exact Polynomial.eval₂_add _ _
  | monomial d p =>
    simp only [Polynomial.eval₂_monomial]
    have hbase : ContinuousOn (fun z : E × ℝ => k z.1) (C ×ˢ Set.univ) :=
      hk.comp continuous_fst.continuousOn (fun _ hz => hz.1)
    exact ((MvPolynomial.continuous_eval p).comp_continuousOn hbase).mul
      (continuous_snd.continuousOn.pow d)

end HodgeLean.Foundations.Program
