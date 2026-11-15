import HodgeLean.Foundations.Curves.AbelTheorem.OrientedBasisIntegral

noncomputable section
open HodgeLean.Foundations.Program
open Manifold MeasureTheory
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem complex_integration_basis_change_positive (h : Module.finrank ℂ E = 1) :
    0 < (b3Rest_b h).det (b4c_residue_basis h) := by
  let L := b3Forms_lineEquiv h (b3Rest_e_ne_zero h)
  let T : E ≃L[ℂ] E := L.symm.trans (b4cov_lineEquiv h)
  have he : T (b3Rest_e h) = b4cov_lineEquiv h 1 := by
    have hL : L 1 = b3Rest_e h := by simp only [L, b3Forms_lineEquiv_apply, one_smul]
    change b4cov_lineEquiv h (L.symm (b3Rest_e h)) = _
    rw [← hL, L.symm_apply_apply]
  have hb : (b4c_residue_basis h : Fin 2 → E) = fun i => T (b3Rest_b h i) := by
    rw [b4c_residue_basis_coe]
    funext i
    fin_cases i
    · simpa [b3Rest_b, b3Forms_cplxBasis_zero] using he.symm
    · simpa [b3Rest_b, b3Forms_cplxBasis_one, map_smul, he] using
        map_smul (b4cov_lineEquiv h) Complex.I (1 : ℂ)
  have hd : (b3Rest_b h).det (b4c_residue_basis h) =
      LinearMap.det (T.toLinearEquiv.toLinearMap.restrictScalars ℝ) := by
    rw [hb]
    change (b3Rest_b h).det ((T.toLinearEquiv.toLinearMap.restrictScalars ℝ) ∘
      (b3Rest_b h : Fin 2 → E)) = _
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hd, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_pos.mpr T.toLinearEquiv.isUnit_det'.ne_zero

end HodgeLean.Foundations.Curves.AbelTheorem
