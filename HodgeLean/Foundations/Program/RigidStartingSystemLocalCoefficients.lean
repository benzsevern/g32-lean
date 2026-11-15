import HodgeLean.Foundations.Program.RigidStartingSystemRational

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

def b65r_centres : Fin 3 → ℂ := ![5,-7,0]

def b65r_regularPart (i : Fin 4) (z : ℂ) : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
  ![(z+5)⁻¹ • b65r_operator b65r_B0+(z+12)⁻¹ • b65r_operator b65r_Bneg7,
    (z-7)⁻¹ • b65r_operator b65r_B0+(z-12)⁻¹ • b65r_operator b65r_B5,
    (z-5)⁻¹ • b65r_operator b65r_B5+(z+7)⁻¹ • b65r_operator b65r_Bneg7,
    (-5/(1-5*z)) • b65r_operator b65r_B5+(7/(1+7*z)) • b65r_operator b65r_Bneg7] i

theorem b65r_regularPart_analyticAt (i : Fin 4) : AnalyticAt ℂ (b65r_regularPart i) 0 := by
  fin_cases i
  · exact (((analyticAt_id.add analyticAt_const).inv (by norm_num)).smul analyticAt_const).add
      (((analyticAt_id.add analyticAt_const).inv (by norm_num)).smul analyticAt_const)
  · exact (((analyticAt_id.sub analyticAt_const).inv (by norm_num)).smul analyticAt_const).add
      (((analyticAt_id.sub analyticAt_const).inv (by norm_num)).smul analyticAt_const)
  · exact (((analyticAt_id.sub analyticAt_const).inv (by norm_num)).smul analyticAt_const).add
      (((analyticAt_id.add analyticAt_const).inv (by norm_num)).smul analyticAt_const)
  · exact ((analyticAt_const.div (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
      (by norm_num)).smul analyticAt_const).add
      ((analyticAt_const.div (analyticAt_const.add (analyticAt_const.mul analyticAt_id))
        (by norm_num)).smul analyticAt_const)

theorem b65r_finite_coefficient (i : Fin 3) (z : ℂ) :
    b65r_A (z+b65r_centres i) =
      z⁻¹ • b65r_operator (b65r_residues i.castSucc)+b65r_regularPart i.castSucc z := by
  fin_cases i <;>
    norm_num [b65r_A,b65r_centres,b65r_residues,b65r_regularPart,
      sub_eq_add_neg,add_assoc,add_left_comm,add_comm]

theorem b65r_inverse_coefficient (z : ℂ) (hz : z ≠ 0) (h5 : z ≠ 5) (hneg7 : z ≠ -7) :
    (z⁻¹)⁻¹ • b65r_operator b65r_Binf+b65r_regularPart 3 z⁻¹ =
      (-(z^2) : ℂ) • b65r_A z := by
  have hz5 : z-5 ≠ 0 := sub_ne_zero.mpr h5
  have hz7 : z+7 ≠ 0 := by exact fun h ↦ hneg7 (by linear_combination h)
  have hd5 : 1-5*z⁻¹ ≠ 0 := by
    rw [show 1-5*z⁻¹ = (z-5)/z by field_simp <;> ring]
    exact div_ne_zero hz5 hz
  have hd7 : 1+7*z⁻¹ ≠ 0 := by
    rw [show 1+7*z⁻¹ = (z+7)/z by field_simp <;> ring]
    exact div_ne_zero hz7 hz
  have hc0 : -(z^2)*z⁻¹ = -z := by field_simp <;> ring
  have hc5 : -z+(-5)/(1-5*z⁻¹) = -(z^2)*(z-5)⁻¹ := by field_simp <;> ring
  have hc7 : -z+7/(1+7*z⁻¹) = -(z^2)*(z+7)⁻¹ := by field_simp <;> ring
  change (z⁻¹)⁻¹ • b65r_operator b65r_Binf+
    ((-5/(1-5*z⁻¹)) • b65r_operator b65r_B5+(7/(1+7*z⁻¹)) • b65r_operator b65r_Bneg7) = _
  rw [b65r_operator_Binf]
  unfold b65r_A
  simp only [inv_inv,smul_neg,smul_add,smul_smul]
  rw [hc0,← hc5,← hc7]
  module

theorem b65r_finite_pullback_coefficient (i : Fin 3) (s : ℂ)
    (h0 : s ≠ 0) (h3 : s ≠ 3) (h1 : s ≠ 1) (h2 : s ≠ -2)
    (h5 : b65r_P 5 s ≠ 0) (h7 : b65r_P (-7) s ≠ 0) :
    b65r_pullback s = deriv (fun z ↦ b65r_phi z-b65r_centres i) s •
      ((b65r_phi s-b65r_centres i)⁻¹ • b65r_operator (b65r_residues i.castSucc)+
        b65r_regularPart i.castSucc (b65r_phi s-b65r_centres i)) := by
  rw [deriv_sub_const, b65r_pullback_formula s h0 h3 h1 h2 h5 h7,
    ← b65r_finite_coefficient]
  simp only [sub_add_cancel]

theorem b65r_phi_avoids (s : ℂ) (h0 : s ≠ 0) (h3 : s ≠ 3)
    (h1 : s ≠ 1) (h2 : s ≠ -2) (h5 : b65r_P 5 s ≠ 0) (h7 : b65r_P (-7) s ≠ 0) :
    b65r_phi s ≠ 0 ∧ b65r_phi s ≠ 5 ∧ b65r_phi s ≠ -7 := by
  have hd : (s-1)^3*(s+2)^3 ≠ 0 := mul_ne_zero
    (pow_ne_zero _ (sub_ne_zero.mpr h1))
    (pow_ne_zero _ (by exact fun h ↦ h2 (by linear_combination h)))
  refine ⟨div_ne_zero (mul_ne_zero (pow_ne_zero _ h0)
    (pow_ne_zero _ (sub_ne_zero.mpr h3))) hd,?_,?_⟩
  · apply sub_ne_zero.mp
    rw [b65r_phi_sub 5 s h1 h2]
    exact div_ne_zero h5 hd
  · apply sub_ne_zero.mp
    rw [b65r_phi_sub (-7) s h1 h2]
    exact div_ne_zero h7 hd

theorem b65r_infinite_pullback_coefficient (s : ℂ)
    (h0 : s ≠ 0) (h3 : s ≠ 3) (h1 : s ≠ 1) (h2 : s ≠ -2)
    (h5 : b65r_P 5 s ≠ 0) (h7 : b65r_P (-7) s ≠ 0) :
    b65r_pullback s = deriv (fun z ↦ (b65r_phi z)⁻¹) s •
      (((b65r_phi s)⁻¹)⁻¹ • b65r_operator b65r_Binf+
        b65r_regularPart 3 (b65r_phi s)⁻¹) := by
  obtain ⟨hz,hz5,hz7⟩ := b65r_phi_avoids s h0 h3 h1 h2 h5 h7
  have hi : HasDerivAt (fun z ↦ (b65r_phi z)⁻¹)
      (-(3*s*(s-3)^3*(5*s^2-3*s+4) / ((s-1)^4*(s+2)^4))/(b65r_phi s)^2) s :=
    (b65r_phi_hasDerivAt s h1 h2).inv hz
  rw [b65r_inverse_coefficient _ hz hz5 hz7, hi.deriv,
    ← (b65r_phi_hasDerivAt s h1 h2).deriv,smul_smul]
  have hc : (-(deriv b65r_phi s)/(b65r_phi s)^2)*(-(b65r_phi s)^2) =
      deriv b65r_phi s := by field_simp
  rw [hc]
  exact b65r_pullback_formula s h0 h3 h1 h2 h5 h7

end HodgeLean.Foundations.Program
