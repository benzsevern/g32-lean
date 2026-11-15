import HodgeLean.Foundations.Program.RigidStartingSystemRational
import HodgeLean.Foundations.Program.RigidStartingSystemAnalyticFactors

noncomputable section
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_P5_bezout (s : ℂ) :
    (-3921456*s^4-24619638*s^3+31548615*s^2+13912524*s+29720580)*b65r_P 5 s +
      (653576*s^5+4838546*s^4-8535893*s^3-604787*s^2-7905990*s+7376220)*
        deriv (b65r_P 5) s = 746250000 := by
  rw [(b65r_P_hasDerivAt 5 s).deriv]
  dsimp only [b65r_P]
  ring

theorem b65r_Pneg7_bezout (s : ℂ) :
    (-464253024*s^4-485154282*s^3-1081080687*s^2+6049040004*s+349382364)*
      b65r_P (-7) s +
      (77375504*s^5+95366954*s^4+288131341*s^3-1898963657*s^2+564648678*s+1064909076)*
        deriv (b65r_P (-7)) s = 69886950000 := by
  rw [(b65r_P_hasDerivAt (-7) s).deriv]
  dsimp only [b65r_P]
  ring

theorem b65r_P5_simple (s : ℂ) (hs : b65r_P 5 s = 0) : deriv (b65r_P 5) s ≠ 0 := by
  intro hd
  have h := b65r_P5_bezout s
  rw [hs,hd,mul_zero,mul_zero,zero_add] at h
  norm_num at h

theorem b65r_Pneg7_simple (s : ℂ) (hs : b65r_P (-7) s = 0) : deriv (b65r_P (-7)) s ≠ 0 := by
  intro hd
  have h := b65r_Pneg7_bezout s
  rw [hs,hd,mul_zero,mul_zero,zero_add] at h
  norm_num at h

theorem b65r_P_root_avoids (ε s : ℂ) (hε : ε ≠ 0) (hs : b65r_P ε s = 0) :
    s ≠ 0 ∧ s ≠ 3 ∧ s ≠ 1 ∧ s ≠ -2 := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> subst s <;> norm_num [b65r_P, hε] at hs

theorem b65r_phi_fibre_derivative (ε s : ℂ) (h1 : s ≠ 1) (hneg2 : s ≠ -2) :
    deriv b65r_phi s =
      (deriv (b65r_P ε) s-(3/(s-1)+3/(s+2))*b65r_P ε s)/((s-1)^3*(s+2)^3) := by
  rw [(b65r_phi_hasDerivAt s h1 hneg2).deriv, (b65r_P_hasDerivAt ε s).deriv]
  have hs1 : s-1 ≠ 0 := sub_ne_zero.mpr h1
  have hs2 : s+2 ≠ 0 := by exact fun h ↦ hneg2 (by linear_combination h)
  dsimp only [b65r_P]
  field_simp
  ring

theorem b65r_phi_fibre_derivative_ne (ε s : ℂ) (h1 : s ≠ 1) (hneg2 : s ≠ -2)
    (hs : b65r_P ε s = 0) (hd : deriv (b65r_P ε) s ≠ 0) : deriv b65r_phi s ≠ 0 := by
  rw [b65r_phi_fibre_derivative ε s h1 hneg2, hs, mul_zero, sub_zero]
  apply div_ne_zero hd
  apply mul_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr h1)
  · apply pow_ne_zero
    exact fun h ↦ hneg2 (by linear_combination h)

theorem b65r_phi_analyticAt (s : ℂ) (h1 : s ≠ 1) (hneg2 : s ≠ -2) :
    AnalyticAt ℂ b65r_phi s := by
  have hs1 : s-1 ≠ 0 := sub_ne_zero.mpr h1
  have hs2 : s+2 ≠ 0 := by exact fun h ↦ hneg2 (by linear_combination h)
  exact ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 4)).div
    (((analyticAt_id.sub analyticAt_const).pow 3).mul ((analyticAt_id.add analyticAt_const).pow 3))
    (mul_ne_zero (pow_ne_zero _ hs1) (pow_ne_zero _ hs2))

theorem b65r_P_analyticAt (ε s : ℂ) : AnalyticAt ℂ (b65r_P ε) s := by
  exact ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 4)).sub
    ((analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow 3)).mul
      ((analyticAt_id.add analyticAt_const).pow 3))

theorem b65r_pullback_guards (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, z ≠ 0 ∧ z ≠ 3 ∧ z ≠ 1 ∧ z ≠ -2 ∧
      b65r_P 5 z ≠ 0 ∧ b65r_P (-7) z ≠ 0 := by
  have h5 := b65r_eventually_ne_punctured (b65r_P 5) a (b65r_P_analyticAt 5 a) (b65r_P5_simple a)
  have h7 := b65r_eventually_ne_punctured (b65r_P (-7)) a (b65r_P_analyticAt (-7) a)
    (b65r_Pneg7_simple a)
  filter_upwards [b65r_eventually_ne_point a 0,b65r_eventually_ne_point a 3,
    b65r_eventually_ne_point a 1,b65r_eventually_ne_point a (-2),h5,h7] with z hz0 hz3 hz1 hz2 hz5 hz7
  exact ⟨hz0,hz3,hz1,hz2,hz5,hz7⟩

theorem b65r_fibre_coordinate_factor (ε a : ℂ) (hε : ε ≠ 0)
    (hP : b65r_P ε a = 0) (hd : deriv (b65r_P ε) a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a ≠ 0 ∧
      ∀ z, b65r_phi z-ε = (z-a)*g z := by
  obtain ⟨h0,h3,h1,h2⟩ := b65r_P_root_avoids ε a hε hP
  have ha : AnalyticAt ℂ (fun z ↦ b65r_phi z-ε) a :=
    (b65r_phi_analyticAt a h1 h2).sub analyticAt_const
  have hz : b65r_phi a-ε = 0 := by rw [b65r_phi_sub ε a h1 h2,hP,zero_div]
  have hD : deriv (fun z ↦ b65r_phi z-ε) a ≠ 0 := by
    rw [deriv_sub_const]
    exact b65r_phi_fibre_derivative_ne ε a h1 h2 hP hd
  exact b65r_simple_analytic_factor (fun z ↦ b65r_phi z-ε) a ha hz hD

theorem b65r_inversePhi_analyticAt (s : ℂ) (h0 : s ≠ 0) (h3 : s ≠ 3) :
    AnalyticAt ℂ (fun z ↦ (b65r_phi z)⁻¹) s := by
  have hf : (fun z ↦ (b65r_phi z)⁻¹) =
      (fun z ↦ (z-1)^3*(z+2)^3/(z^2*(z-3)^4)) := by
    funext z
    unfold b65r_phi
    rw [inv_div]
  rw [hf]
  exact (((analyticAt_id.sub analyticAt_const).pow 3).mul
    ((analyticAt_id.add analyticAt_const).pow 3)).div
    ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 4))
    (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ (sub_ne_zero.mpr h3)))

end HodgeLean.Foundations.Program
