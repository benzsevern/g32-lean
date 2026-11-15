import HodgeLean.Foundations.Program.RigidStartingSystemPeripheralTransport
import HodgeLean.Foundations.Program.RigidStartingSystemPoleEnumeration
import HodgeLean.Foundations.Program.RigidStartingSystemPrintedGroup

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65r_sourceChart_finite (i : Fin 3) (z : ℂ) :
    b65r_sourceChart i.castSucc z = b65r_centres i+z := by
  fin_cases i <;> norm_num [b65r_sourceChart,b65r_centres] <;> ring

theorem b65r_finite_peripheral_class (x : b65r_sourceDomain)
    (M : FundamentalGroup b65r_sourceDomain x →*
      ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hM : ∀ p : Path x x, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val))
    (i : Fin 3) (g : FundamentalGroup b65r_sourceDomain x)
    (hgeom : ∃ R : ℝ, ∃ w : ℂ, w ≠ 0 ∧ ‖w‖ < R ∧
      (∀ z : ℂ, ‖z‖ < R → z ≠ 0 → (b65r_sourcePole i : ℂ)+z ∉ b65r_sourcePoles) ∧
      ∃ (y : b65r_sourceDomain) (k : Path x y) (d : Path y y),
        (∀ t, (d t : ℂ) = (b65r_sourcePole i : ℂ)+
          Complex.exp ((((t : ℝ)*(2*Real.pi) : ℝ) : ℂ)*Complex.I)*w) ∧
        FundamentalGroup.fromPath ⟦(k.trans d).trans k.symm⟧ = g) :
    IsConj (b65r_printedOperatorHom (b4b_generators i.castSucc)) (M g) := by
  obtain ⟨R,w,hw0,hw,havoid,y,k,d,hd,hclass⟩ := hgeom
  have ha : ∀ z : ℂ, ‖z‖ < R → z ≠ 0 →
      b65r_sourceChart i.castSucc z ∈ b65r_sourceDomain := by
    intro z hz hz0
    rw [← b65r_sourcePoles_domain,b65r_sourceChart_finite]
    exact havoid z hz hz0
  have hdc : ∀ t : unitInterval, (d t : ℂ) =
      b65r_sourceChart i.castSucc (Complex.exp (2*Real.pi*Complex.I*((t : ℝ) : ℂ))*w) := by
    intro t
    rw [hd,b65r_sourceChart_finite]
    congr 2
    push_cast
    ring
  obtain ⟨C,hC⟩ := b65r_peripheral_transport i.castSucc R ha w hw0 hw k d hdc
  apply isConj_iff.mpr
  refine ⟨C,Units.ext ?_⟩
  simp only [Units.val_mul,b65r_printedOperatorHom_val]
  rw [← hclass,hM]
  exact hC.symm

theorem b65r_infinite_peripheral_class (x : b65r_sourceDomain)
    (M : FundamentalGroup b65r_sourceDomain x →*
      ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hM : ∀ p : Path x x, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val))
    (g : FundamentalGroup b65r_sourceDomain x)
    (R L : ℝ) (hR : 0 < R) (hRL : 2*R < L)
    (hbound : ∀ z ∈ b65r_sourcePoles, ‖z‖ ≤ R)
    (y : b65r_sourceDomain) (k : Path x y) (d : Path y y)
    (hd : ∀ t, (d t : ℂ) =
      Complex.exp ((((t : ℝ)*(2*Real.pi) : ℝ) : ℂ)*Complex.I)*(L : ℂ))
    (hclass : FundamentalGroup.fromPath ⟦(k.trans d.symm).trans k.symm⟧ = g) :
    IsConj (b65r_printedOperatorHom (b4b_generators 3)) (M g) := by
  have hL : 0 < L := by linarith
  have ha : ∀ z : ℂ, ‖z‖ < R⁻¹ → z ≠ 0 →
      b65r_sourceChart 3 z ∈ b65r_sourceDomain := by
    intro z hz hz0
    have hn : R < ‖z⁻¹‖ := by
      rw [norm_inv]
      have hh := (inv_lt_inv₀ (inv_pos.mpr hR) (norm_pos_iff.mpr hz0)).mpr hz
      simpa only [inv_inv] using hh
    rw [← b65r_sourcePoles_domain]
    change z⁻¹ ∉ b65r_sourcePoles
    intro hm
    exact (not_le_of_gt hn) (hbound _ hm)
  have hw0 : (L : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hL.ne')
  have hw : ‖(L : ℂ)⁻¹‖ < R⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    exact (inv_lt_inv₀ hL hR).mpr (by linarith)
  have hdc : ∀ t : unitInterval, (d.symm t : ℂ) =
      b65r_sourceChart 3 (Complex.exp (2*Real.pi*Complex.I*((t : ℝ) : ℂ))*(L : ℂ)⁻¹) := by
    intro t
    change (d (unitInterval.symm t) : ℂ) = _
    rw [hd]
    change Complex.exp (((((1-(t : ℝ))*(2*Real.pi) : ℝ) : ℂ)*Complex.I))*(L : ℂ) =
      (Complex.exp (2*Real.pi*Complex.I*((t : ℝ) : ℂ))*(L : ℂ)⁻¹)⁻¹
    have he : ((((1-(t : ℝ))*(2*Real.pi) : ℝ) : ℂ)*Complex.I) =
        2*Real.pi*Complex.I-2*Real.pi*Complex.I*((t : ℝ) : ℂ) := by push_cast; ring
    rw [he,Complex.exp_sub,Complex.exp_two_pi_mul_I]
    simp [mul_inv_rev,div_eq_mul_inv,mul_comm]
  obtain ⟨C,hC⟩ := b65r_peripheral_transport 3 R⁻¹ ha (L : ℂ)⁻¹ hw0 hw k d.symm hdc
  apply isConj_iff.mpr
  refine ⟨C,Units.ext ?_⟩
  simp only [Units.val_mul,b65r_printedOperatorHom_val]
  rw [← hclass,hM]
  exact hC.symm

end HodgeLean.Foundations.Program
