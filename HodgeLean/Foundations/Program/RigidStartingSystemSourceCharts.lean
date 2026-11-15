import HodgeLean.Foundations.Program.RigidStartingSystemLocalCoefficients

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

def b65r_sourceDomain : Set ℂ := {z | z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7}

def b65r_sourceChart (i : Fin 4) (z : ℂ) : ℂ :=
  ![z+5,z-7,z,z⁻¹] i

def b65r_sourceCoefficient (i : Fin 4) (z : ℂ) : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
  z⁻¹ • b65r_operator (b65r_residues i)+b65r_regularPart i z

theorem b65r_sourceDomain_open : IsOpen b65r_sourceDomain := by
  change IsOpen (({0}ᶜ : Set ℂ) ∩ ({5}ᶜ ∩ {-7}ᶜ))
  exact isOpen_compl_singleton.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)

theorem b65r_A_analytic : AnalyticOnNhd ℂ b65r_A b65r_sourceDomain := by
  intro z hz
  obtain ⟨h0,h5,h7⟩ := hz
  have hz7 : z+7 ≠ 0 := by exact fun h ↦ h7 (by linear_combination h)
  exact (((analyticAt_id.inv h0).smul analyticAt_const).add
    (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h5)).smul analyticAt_const)).add
    (((analyticAt_id.add analyticAt_const).inv hz7).smul analyticAt_const)

theorem b65r_sourceChart_analytic (i : Fin 4) (z : ℂ) (hz : z ≠ 0) :
    AnalyticAt ℂ (b65r_sourceChart i) z := by
  fin_cases i
  · exact analyticAt_id.add analyticAt_const
  · exact analyticAt_id.sub analyticAt_const
  · exact analyticAt_id
  · exact analyticAt_id.inv hz

theorem b65r_sourceChart_relation (i : Fin 4) (z : ℂ) (hz : z ≠ 0)
    (hm : b65r_sourceChart i z ∈ b65r_sourceDomain) :
    deriv (b65r_sourceChart i) z • b65r_A (b65r_sourceChart i z) =
      b65r_sourceCoefficient i z := by
  fin_cases i
  · change deriv (fun w : ℂ ↦ w+5) z • b65r_A (z+5) = b65r_sourceCoefficient 0 z
    have hd : HasDerivAt (fun w : ℂ ↦ w+5) 1 z := (hasDerivAt_id z).add_const 5
    rw [hd.deriv,one_smul]
    exact b65r_finite_coefficient 0 z
  · change deriv (fun w : ℂ ↦ w-7) z • b65r_A (z-7) = b65r_sourceCoefficient 1 z
    have hd : HasDerivAt (fun w : ℂ ↦ w-7) 1 z := (hasDerivAt_id z).sub_const 7
    rw [hd.deriv,one_smul]
    simpa [b65r_sourceCoefficient,b65r_sourceChart,b65r_centres,sub_eq_add_neg] using b65r_finite_coefficient 1 z
  · change deriv (fun w : ℂ ↦ w) z • b65r_A (z) = b65r_sourceCoefficient 2 z
    have hd : HasDerivAt (fun w : ℂ ↦ w) 1 z := hasDerivAt_id z
    rw [hd.deriv,one_smul]
    simpa [b65r_sourceCoefficient,b65r_sourceChart,b65r_centres] using b65r_finite_coefficient 2 z
  · change deriv (fun w : ℂ ↦ w⁻¹) z • b65r_A (z⁻¹) = b65r_sourceCoefficient 3 z
    have hd : HasDerivAt (fun w : ℂ ↦ w⁻¹) (-1/z^2) z := (hasDerivAt_id z).inv hz
    rw [hd.deriv]
    have hi := b65r_inverse_coefficient z⁻¹ (inv_ne_zero hz) hm.2.1 hm.2.2
    simp only [inv_inv] at hi
    change _ = z⁻¹ • b65r_operator b65r_Binf+b65r_regularPart 3 z
    rw [hi]
    congr 1
    simp [div_eq_mul_inv,inv_pow]

theorem b65r_sourceChart_avoids (i : Fin 4) (z : ℂ) (hz : z ≠ 0) (hs : ‖z‖ < 1/8) :
    b65r_sourceChart i z ∈ b65r_sourceDomain := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  fin_cases i
  · change z+5 ≠ 0 ∧ z+5 ≠ 5 ∧ z+5 ≠ -7
    constructor
    · intro h; have he : z = -5 := by linear_combination h
      subst z; norm_num at hs
    · constructor
      · exact fun h ↦ hz (by linear_combination h)
      · intro h; have he : z = -12 := by linear_combination h
        subst z; norm_num at hs
  · change z-7 ≠ 0 ∧ z-7 ≠ 5 ∧ z-7 ≠ -7
    constructor
    · intro h; have he : z = 7 := by linear_combination h
      subst z; norm_num at hs
    · constructor
      · intro h; have he : z = 12 := by linear_combination h
        subst z; norm_num at hs
      · exact fun h ↦ hz (by linear_combination h)
  · change z ≠ 0 ∧ z ≠ 5 ∧ z ≠ -7
    refine ⟨hz,?_,?_⟩
    · intro h; subst z; norm_num at hs
    · intro h; subst z; norm_num at hs
  · change z⁻¹ ≠ 0 ∧ z⁻¹ ≠ 5 ∧ z⁻¹ ≠ -7
    refine ⟨inv_ne_zero hz,?_,?_⟩
    · intro h
      have hh := congrArg Inv.inv h
      simp only [inv_inv] at hh
      rw [hh] at hs
      norm_num [norm_inv] at hs
    · intro h
      have hh := congrArg Inv.inv h
      simp only [inv_inv] at hh
      rw [hh] at hs
      norm_num [norm_inv] at hs

end HodgeLean.Foundations.Program
