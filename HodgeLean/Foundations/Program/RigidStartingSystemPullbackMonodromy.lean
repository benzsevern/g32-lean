import HodgeLean.Foundations.Program.RigidStartingSystemBranchData
import HodgeLean.Foundations.Program.RigidStartingSystemLocalCoefficients
import HodgeLean.Foundations.Program.RigidStartingSystemRamifiedMonodromy
import HodgeLean.Foundations.Program.RigidStartingSystemMonodromyClasses
import HodgeLean.Foundations.Program.RigidStartingSystemNonresonance

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65r_branch_coefficient (i : Fin 4) (a : ℂ) :
    b65r_pullback =ᶠ[𝓝[≠] a] fun z ↦ deriv (b65r_branchMaps i) z •
      ((b65r_branchMaps i z)⁻¹ • b65r_operator (b65r_residues (b65r_branchIndices i))+
        b65r_regularPart (b65r_branchIndices i) (b65r_branchMaps i z)) := by
  filter_upwards [b65r_pullback_guards a] with z hz
  obtain ⟨h0,h3,h1,h2,h5,h7⟩ := hz
  fin_cases i
  · change b65r_pullback z = deriv b65r_phi z •
        ((b65r_phi z)⁻¹ • b65r_operator (b65r_residues 2)+b65r_regularPart 2 (b65r_phi z))
    simpa [b65r_centres] using
      b65r_finite_pullback_coefficient 2 z h0 h3 h1 h2 h5 h7
  · change b65r_pullback z = deriv b65r_phi z •
        ((b65r_phi z)⁻¹ • b65r_operator (b65r_residues 2)+b65r_regularPart 2 (b65r_phi z))
    simpa [b65r_centres] using
      b65r_finite_pullback_coefficient 2 z h0 h3 h1 h2 h5 h7
  · exact b65r_infinite_pullback_coefficient z h0 h3 h1 h2 h5 h7
  · exact b65r_infinite_pullback_coefficient z h0 h3 h1 h2 h5 h7

theorem b65r_ramified_printed_conjugacy (i : Fin 4) (φ g : ℂ → ℂ) (a : ℂ)
    (e : ℕ) (he : 0 < e) (hφ : AnalyticAt ℂ φ a) (hg : AnalyticAt ℂ g a)
    (hga : g a ≠ 0) (hfactor : ∀ z, φ z = (z-a)^e*g z)
    (hEq : b65r_pullback =ᶠ[𝓝[≠] a] fun z ↦ deriv φ z •
      ((φ z)⁻¹ • b65r_operator (b65r_residues i)+b65r_regularPart i (φ z))) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (b65f_circle a ρ) =
          C.val*b65r_operator (b4b_toMatrix ((b4b_generators i)^e))*(C⁻¹).val := by
  obtain ⟨d,hd,hB⟩ := (b65r_regularPart_analyticAt i).exists_ball_analyticOnNhd
  obtain ⟨r,hr,hM⟩ := b65r_ramified_local_conjugacy (Fin 4 → ℂ)
    (b65r_operator (b65r_residues i)) (b65r_regularPart i) b65r_pullback d hd hB
    (b65r_residues_nonresonance i) φ g a e he hφ hg hga hfactor hEq
  refine ⟨r,hr,fun ρ hρ hρr ↦ ?_⟩
  obtain ⟨C,hC⟩ := hM ρ hρ hρr
  obtain ⟨D,hD⟩ := b65r_residue_power_class i e
  exact b65r_change_local_class _ _ _ C D hC hD

theorem b65r_branch_local_target (i : Fin 4) :
    b65r_localTarget (b65r_branchCentres i) =
      (b4b_generators (b65r_branchIndices i))^(b65r_branchOrders i) := by
  fin_cases i <;> norm_num [b65r_localTarget,b65r_branchCentres,b65r_branchIndices,b65r_branchOrders]

theorem b65r_branch_local_conjugacy (i : Fin 4) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        b65f_transport (Fin 4 → ℂ) b65r_pullback
          (b65f_circle (b65r_branchCentres i) ρ) =
          C.val*b65r_operator (b4b_toMatrix (b65r_localTarget (b65r_branchCentres i)))*(C⁻¹).val := by
  rw [b65r_branch_local_target]
  exact b65r_ramified_printed_conjugacy (b65r_branchIndices i)
    (b65r_branchMaps i) (b65r_branchFactors i) (b65r_branchCentres i)
    (b65r_branchOrders i) (b65r_branch_order_pos i) (b65r_branch_map_analytic i)
    (b65r_branch_factor_analytic i) (b65r_branch_factor_ne i) (b65r_branch_factor i)
    (b65r_branch_coefficient i _)

theorem b65r_distinct_fibre (ε δ a : ℂ) (hε : ε ≠ 0) (hne : ε ≠ δ)
    (hP : b65r_P ε a = 0) : b65r_P δ a ≠ 0 := by
  obtain ⟨h0,h3,h1,h2⟩ := b65r_P_root_avoids ε a hε hP
  have hd : (a-1)^3*(a+2)^3 ≠ 0 := mul_ne_zero
    (pow_ne_zero _ (sub_ne_zero.mpr h1))
    (pow_ne_zero _ (by exact fun h ↦ h2 (by linear_combination h)))
  intro hQ
  have hh : (δ-ε)*((a-1)^3*(a+2)^3) = 0 := by
    dsimp [b65r_P] at hP hQ
    linear_combination hP-hQ
  exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hd)).symm

theorem b65r_reflection_local_target (i : Fin 2) (a : ℂ)
    (hP : b65r_P (b65r_centres i.castSucc) a = 0) :
    b65r_localTarget a = b4b_generators i.castSucc.castSucc := by
  fin_cases i
  · change b65r_P 5 a = 0 at hP
    have h := b65r_P_root_avoids 5 a (by norm_num) hP
    simp [b65r_localTarget,h.1,h.2.1,h.2.2.1,h.2.2.2,hP]
  · have h := b65r_P_root_avoids (-7) a (by norm_num) hP
    have h5 := b65r_distinct_fibre (-7) 5 a (by norm_num) (by norm_num) hP
    simp [b65r_localTarget,h.1,h.2.1,h.2.2.1,h.2.2.2,h5]

theorem b65r_reflection_local_conjugacy (i : Fin 2) (a : ℂ)
    (hP : b65r_P (b65r_centres i.castSucc) a = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
        b65f_transport (Fin 4 → ℂ) b65r_pullback (b65f_circle a ρ) =
          C.val*b65r_operator (b4b_toMatrix (b65r_localTarget a))*(C⁻¹).val := by
  have hε : b65r_centres i.castSucc ≠ 0 := by fin_cases i <;> norm_num [b65r_centres]
  have hd : deriv (b65r_P (b65r_centres i.castSucc)) a ≠ 0 := by
    fin_cases i
    · exact b65r_P5_simple a hP
    · exact b65r_Pneg7_simple a hP
  obtain ⟨g,hg,hga,hfactor⟩ := b65r_fibre_coordinate_factor _ a hε hP hd
  obtain ⟨h0,h3,h1,h2⟩ := b65r_P_root_avoids _ a hε hP
  rw [b65r_reflection_local_target i a hP]
  have heq : b65r_pullback =ᶠ[𝓝[≠] a] fun z ↦
      deriv (fun z ↦ b65r_phi z-b65r_centres i.castSucc) z •
        ((b65r_phi z-b65r_centres i.castSucc)⁻¹ •
          b65r_operator (b65r_residues i.castSucc.castSucc)+
          b65r_regularPart i.castSucc.castSucc (b65r_phi z-b65r_centres i.castSucc)) := by
    filter_upwards [b65r_pullback_guards a] with z hz
    exact b65r_finite_pullback_coefficient i.castSucc z hz.1 hz.2.1 hz.2.2.1
      hz.2.2.2.1 hz.2.2.2.2.1 hz.2.2.2.2.2
  simpa only [pow_one] using b65r_ramified_printed_conjugacy i.castSucc.castSucc
    (fun z ↦ b65r_phi z-b65r_centres i.castSucc) g a 1 (by omega)
    ((b65r_phi_analyticAt a h1 h2).sub analyticAt_const) hg hga
    (by simpa only [pow_one] using hfactor) heq

end HodgeLean.Foundations.Program
