import HodgeLean.Foundations.Program.G32PropFourSixFamilyCWData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0447
import HodgeLean.Foundations.Program.G32PropFourSixPacked0186
import HodgeLean.Foundations.Program.G32PropFourSixFamilies
import HodgeLean.Foundations.Program.G32PropFourSixRowComparison
import HodgeLean.Foundations.Program.G32PropFourSixCharacters
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187
import HodgeLean.Foundations.Program.G32PropFourSixPacked0442

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate_096 :
    (g32p_literalCharacterValue 96 0).re = g32p_familyCWDimension 96 ∧
    (g32p_literalCharacterValue 96 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 96
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 96
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 96 j =
        g32p_familyCWDimension 96 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 96 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 96 : ℤ) -
        g32p_familyCWFixed 96 j)) = g32p_familyCWMultiplicity 96 := by
  decide +kernel

theorem g32p_familyCW_certificate_097 :
    (g32p_literalCharacterValue 97 0).re = g32p_familyCWDimension 97 ∧
    (g32p_literalCharacterValue 97 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 97
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 97
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 97 j =
        g32p_familyCWDimension 97 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 97 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 97 : ℤ) -
        g32p_familyCWFixed 97 j)) = g32p_familyCWMultiplicity 97 := by
  decide +kernel

theorem g32p_familyCW_certificate_098 :
    (g32p_literalCharacterValue 98 0).re = g32p_familyCWDimension 98 ∧
    (g32p_literalCharacterValue 98 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 98
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 98
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 98 j =
        g32p_familyCWDimension 98 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 98 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 98 : ℤ) -
        g32p_familyCWFixed 98 j)) = g32p_familyCWMultiplicity 98 := by
  decide +kernel

theorem g32p_familyCW_certificate_099 :
    (g32p_literalCharacterValue 99 0).re = g32p_familyCWDimension 99 ∧
    (g32p_literalCharacterValue 99 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 99
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 99
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 99 j =
        g32p_familyCWDimension 99 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 99 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 99 : ℤ) -
        g32p_familyCWFixed 99 j)) = g32p_familyCWMultiplicity 99 := by
  decide +kernel

theorem g32p_familyCW_certificate_100 :
    (g32p_literalCharacterValue 100 0).re = g32p_familyCWDimension 100 ∧
    (g32p_literalCharacterValue 100 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 100
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 100
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 100 j =
        g32p_familyCWDimension 100 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 100 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 100 : ℤ) -
        g32p_familyCWFixed 100 j)) = g32p_familyCWMultiplicity 100 := by
  decide +kernel

theorem g32p_familyCW_certificate_101 :
    (g32p_literalCharacterValue 101 0).re = g32p_familyCWDimension 101 ∧
    (g32p_literalCharacterValue 101 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue 101
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue 101
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed 101 j =
        g32p_familyCWDimension 101 + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension 101 : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension 101 : ℤ) -
        g32p_familyCWFixed 101 j)) = g32p_familyCWMultiplicity 101 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_familyCW_certificate (i : Fin 102) :
    (g32p_literalCharacterValue i 0).re = g32p_familyCWDimension i ∧
    (g32p_literalCharacterValue i 0).om = 0 ∧
    (∀ j : Fin 13,
      let t := g32p_literalCharacterValue i
        (g32p_literalColumn (g32p_familyCWBranchClass j))
      let u := g32p_literalCharacterValue i
        (g32p_literalColumn (g32p_familiesSquare (g32p_familyCWBranchClass j)))
      (g32p_familyCWPeriod j : ℤ) * g32p_familyCWFixed i j =
        g32p_familyCWDimension i + t.re + (if j.val < 12 then u.re else 0) ∧
      t.om + (if j.val < 12 then u.om else 0) = 0) ∧
    -2 * (g32p_familyCWDimension i : ℤ) +
      (∑ j : Fin 13, ((g32p_familyCWDimension i : ℤ) -
        g32p_familyCWFixed i j)) = g32p_familyCWMultiplicity i := by
  fin_cases i
  · exact g32p_familyCW_certificate_000
  · exact g32p_familyCW_certificate_001
  · exact g32p_familyCW_certificate_002
  · exact g32p_familyCW_certificate_003
  · exact g32p_familyCW_certificate_004
  · exact g32p_familyCW_certificate_005
  · exact g32p_familyCW_certificate_006
  · exact g32p_familyCW_certificate_007
  · exact g32p_familyCW_certificate_008
  · exact g32p_familyCW_certificate_009
  · exact g32p_familyCW_certificate_010
  · exact g32p_familyCW_certificate_011
  · exact g32p_familyCW_certificate_012
  · exact g32p_familyCW_certificate_013
  · exact g32p_familyCW_certificate_014
  · exact g32p_familyCW_certificate_015
  · exact g32p_familyCW_certificate_016
  · exact g32p_familyCW_certificate_017
  · exact g32p_familyCW_certificate_018
  · exact g32p_familyCW_certificate_019
  · exact g32p_familyCW_certificate_020
  · exact g32p_familyCW_certificate_021
  · exact g32p_familyCW_certificate_022
  · exact g32p_familyCW_certificate_023
  · exact g32p_familyCW_certificate_024
  · exact g32p_familyCW_certificate_025
  · exact g32p_familyCW_certificate_026
  · exact g32p_familyCW_certificate_027
  · exact g32p_familyCW_certificate_028
  · exact g32p_familyCW_certificate_029
  · exact g32p_familyCW_certificate_030
  · exact g32p_familyCW_certificate_031
  · exact g32p_familyCW_certificate_032
  · exact g32p_familyCW_certificate_033
  · exact g32p_familyCW_certificate_034
  · exact g32p_familyCW_certificate_035
  · exact g32p_familyCW_certificate_036
  · exact g32p_familyCW_certificate_037
  · exact g32p_familyCW_certificate_038
  · exact g32p_familyCW_certificate_039
  · exact g32p_familyCW_certificate_040
  · exact g32p_familyCW_certificate_041
  · exact g32p_familyCW_certificate_042
  · exact g32p_familyCW_certificate_043
  · exact g32p_familyCW_certificate_044
  · exact g32p_familyCW_certificate_045
  · exact g32p_familyCW_certificate_046
  · exact g32p_familyCW_certificate_047
  · exact g32p_familyCW_certificate_048
  · exact g32p_familyCW_certificate_049
  · exact g32p_familyCW_certificate_050
  · exact g32p_familyCW_certificate_051
  · exact g32p_familyCW_certificate_052
  · exact g32p_familyCW_certificate_053
  · exact g32p_familyCW_certificate_054
  · exact g32p_familyCW_certificate_055
  · exact g32p_familyCW_certificate_056
  · exact g32p_familyCW_certificate_057
  · exact g32p_familyCW_certificate_058
  · exact g32p_familyCW_certificate_059
  · exact g32p_familyCW_certificate_060
  · exact g32p_familyCW_certificate_061
  · exact g32p_familyCW_certificate_062
  · exact g32p_familyCW_certificate_063
  · exact g32p_familyCW_certificate_064
  · exact g32p_familyCW_certificate_065
  · exact g32p_familyCW_certificate_066
  · exact g32p_familyCW_certificate_067
  · exact g32p_familyCW_certificate_068
  · exact g32p_familyCW_certificate_069
  · exact g32p_familyCW_certificate_070
  · exact g32p_familyCW_certificate_071
  · exact g32p_familyCW_certificate_072
  · exact g32p_familyCW_certificate_073
  · exact g32p_familyCW_certificate_074
  · exact g32p_familyCW_certificate_075
  · exact g32p_familyCW_certificate_076
  · exact g32p_familyCW_certificate_077
  · exact g32p_familyCW_certificate_078
  · exact g32p_familyCW_certificate_079
  · exact g32p_familyCW_certificate_080
  · exact g32p_familyCW_certificate_081
  · exact g32p_familyCW_certificate_082
  · exact g32p_familyCW_certificate_083
  · exact g32p_familyCW_certificate_084
  · exact g32p_familyCW_certificate_085
  · exact g32p_familyCW_certificate_086
  · exact g32p_familyCW_certificate_087
  · exact g32p_familyCW_certificate_088
  · exact g32p_familyCW_certificate_089
  · exact g32p_familyCW_certificate_090
  · exact g32p_familyCW_certificate_091
  · exact g32p_familyCW_certificate_092
  · exact g32p_familyCW_certificate_093
  · exact g32p_familyCW_certificate_094
  · exact g32p_familyCW_certificate_095
  · exact g32p_familyCW_certificate_096
  · exact g32p_familyCW_certificate_097
  · exact g32p_familyCW_certificate_098
  · exact g32p_familyCW_certificate_099
  · exact g32p_familyCW_certificate_100
  · exact g32p_familyCW_certificate_101

theorem g32p_familyCW_selected_positive :
    (∀ j, 0 < g32p_familyCWMultiplicity (g32p_familiesPair j)) ∧
    (∀ j, 0 < g32p_familyCWMultiplicity (g32p_familiesBar j)) ∧
    (∀ j, 0 < g32p_familyCWMultiplicity (g32p_familiesQuat j)) := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 200000

def g32p_branchTrace (j : Fin 13) : HurwitzPrymRex_Zw :=
  if j.val < 6 then ⟨3, 1⟩ else if j.val < 12 then ⟨2, -1⟩ else ⟨0, 0⟩

theorem g32p_branch_character (j : Fin 13) :
    g32p_rho.character (g32p_classDatum j) =
      HurwitzPrymRex_ev g32h_omega (g32p_branchTrace j) := by
  have h0 : g32p_rho.character (g32p_classDatum 0) =
      HurwitzPrymRex_ev g32h_omega ⟨3, 1⟩ := by
    simpa only [HurwitzPrymRex_ev, Int.cast_ofNat, Int.cast_one, one_mul] using
      g32p_rho_character_reflection
  have h1 : g32p_rho.character (g32p_classDatum 6) =
      HurwitzPrymRex_ev g32h_omega ⟨2, -1⟩ := by
    rw [g32p_rho_character]
    change Matrix.trace (g32R2 g32h_omega) = _
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_four, g32R2, HurwitzPrymRex_ev]
    ring
  have h12 : g32p_rho.character (g32p_classDatum 12) =
      HurwitzPrymRex_ev g32h_omega ⟨0, 0⟩ := by
    rw [g32p_rho_character]
    change Matrix.trace (g32X g32h_omega * g32X g32h_omega) = _
    rw [papers3b_x_sq g32h_omega g32h_omega_sq_add]
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_four, HurwitzPrymRex_ev]
  fin_cases j <;> first | exact h0 | exact h1 | exact h12

def g32p_secondReflectionSquare (w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(w + 2) / 3, (w + 2) / 3, (w + 2) / 3, 0;
    -(2 * w + 1) / 3, (w + 2) / 3, (w - 1) / 3, 0;
    -(2 * w + 1) / 3, (w - 1) / 3, (w + 2) / 3, 0;
    0, 0, 0, 1]

theorem g32p_secondReflection_square :
    g32R2 g32h_omega * g32R2 g32h_omega = g32p_secondReflectionSquare g32h_omega := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32R2, g32p_secondReflectionSquare, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add

theorem g32p_secondReflection_cube : (g32p_classDatum 6) ^ 3 = 1 := by
  apply Subtype.ext
  change g32R2 g32h_omega ^ 3 = 1
  rw [pow_three, g32p_secondReflection_square]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g32R2, g32p_secondReflectionSquare, Matrix.mul_apply, Fin.sum_univ_four] <;>
    papers3b_omega_ring papers3b_omega_pow g32h_omega g32h_omega_sq_add

theorem g32p_branch_power (j : Fin 13) :
    g32p_classDatum j ^ (if j.val < 12 then 3 else 2) = 1 := by
  have hx : (g32p_classDatum 12) ^ 2 = 1 := by
    apply Subtype.ext
    change (g32X g32h_omega * g32X g32h_omega) ^ 2 = 1
    rw [← pow_two, ← pow_mul]
    exact (papers_g32_x_sq_aux g32h_omega g32h_omega_sq_add).2
  fin_cases j
  · exact g32p_reflection_cube
  · exact g32p_reflection_cube
  · exact g32p_reflection_cube
  · exact g32p_reflection_cube
  · exact g32p_reflection_cube
  · exact g32p_reflection_cube
  · exact g32p_secondReflection_cube
  · exact g32p_secondReflection_cube
  · exact g32p_secondReflection_cube
  · exact g32p_secondReflection_cube
  · exact g32p_secondReflection_cube
  · exact g32p_secondReflection_cube
  · exact hx


end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000

/-- Fixed-space dimension for an operator of period two or three.
Source: Serre, Linear Representations of Finite Groups, §2.1, averaging projector. -/
theorem g32p_familyCW_fixed_trace (V : FDRep ℂ g32p_G) (g : g32p_G)
    (n : ℕ) (hn : n = 2 ∨ n = 3) (hg : g ^ n = 1) :
    (n : ℂ) * (Module.finrank ℂ (LinearMap.ker (V.ρ g - 1)) : ℂ) =
      ∑ k ∈ Finset.range n, V.character (g ^ k) := by
  let T := V.ρ g
  let P : Module.End ℂ V := (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, T ^ k
  have hT : T ^ n = 1 := by rw [← map_pow, hg, map_one]
  have hn0 : (n : ℂ) ≠ 0 := by rcases hn with rfl | rfl <;> norm_num
  have hTP : T * P = P := by
    dsimp [P]
    rw [mul_smul_comm]
    congr 1
    rcases hn with rfl | rfl
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
        pow_one] at *
      noncomm_ring
      simpa only [← pow_two, ← pow_succ'] using congrArg (fun a => T + a) hT
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
        pow_one] at *
      noncomm_ring
      rw [← pow_two, ← pow_succ', hT]
  have hp : LinearMap.IsProj (LinearMap.ker (T - 1)) P := by
    constructor
    · intro v
      change (T - 1) (P v) = 0
      have h := congrArg (fun f : Module.End ℂ V => f v) hTP
      simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] using h
    · intro v hv
      have ht : T v = v := by
        simpa only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
          sub_eq_zero] using hv
      have hpow (k : ℕ) : (T ^ k) v = v := by
        induction k with
        | zero => rfl
        | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, ht]
      dsimp [P]
      simp only [LinearMap.sum_apply, hpow, Finset.sum_const,
        Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn0,
        one_smul]
  have htr := hp.trace
  dsimp [P] at htr
  rw [map_smul, map_sum] at htr
  have hc (k : ℕ) : LinearMap.trace ℂ V (T ^ k) = V.character (g ^ k) := by
    simp only [FDRep.character, map_pow]
    rfl
  simp_rw [hc] at htr
  rw [← htr]
  simp [smul_eq_mul, hn0]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

/-- Transport a row's identity entry to its representation dimension.
Source: Serre, Linear Representations of Finite Groups, §2.1. -/
theorem g32p_familyCW_dimension (i : Fin 102) (V : FDRep ℂ g32p_G)
    (h : V.character 1 = g32p_literalComplexValue i 0) :
    Module.finrank ℂ V = g32p_familyCWDimension i := by
  have hc := g32p_familyCW_certificate i
  have hid : g32p_literalColumn 0 = 0 := by decide
  simp only [g32p_literalComplexValue, hid, HurwitzPrymRex_ev, hc.1, hc.2.1,
    Int.cast_natCast, Int.cast_zero, zero_mul, add_zero] at h
  simpa only [FDRep.char_one, Nat.cast_inj] using h

/-- The branch fixed dimension from the row's branch and square traces.
Source: G32 v0.16, Proposition 3.1; cyclic averaging. -/
theorem g32p_familyCW_fixed (i : Fin 102) (V : FDRep ℂ g32p_G)
    (hd : Module.finrank ℂ V = g32p_familyCWDimension i)
    (ht : ∀ j, V.character (g32p_classDatum j) =
      g32p_literalComplexValue i (g32p_familyCWBranchClass j))
    (hs : ∀ j, V.character (g32p_classDatum j ^ 2) =
      g32p_literalComplexValue i (g32p_familiesSquare (g32p_familyCWBranchClass j)))
    (j : Fin 13) :
    Module.finrank ℂ (LinearMap.ker (V.ρ (g32p_classDatum j) - 1)) =
      g32p_familyCWFixed i j := by
  have h := g32p_familyCW_fixed_trace V (g32p_classDatum j) (g32p_familyCWPeriod j)
    (by unfold g32p_familyCWPeriod; split <;> simp) (g32p_branch_power j)
  have hc := (g32p_familyCW_certificate i).2.2.1 j
  dsimp only at hc
  have he : (g32p_familyCWPeriod j : ℂ) * (g32p_familyCWFixed i j : ℂ) =
      ∑ k ∈ Finset.range (g32p_familyCWPeriod j),
        V.character (g32p_classDatum j ^ k) := by
    by_cases hj : j.val < 12
    · simp only [g32p_familyCWPeriod, hj, ite_true, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, pow_zero, pow_one, ht, hs,
        FDRep.char_one, hd]
      simp only [g32p_familyCWPeriod, hj, ite_true] at hc
      have hr := congrArg (fun z : ℤ => (z : ℂ)) hc.1
      have hz := congrArg (fun z : ℤ => (z : ℂ)) hc.2
      push_cast at hr hz
      simp only [g32p_literalComplexValue, HurwitzPrymRex_ev]
      linear_combination hr - hz * g32h_omega
    · simp only [g32p_familyCWPeriod, hj, ite_false, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, pow_zero, pow_one, ht,
        FDRep.char_one, hd]
      simp only [g32p_familyCWPeriod, hj, ite_false, add_zero] at hc
      have hr := congrArg (fun z : ℤ => (z : ℂ)) hc.1
      push_cast at hr
      simp only [g32p_literalComplexValue, HurwitzPrymRex_ev, hc.2, Int.cast_zero,
        zero_mul, add_zero]
      exact hr
  have hn : (g32p_familyCWPeriod j : ℂ) ≠ 0 := by
    unfold g32p_familyCWPeriod
    split <;> norm_num
  exact_mod_cast (mul_left_cancel₀ hn (h.trans he.symm))

/-- CW multiplicity from the identity, branch and branch-square character entries.
Source: G32 v0.16, Proposition 3.1 and Definition 3.5. -/
theorem g32p_familyCW_multiplicity (i : Fin 102) (V : FDRep ℂ g32p_G)
    (h1 : V.character 1 = g32p_literalComplexValue i 0)
    (ht : ∀ j, V.character (g32p_classDatum j) =
      g32p_literalComplexValue i (g32p_familyCWBranchClass j))
    (hs : ∀ j, V.character (g32p_classDatum j ^ 2) =
      g32p_literalComplexValue i (g32p_familiesSquare (g32p_familyCWBranchClass j))) :
    g32p_cwMult V = g32p_familyCWMultiplicity i := by
  have hd := g32p_familyCW_dimension i V h1
  have hr (j : Fin 13) :
      (Module.finrank ℂ (LinearMap.range (V.ρ (g32p_classDatum j) - 1)) : ℤ) =
        (g32p_familyCWDimension i : ℤ) - g32p_familyCWFixed i j := by
    have hk := g32p_familyCW_fixed i V hd ht hs j
    have h := LinearMap.finrank_range_add_finrank_ker (V.ρ (g32p_classDatum j) - 1)
    rw [hd, hk] at h
    omega
  unfold g32p_cwMult
  simp_rw [hr]
  rw [hd]
  exact (g32p_familyCW_certificate i).2.2.2

example : g32p_familyCWBranchClass 0 = 1 ∧
    g32p_familyCWBranchClass 6 = 2 ∧ g32p_familyCWBranchClass 12 = 18 ∧
    g32p_familyCWPeriod 0 = 3 ∧ g32p_familyCWPeriod 12 = 2 := by
  decide +kernel

example : g32p_familyCWDimension 7 = 4 ∧
    g32p_familyCWFixed 7 0 = 3 ∧ g32p_familyCWFixed 7 6 = 3 ∧
    g32p_familyCWFixed 7 12 = 2 ∧ g32p_familyCWMultiplicity 7 = 6 ∧
    g32p_familyCWMultiplicity 0 = -2 := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

/-! Branch-trace positivity for the specified representation families.
HC no distance; AV milestone no distance. -/

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers

set_option maxHeartbeats 400000

/-- Multiplicity transport using the class map at branch elements.
Source: G32 v0.16, Proposition 3.1 and Definition 3.5. -/
theorem g32p_familyCW_of_character (D : g32p_familiesClassData)
    (hbranch : ∀ j, D.label (g32p_classDatum j) = g32p_familyCWBranchClass j)
    (hsquare : ∀ g, D.label (g * g) = g32p_familiesSquare (D.label g))
    (i : Fin 102) (V : FDRep ℂ g32p_G)
    (hV : ∀ g, V.character g = g32p_literalComplexValue i (D.label g)) :
    g32p_cwMult V = g32p_familyCWMultiplicity i := by
  apply g32p_familyCW_multiplicity i V
  · rw [hV, D.identity]
  · intro j
    rw [hV, hbranch]
  · intro j
    rw [hV, pow_two, hsquare, hbranch]

/-- The family-side conjuncts of the character comparison, with positive multiplicities.
Source: G32 v0.16, Proposition 4.6 and Appendix A. -/
theorem g32p_familyCW_families_of_class_data (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (hsquare : ∀ g, D.label (g * g) = g32p_familiesSquare (D.label g))
    (hbranch : ∀ j, D.label (g32p_classDatum j) = g32p_familyCWBranchClass j)
    (htrace : ∀ k c, (g32p_recordedInductionGenerators k).character
      (g32p_literalRepresentative c) =
        HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue k c)) :
    ∃ (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧
        0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      (∀ j, 0 < g32p_cwMult (τbar j)) ∧
      (∀ j g, (τ j).character g =
        g32p_literalComplexValue (g32p_familiesPair j) (D.label g)) ∧
      (∀ j g, (τbar j).character g =
        g32p_literalComplexValue (g32p_familiesBar j) (D.label g)) ∧
      (∀ j g, (θ j).character g =
        g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) := by
  obtain ⟨τ, τbar, θ, hp, hq, hdist, hqdist, hρ, hcover, ht, hb, hθ⟩ :=
    g32p_families_of_class_data D hrep hconj hsquare htrace
  have hpos (j : Fin 44) : 0 < g32p_cwMult (τ j) := by
    rw [g32p_familyCW_of_character D hbranch hsquare _ _ (ht j)]
    exact g32p_familyCW_selected_positive.1 j
  have hbar (j : Fin 44) : 0 < g32p_cwMult (τbar j) := by
    rw [g32p_familyCW_of_character D hbranch hsquare _ _ (hb j)]
    exact g32p_familyCW_selected_positive.2.1 j
  have hquat (j : Fin 4) : 0 < g32p_cwMult (θ j) := by
    rw [g32p_familyCW_of_character D hbranch hsquare _ _ (hθ j)]
    exact g32p_familyCW_selected_positive.2.2 j
  refine ⟨τ, τbar, θ, ?_, ?_, hdist, hqdist, hρ, ?_, hbar, ht, hb, hθ⟩
  · intro j
    exact ⟨(hp j).1, (hp j).2.1, (hp j).2.2.1, (hp j).2.2.2, hpos j⟩
  · intro j
    exact ⟨(hq j).1, (hq j).2, hquat j⟩
  · intro σ hσ _
    exact hcover σ hσ

example (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (hsquare : ∀ g, D.label (g * g) = g32p_familiesSquare (D.label g))
    (hbranch : ∀ j, D.label (g32p_classDatum j) = g32p_familyCWBranchClass j)
    (htrace : ∀ k c, (g32p_recordedInductionGenerators k).character
      (g32p_literalRepresentative c) =
        HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue k c)) :
    ∃ (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧
        0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) := by
  obtain ⟨τ, τbar, θ, hp, hq, hd, hqd, hρ, hc, _, _, _, _⟩ :=
    g32p_familyCW_families_of_class_data D hrep hconj hsquare hbranch htrace
  exact ⟨τ, τbar, θ, hp, hq, hd, hqd, hρ, hc⟩

end HodgeLean.Foundations.Program

end
end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 200000

noncomputable def g32p_restrictionTrace {G : Type*} [Group G]
    (τ τbar : Fin 44 → FDRep ℂ G) (θ : Fin 4 → FDRep ℂ G)
    (j : Fin 48) (g : G) : ℂ :=
  if h : j.val < 44 then
    (τ ⟨j.val, h⟩).character g - (τbar ⟨j.val, h⟩).character g
  else (θ ⟨j.val - 44, by omega⟩).character g

theorem g32p_restriction_node_weight (S : g32p_Supplier)
    (V W : FDRep ℂ g32p_G) (h : S.H) (a : HurwitzPrymRex_Zw)
    (b : Multiplicative (ZMod S.m))
    (htrace : V.character h - W.character h =
      HurwitzPrymRex_ev (g32p_root S.m ^ (S.m / 3)) a)
    (hvalue : S.χ h = b) :
    (V.character h - W.character h) * (g32p_complexCharacter S h⁻¹ : ℂ) =
      HurwitzPrymRex_ev (g32p_root S.m ^ (S.m / 3)) a *
        g32p_root S.m ^ (Multiplicative.toAdd b⁻¹).val := by
  rw [htrace, g32p_complexCharacter_apply, map_inv, hvalue]

theorem g32p_restriction_histogram_sum {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H] {n : ℕ} (e : Fin n ≃ H)
    (f : H → ℂ) (terms : List (ℕ × HurwitzPrymRex_Zw × ℕ))
    (label : Fin n → Option (Fin terms.length)) (z : ℂ) (m : ℕ)
    (hvalue : ∀ i, f (e i) =
      (label i).elim 0 (fun t =>
        HurwitzPrymRex_ev (z ^ (m / 3)) (terms[t]).2.1 * z ^ (terms[t]).2.2))
    (hcount : ∀ t : Fin terms.length,
      (Finset.univ.filter (fun i => label i = some t)).card = (terms[t]).1) :
    (∑ h : H, f h) = (terms.map (fun x => (x.1 : ℂ) *
      HurwitzPrymRex_ev (z ^ (m / 3)) x.2.1 * z ^ x.2.2)).sum := by
  classical
  rw [← e.sum_comp f]
  simp_rw [hvalue]
  rw [← Finset.sum_fiberwise' Finset.univ label
    (fun o : Option (Fin terms.length) => o.elim 0 (fun t =>
      HurwitzPrymRex_ev (z ^ (m / 3)) (terms[t]).2.1 * z ^ (terms[t]).2.2))]
  rw [Fintype.sum_option]
  simp only [Option.elim_none, Finset.sum_const_zero, zero_add, Option.elim_some,
    Finset.sum_const, nsmul_eq_mul, hcount]
  have he := List.sum_ofFn (f := fun t : Fin terms.length =>
    ((terms[t]).1 : ℂ) *
      (HurwitzPrymRex_ev (z ^ (m / 3)) (terms[t]).2.1 * z ^ (terms[t]).2.2))
  rw [← he]
  have ht : (List.ofFn fun t : Fin terms.length =>
      ((terms[t]).1 : ℂ) *
        (HurwitzPrymRex_ev (z ^ (m / 3)) (terms[t]).2.1 * z ^ (terms[t]).2.2)) =
      terms.map (fun x => (x.1 : ℂ) *
        (HurwitzPrymRex_ev (z ^ (m / 3)) x.2.1 * z ^ x.2.2)) := by
    apply List.ext_get
    · simp only [List.length_ofFn, List.length_map]
    · intro i hi₁ hi₂
      simp [List.get_eq_getElem]
  rw [ht]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  exact (mul_assoc _ _ _).symm

end HodgeLean.Foundations.Program

end

section

/-! Character comparison from explicit class, supplier and node restriction inputs.
HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- The ordered free differences and quaternionic character values. -/
def g32p_comparisonAssemblyValue (c : Fin 102) (j : Fin 48) : ℂ :=
  if h : j.val < 44 then
    g32p_literalComplexValue (g32p_familiesPair ⟨j.val, h⟩) c -
      g32p_literalComplexValue (g32p_familiesBar ⟨j.val, h⟩) c
  else g32p_literalComplexValue (g32p_familiesQuat ⟨j.val - 44, by omega⟩) c

theorem g32p_comparisonAssembly_trace (D : g32p_familiesClassData)
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g))
    (j : Fin 48) (g : g32p_G) :
    g32p_restrictionTrace τ τbar θ j g =
      g32p_comparisonAssemblyValue (D.label g) j := by
  unfold g32p_restrictionTrace g32p_comparisonAssemblyValue
  split_ifs
  · rw [ht, hb]
  · rw [hq]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_comparisonAssembly (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (hsquare : ∀ g, D.label (g * g) = g32p_familiesSquare (D.label g))
    (hbranch : ∀ j, D.label (g32p_classDatum j) = g32p_familyCWBranchClass j)
    (htrace : ∀ k c, (g32p_recordedInductionGenerators k).character
      (g32p_literalRepresentative c) =
        HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue k c))
    (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
    (hsupplier : ∀ i : Fin 51,
      (∀ h, (χc i h : ℂ) =
        g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
        r.orderH = Nat.card (S i).H ∧
        (g32p_exponents (S i)).Perm (expandExps r.exps)))
    (n : Fin 51 → ℕ) (e : ∀ i, Fin (n i) ≃ (S i).H)
    (coeff : ∀ i, Fin 48 → Fin (n i) → HurwitzPrymRex_Zw)
    (hnode : ∀ i j k, g32p_comparisonAssemblyValue (D.label (e i k)) j =
      HurwitzPrymRex_ev g32h_omega (coeff i j k))
    (hrestriction : ∀ i (τ τbar : Fin 44 → FDRep ℂ g32p_G)
      (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j k, g32p_restrictionTrace τ τbar θ j (e i k) =
        HurwitzPrymRex_ev g32h_omega (coeff i j k)) →
      ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
        papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords) :
    ∃ (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
      (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      ∀ i : Fin 51,
        (∀ h, ((χc i h : ℂˣ) : ℂ) =
          g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
        (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
          r.orderH = Nat.card (S i).H ∧ (g32p_exponents (S i)).Perm (expandExps r.exps)) ∧
        ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
          papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords := by
  obtain ⟨τ, τbar, θ, hp, hq, hd, hqd, hρ, hc, _, ht, hb, hθ⟩ :=
    g32p_familyCW_families_of_class_data D hrep hconj hsquare hbranch htrace
  refine ⟨S, χc, τ, τbar, θ, hp, hq, hd, hqd, hρ, hc, ?_⟩
  intro i
  refine ⟨(hsupplier i).1, (hsupplier i).2, hrestriction i τ τbar θ ?_⟩
  intro j k
  rw [g32p_comparisonAssembly_trace D τ τbar θ ht hb hθ]
  exact hnode i j k

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_inverse_isConj_of_mul {G : Type} [Group G] (r s c : G)
    (h : r * (c * s) = c) : IsConj r⁻¹ s := by
  have he : c * s = r⁻¹ * c := by
    have h' := congrArg (fun x => r⁻¹ * x) h
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h'
  apply IsConj.symm
  apply isConj_iff.mpr
  exact ⟨c, by rw [he, mul_assoc, mul_inv_cancel, mul_one]⟩

theorem g32p_archiveWord_inverse_isConj
    (r s w : List (Fin 4)) (R S C : HurwitzPrymRex_Mat)
    (hr : g32p_archiveIntegralWord r = R)
    (hs : g32p_archiveIntegralWord s = S)
    (hc : g32p_archiveIntegralWord w = C)
    (h : HurwitzPrymRex_mmul R (HurwitzPrymRex_mmul C S) = C) :
    IsConj (g32p_archiveWord r)⁻¹ (g32p_archiveWord s) := by
  apply g32p_inverse_isConj_of_mul _ _ (g32p_archiveWord w)
  apply Subtype.ext
  change b4b_toMatrix (g32p_archiveWord r *
    (g32p_archiveWord w * g32p_archiveWord s)) = b4b_toMatrix (g32p_archiveWord w)
  rw [map_mul, map_mul, g32p_archiveIntegralWord_map,
    g32p_archiveIntegralWord_map, g32p_archiveIntegralWord_map, hr, hs, hc,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, h]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_integration_isConj_of_matrix (a b : g32p_G)
    (w : List (Fin 4)) (A B C : HurwitzPrymRex_Mat)
    (ha : b4b_toMatrix a = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega A))
    (hb : b4b_toMatrix b = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega B))
    (hc : g32p_archiveIntegralWord w = C)
    (he : HurwitzPrymRex_mmul A C = HurwitzPrymRex_mmul C B) : IsConj a b := by
  have h : a * g32p_archiveWord w = g32p_archiveWord w * b := by
    apply Subtype.ext
    change b4b_toMatrix (a * g32p_archiveWord w) = b4b_toMatrix (g32p_archiveWord w * b)
    rw [map_mul, map_mul, ha, hb, g32p_archiveIntegralWord_map, hc,
      ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
      ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, he]
  apply IsConj.symm
  apply isConj_iff.mpr
  exact ⟨g32p_archiveWord w, by rw [← h, mul_assoc, mul_inv_cancel, mul_one]⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationBranch0Word : List (Fin 4) := [3, 3, 2, 1]

def g32p_integrationBranch0Matrix : HurwitzPrymRex_Mat := ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

def g32p_integrationBranch0Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationBranch0_certificate : g32p_archiveWordCertificate g32p_integrationBranch0Word g32p_integrationBranch0Stages = true := by
  decide +kernel

theorem g32p_integrationBranch0_integral : g32p_archiveIntegralWord g32p_integrationBranch0Word = g32p_integrationBranch0Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationBranch0_certificate
  have hx : x = g32p_integrationBranch0Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationBranch0_equation :
    HurwitzPrymRex_mmul (![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]) g32p_integrationBranch0Matrix =
      HurwitzPrymRex_mmul g32p_integrationBranch0Matrix g32p_literalMatrix_001 := by
  decide +kernel

theorem g32p_integrationBranch0_actual : IsConj (g32p_classDatum 0) (g32p_literalRepresentative 1) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationBranch0Word
    (![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]) g32p_literalMatrix_001 g32p_integrationBranch0Matrix
  · change b4b_toMatrix (b4b_generators 0) = _
    exact g32p_integralGenerator_map 0
  · exact g32p_literalRepresentative_matrix 1
  · exact g32p_integrationBranch0_integral
  · exact g32p_integrationBranch0_equation

def g32p_integrationBranch1Word : List (Fin 4) := [1, 1]

def g32p_integrationBranch1Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationBranch1Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationBranch1_certificate : g32p_archiveWordCertificate g32p_integrationBranch1Word g32p_integrationBranch1Stages = true := by
  decide +kernel

theorem g32p_integrationBranch1_integral : g32p_archiveIntegralWord g32p_integrationBranch1Word = g32p_integrationBranch1Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationBranch1_certificate
  have hx : x = g32p_integrationBranch1Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationBranch1_equation :
    HurwitzPrymRex_mmul (![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]) g32p_integrationBranch1Matrix =
      HurwitzPrymRex_mmul g32p_integrationBranch1Matrix g32p_literalMatrix_002 := by
  decide +kernel

theorem g32p_integrationBranch1_actual : IsConj (g32p_classDatum 6) (g32p_literalRepresentative 2) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationBranch1Word
    (![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]) g32p_literalMatrix_002 g32p_integrationBranch1Matrix
  · change b4b_toMatrix (b4b_generators 1) = _
    exact g32p_integralGenerator_map 1
  · exact g32p_literalRepresentative_matrix 2
  · exact g32p_integrationBranch1_integral
  · exact g32p_integrationBranch1_equation

def g32p_integrationBranch2Word : List (Fin 4) := [3, 0, 0, 1, 2]

def g32p_integrationBranch2Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

def g32p_integrationBranch2Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationBranch2_certificate : g32p_archiveWordCertificate g32p_integrationBranch2Word g32p_integrationBranch2Stages = true := by
  decide +kernel

theorem g32p_integrationBranch2_integral : g32p_archiveIntegralWord g32p_integrationBranch2Word = g32p_integrationBranch2Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationBranch2_certificate
  have hx : x = g32p_integrationBranch2Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationBranch2_equation :
    HurwitzPrymRex_mmul (![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]) g32p_integrationBranch2Matrix =
      HurwitzPrymRex_mmul g32p_integrationBranch2Matrix g32p_literalMatrix_018 := by
  decide +kernel

theorem g32p_integrationBranch2_actual : IsConj (g32p_classDatum 12) (g32p_literalRepresentative 18) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationBranch2Word
    (![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]) g32p_literalMatrix_018 g32p_integrationBranch2Matrix
  · change b4b_toMatrix (b4b_generators 2 * b4b_generators 2) = _
    rw [map_mul, g32p_integralGenerator_map, ← map_mul,
      ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
    rfl
  · exact g32p_literalRepresentative_matrix 18
  · exact g32p_integrationBranch2_integral
  · exact g32p_integrationBranch2_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare000Word : List (Fin 4) := []

def g32p_integrationSquare000Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare000Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare000_certificate : g32p_archiveWordCertificate g32p_integrationSquare000Word g32p_integrationSquare000Stages = true := by
  decide +kernel

theorem g32p_integrationSquare000_integral : g32p_archiveIntegralWord g32p_integrationSquare000Word = g32p_integrationSquare000Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare000_certificate
  have hx : x = g32p_integrationSquare000Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare000_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_000 g32p_literalMatrix_000) g32p_integrationSquare000Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare000Matrix g32p_literalMatrix_000 := by
  decide +kernel

theorem g32p_integrationSquare000_actual : IsConj (g32p_literalRepresentative 0 * g32p_literalRepresentative 0)
    (g32p_literalRepresentative (g32p_familiesSquare 0)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare000Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_000 g32p_literalMatrix_000) g32p_literalMatrix_000 g32p_integrationSquare000Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_000) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_000) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 0) = _
    exact g32p_literalRepresentative_matrix 0
  · exact g32p_integrationSquare000_integral
  · exact g32p_integrationSquare000_equation

def g32p_integrationSquare001Word : List (Fin 4) := []

def g32p_integrationSquare001Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare001Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare001_certificate : g32p_archiveWordCertificate g32p_integrationSquare001Word g32p_integrationSquare001Stages = true := by
  decide +kernel

theorem g32p_integrationSquare001_integral : g32p_archiveIntegralWord g32p_integrationSquare001Word = g32p_integrationSquare001Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare001_certificate
  have hx : x = g32p_integrationSquare001Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare001_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_001 g32p_literalMatrix_001) g32p_integrationSquare001Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare001Matrix g32p_literalMatrix_002 := by
  decide +kernel

theorem g32p_integrationSquare001_actual : IsConj (g32p_literalRepresentative 1 * g32p_literalRepresentative 1)
    (g32p_literalRepresentative (g32p_familiesSquare 1)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare001Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_001 g32p_literalMatrix_001) g32p_literalMatrix_002 g32p_integrationSquare001Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_001) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_001) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 2) = _
    exact g32p_literalRepresentative_matrix 2
  · exact g32p_integrationSquare001_integral
  · exact g32p_integrationSquare001_equation

def g32p_integrationSquare002Word : List (Fin 4) := []

def g32p_integrationSquare002Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare002Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare002_certificate : g32p_archiveWordCertificate g32p_integrationSquare002Word g32p_integrationSquare002Stages = true := by
  decide +kernel

theorem g32p_integrationSquare002_integral : g32p_archiveIntegralWord g32p_integrationSquare002Word = g32p_integrationSquare002Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare002_certificate
  have hx : x = g32p_integrationSquare002Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare002_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_002 g32p_literalMatrix_002) g32p_integrationSquare002Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare002Matrix g32p_literalMatrix_001 := by
  decide +kernel

theorem g32p_integrationSquare002_actual : IsConj (g32p_literalRepresentative 2 * g32p_literalRepresentative 2)
    (g32p_literalRepresentative (g32p_familiesSquare 2)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare002Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_002 g32p_literalMatrix_002) g32p_literalMatrix_001 g32p_integrationSquare002Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_002) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_002) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 1) = _
    exact g32p_literalRepresentative_matrix 1
  · exact g32p_integrationSquare002_integral
  · exact g32p_integrationSquare002_equation

def g32p_integrationSquare003Word : List (Fin 4) := [1]

def g32p_integrationSquare003Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare003Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare003_certificate : g32p_archiveWordCertificate g32p_integrationSquare003Word g32p_integrationSquare003Stages = true := by
  decide +kernel

theorem g32p_integrationSquare003_integral : g32p_archiveIntegralWord g32p_integrationSquare003Word = g32p_integrationSquare003Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare003_certificate
  have hx : x = g32p_integrationSquare003Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare003_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_003 g32p_literalMatrix_003) g32p_integrationSquare003Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare003Matrix g32p_literalMatrix_001 := by
  decide +kernel

theorem g32p_integrationSquare003_actual : IsConj (g32p_literalRepresentative 3 * g32p_literalRepresentative 3)
    (g32p_literalRepresentative (g32p_familiesSquare 3)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare003Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_003 g32p_literalMatrix_003) g32p_literalMatrix_001 g32p_integrationSquare003Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_003) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_003) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 1) = _
    exact g32p_literalRepresentative_matrix 1
  · exact g32p_integrationSquare003_integral
  · exact g32p_integrationSquare003_equation

def g32p_integrationSquare004Word : List (Fin 4) := []

def g32p_integrationSquare004Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare004Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare004_certificate : g32p_archiveWordCertificate g32p_integrationSquare004Word g32p_integrationSquare004Stages = true := by
  decide +kernel

theorem g32p_integrationSquare004_integral : g32p_archiveIntegralWord g32p_integrationSquare004Word = g32p_integrationSquare004Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare004_certificate
  have hx : x = g32p_integrationSquare004Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare004_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_004 g32p_literalMatrix_004) g32p_integrationSquare004Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare004Matrix g32p_literalMatrix_011 := by
  decide +kernel

theorem g32p_integrationSquare004_actual : IsConj (g32p_literalRepresentative 4 * g32p_literalRepresentative 4)
    (g32p_literalRepresentative (g32p_familiesSquare 4)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare004Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_004 g32p_literalMatrix_004) g32p_literalMatrix_011 g32p_integrationSquare004Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_004) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_004) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 11) = _
    exact g32p_literalRepresentative_matrix 11
  · exact g32p_integrationSquare004_integral
  · exact g32p_integrationSquare004_equation

def g32p_integrationSquare005Word : List (Fin 4) := []

def g32p_integrationSquare005Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare005Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare005_certificate : g32p_archiveWordCertificate g32p_integrationSquare005Word g32p_integrationSquare005Stages = true := by
  decide +kernel

theorem g32p_integrationSquare005_integral : g32p_archiveIntegralWord g32p_integrationSquare005Word = g32p_integrationSquare005Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare005_certificate
  have hx : x = g32p_integrationSquare005Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare005_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_005 g32p_literalMatrix_005) g32p_integrationSquare005Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare005Matrix g32p_literalMatrix_018 := by
  decide +kernel

theorem g32p_integrationSquare005_actual : IsConj (g32p_literalRepresentative 5 * g32p_literalRepresentative 5)
    (g32p_literalRepresentative (g32p_familiesSquare 5)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare005Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_005 g32p_literalMatrix_005) g32p_literalMatrix_018 g32p_integrationSquare005Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_005) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_005) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 18) = _
    exact g32p_literalRepresentative_matrix 18
  · exact g32p_integrationSquare005_integral
  · exact g32p_integrationSquare005_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare006Word : List (Fin 4) := [1, 2, 0, 1]

def g32p_integrationSquare006Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare006Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare006_certificate : g32p_archiveWordCertificate g32p_integrationSquare006Word g32p_integrationSquare006Stages = true := by
  decide +kernel

theorem g32p_integrationSquare006_integral : g32p_archiveIntegralWord g32p_integrationSquare006Word = g32p_integrationSquare006Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare006_certificate
  have hx : x = g32p_integrationSquare006Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare006_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_006 g32p_literalMatrix_006) g32p_integrationSquare006Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare006Matrix g32p_literalMatrix_006 := by
  decide +kernel

theorem g32p_integrationSquare006_actual : IsConj (g32p_literalRepresentative 6 * g32p_literalRepresentative 6)
    (g32p_literalRepresentative (g32p_familiesSquare 6)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare006Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_006 g32p_literalMatrix_006) g32p_literalMatrix_006 g32p_integrationSquare006Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_006) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_006) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 6) = _
    exact g32p_literalRepresentative_matrix 6
  · exact g32p_integrationSquare006_integral
  · exact g32p_integrationSquare006_equation

def g32p_integrationSquare007Word : List (Fin 4) := [3, 2, 1, 0, 3, 2]

def g32p_integrationSquare007Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

def g32p_integrationSquare007Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare007_certificate : g32p_archiveWordCertificate g32p_integrationSquare007Word g32p_integrationSquare007Stages = true := by
  decide +kernel

theorem g32p_integrationSquare007_integral : g32p_archiveIntegralWord g32p_integrationSquare007Word = g32p_integrationSquare007Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare007_certificate
  have hx : x = g32p_integrationSquare007Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare007_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_007 g32p_literalMatrix_007) g32p_integrationSquare007Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare007Matrix g32p_literalMatrix_019 := by
  decide +kernel

theorem g32p_integrationSquare007_actual : IsConj (g32p_literalRepresentative 7 * g32p_literalRepresentative 7)
    (g32p_literalRepresentative (g32p_familiesSquare 7)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare007Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_007 g32p_literalMatrix_007) g32p_literalMatrix_019 g32p_integrationSquare007Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_007) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_007) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 19) = _
    exact g32p_literalRepresentative_matrix 19
  · exact g32p_integrationSquare007_integral
  · exact g32p_integrationSquare007_equation

def g32p_integrationSquare008Word : List (Fin 4) := [1, 1]

def g32p_integrationSquare008Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare008Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare008_certificate : g32p_archiveWordCertificate g32p_integrationSquare008Word g32p_integrationSquare008Stages = true := by
  decide +kernel

theorem g32p_integrationSquare008_integral : g32p_archiveIntegralWord g32p_integrationSquare008Word = g32p_integrationSquare008Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare008_certificate
  have hx : x = g32p_integrationSquare008Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare008_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_008 g32p_literalMatrix_008) g32p_integrationSquare008Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare008Matrix g32p_literalMatrix_002 := by
  decide +kernel

theorem g32p_integrationSquare008_actual : IsConj (g32p_literalRepresentative 8 * g32p_literalRepresentative 8)
    (g32p_literalRepresentative (g32p_familiesSquare 8)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare008Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_008 g32p_literalMatrix_008) g32p_literalMatrix_002 g32p_integrationSquare008Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_008) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_008) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 2) = _
    exact g32p_literalRepresentative_matrix 2
  · exact g32p_integrationSquare008_integral
  · exact g32p_integrationSquare008_equation

def g32p_integrationSquare009Word : List (Fin 4) := [1, 1, 0, 0]

def g32p_integrationSquare009Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

def g32p_integrationSquare009Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare009_certificate : g32p_archiveWordCertificate g32p_integrationSquare009Word g32p_integrationSquare009Stages = true := by
  decide +kernel

theorem g32p_integrationSquare009_integral : g32p_archiveIntegralWord g32p_integrationSquare009Word = g32p_integrationSquare009Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare009_certificate
  have hx : x = g32p_integrationSquare009Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare009_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_009 g32p_literalMatrix_009) g32p_integrationSquare009Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare009Matrix g32p_literalMatrix_014 := by
  decide +kernel

theorem g32p_integrationSquare009_actual : IsConj (g32p_literalRepresentative 9 * g32p_literalRepresentative 9)
    (g32p_literalRepresentative (g32p_familiesSquare 9)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare009Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_009 g32p_literalMatrix_009) g32p_literalMatrix_014 g32p_integrationSquare009Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_009) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_009) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 14) = _
    exact g32p_literalRepresentative_matrix 14
  · exact g32p_integrationSquare009_integral
  · exact g32p_integrationSquare009_equation

def g32p_integrationSquare010Word : List (Fin 4) := []

def g32p_integrationSquare010Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare010Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare010_certificate : g32p_archiveWordCertificate g32p_integrationSquare010Word g32p_integrationSquare010Stages = true := by
  decide +kernel

theorem g32p_integrationSquare010_integral : g32p_archiveIntegralWord g32p_integrationSquare010Word = g32p_integrationSquare010Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare010_certificate
  have hx : x = g32p_integrationSquare010Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare010_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_010 g32p_literalMatrix_010) g32p_integrationSquare010Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare010Matrix g32p_literalMatrix_035 := by
  decide +kernel

theorem g32p_integrationSquare010_actual : IsConj (g32p_literalRepresentative 10 * g32p_literalRepresentative 10)
    (g32p_literalRepresentative (g32p_familiesSquare 10)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare010Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_010 g32p_literalMatrix_010) g32p_literalMatrix_035 g32p_integrationSquare010Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_010) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_010) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 35) = _
    exact g32p_literalRepresentative_matrix 35
  · exact g32p_integrationSquare010_integral
  · exact g32p_integrationSquare010_equation

def g32p_integrationSquare011Word : List (Fin 4) := []

def g32p_integrationSquare011Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare011Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare011_certificate : g32p_archiveWordCertificate g32p_integrationSquare011Word g32p_integrationSquare011Stages = true := by
  decide +kernel

theorem g32p_integrationSquare011_integral : g32p_archiveIntegralWord g32p_integrationSquare011Word = g32p_integrationSquare011Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare011_certificate
  have hx : x = g32p_integrationSquare011Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare011_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_011 g32p_literalMatrix_011) g32p_integrationSquare011Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare011Matrix g32p_literalMatrix_004 := by
  decide +kernel

theorem g32p_integrationSquare011_actual : IsConj (g32p_literalRepresentative 11 * g32p_literalRepresentative 11)
    (g32p_literalRepresentative (g32p_familiesSquare 11)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare011Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_011 g32p_literalMatrix_011) g32p_literalMatrix_004 g32p_integrationSquare011Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_011) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_011) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 4) = _
    exact g32p_literalRepresentative_matrix 4
  · exact g32p_integrationSquare011_integral
  · exact g32p_integrationSquare011_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare012Word : List (Fin 4) := []

def g32p_integrationSquare012Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare012Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare012_certificate : g32p_archiveWordCertificate g32p_integrationSquare012Word g32p_integrationSquare012Stages = true := by
  decide +kernel

theorem g32p_integrationSquare012_integral : g32p_archiveIntegralWord g32p_integrationSquare012Word = g32p_integrationSquare012Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare012_certificate
  have hx : x = g32p_integrationSquare012Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare012_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_012 g32p_literalMatrix_012) g32p_integrationSquare012Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare012Matrix g32p_literalMatrix_036 := by
  decide +kernel

theorem g32p_integrationSquare012_actual : IsConj (g32p_literalRepresentative 12 * g32p_literalRepresentative 12)
    (g32p_literalRepresentative (g32p_familiesSquare 12)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare012Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_012 g32p_literalMatrix_012) g32p_literalMatrix_036 g32p_integrationSquare012Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_012) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_012) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 36) = _
    exact g32p_literalRepresentative_matrix 36
  · exact g32p_integrationSquare012_integral
  · exact g32p_integrationSquare012_equation

def g32p_integrationSquare013Word : List (Fin 4) := []

def g32p_integrationSquare013Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare013Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare013_certificate : g32p_archiveWordCertificate g32p_integrationSquare013Word g32p_integrationSquare013Stages = true := by
  decide +kernel

theorem g32p_integrationSquare013_integral : g32p_archiveIntegralWord g32p_integrationSquare013Word = g32p_integrationSquare013Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare013_certificate
  have hx : x = g32p_integrationSquare013Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare013_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_013 g32p_literalMatrix_013) g32p_integrationSquare013Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare013Matrix g32p_literalMatrix_037 := by
  decide +kernel

theorem g32p_integrationSquare013_actual : IsConj (g32p_literalRepresentative 13 * g32p_literalRepresentative 13)
    (g32p_literalRepresentative (g32p_familiesSquare 13)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare013Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_013 g32p_literalMatrix_013) g32p_literalMatrix_037 g32p_integrationSquare013Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_013) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_013) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 37) = _
    exact g32p_literalRepresentative_matrix 37
  · exact g32p_integrationSquare013_integral
  · exact g32p_integrationSquare013_equation

def g32p_integrationSquare014Word : List (Fin 4) := [1, 1, 2, 2]

def g32p_integrationSquare014Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare014Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare014_certificate : g32p_archiveWordCertificate g32p_integrationSquare014Word g32p_integrationSquare014Stages = true := by
  decide +kernel

theorem g32p_integrationSquare014_integral : g32p_archiveIntegralWord g32p_integrationSquare014Word = g32p_integrationSquare014Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare014_certificate
  have hx : x = g32p_integrationSquare014Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare014_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_014 g32p_literalMatrix_014) g32p_integrationSquare014Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare014Matrix g32p_literalMatrix_009 := by
  decide +kernel

theorem g32p_integrationSquare014_actual : IsConj (g32p_literalRepresentative 14 * g32p_literalRepresentative 14)
    (g32p_literalRepresentative (g32p_familiesSquare 14)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare014Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_014 g32p_literalMatrix_014) g32p_literalMatrix_009 g32p_integrationSquare014Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_014) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_014) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 9) = _
    exact g32p_literalRepresentative_matrix 9
  · exact g32p_integrationSquare014_integral
  · exact g32p_integrationSquare014_equation

def g32p_integrationSquare015Word : List (Fin 4) := [2]

def g32p_integrationSquare015Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

def g32p_integrationSquare015Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare015_certificate : g32p_archiveWordCertificate g32p_integrationSquare015Word g32p_integrationSquare015Stages = true := by
  decide +kernel

theorem g32p_integrationSquare015_integral : g32p_archiveIntegralWord g32p_integrationSquare015Word = g32p_integrationSquare015Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare015_certificate
  have hx : x = g32p_integrationSquare015Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare015_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_015 g32p_literalMatrix_015) g32p_integrationSquare015Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare015Matrix g32p_literalMatrix_045 := by
  decide +kernel

theorem g32p_integrationSquare015_actual : IsConj (g32p_literalRepresentative 15 * g32p_literalRepresentative 15)
    (g32p_literalRepresentative (g32p_familiesSquare 15)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare015Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_015 g32p_literalMatrix_015) g32p_literalMatrix_045 g32p_integrationSquare015Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_015) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_015) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 45) = _
    exact g32p_literalRepresentative_matrix 45
  · exact g32p_integrationSquare015_integral
  · exact g32p_integrationSquare015_equation

def g32p_integrationSquare016Word : List (Fin 4) := [1, 1, 2, 0, 0, 3, 2, 2]

def g32p_integrationSquare016Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare016Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare016_certificate : g32p_archiveWordCertificate g32p_integrationSquare016Word g32p_integrationSquare016Stages = true := by
  decide +kernel

theorem g32p_integrationSquare016_integral : g32p_archiveIntegralWord g32p_integrationSquare016Word = g32p_integrationSquare016Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare016_certificate
  have hx : x = g32p_integrationSquare016Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare016_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_016 g32p_literalMatrix_016) g32p_integrationSquare016Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare016Matrix g32p_literalMatrix_026 := by
  decide +kernel

theorem g32p_integrationSquare016_actual : IsConj (g32p_literalRepresentative 16 * g32p_literalRepresentative 16)
    (g32p_literalRepresentative (g32p_familiesSquare 16)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare016Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_016 g32p_literalMatrix_016) g32p_literalMatrix_026 g32p_integrationSquare016Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_016) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_016) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 26) = _
    exact g32p_literalRepresentative_matrix 26
  · exact g32p_integrationSquare016_integral
  · exact g32p_integrationSquare016_equation

def g32p_integrationSquare017Word : List (Fin 4) := [3, 0, 0, 3, 0]

def g32p_integrationSquare017Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare017Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare017_certificate : g32p_archiveWordCertificate g32p_integrationSquare017Word g32p_integrationSquare017Stages = true := by
  decide +kernel

theorem g32p_integrationSquare017_integral : g32p_archiveIntegralWord g32p_integrationSquare017Word = g32p_integrationSquare017Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare017_certificate
  have hx : x = g32p_integrationSquare017Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare017_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_017 g32p_literalMatrix_017) g32p_integrationSquare017Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare017Matrix g32p_literalMatrix_051 := by
  decide +kernel

theorem g32p_integrationSquare017_actual : IsConj (g32p_literalRepresentative 17 * g32p_literalRepresentative 17)
    (g32p_literalRepresentative (g32p_familiesSquare 17)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare017Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_017 g32p_literalMatrix_017) g32p_literalMatrix_051 g32p_integrationSquare017Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_017) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_017) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 51) = _
    exact g32p_literalRepresentative_matrix 51
  · exact g32p_integrationSquare017_integral
  · exact g32p_integrationSquare017_equation

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_integrationSquare018Word : List (Fin 4) := []

def g32p_integrationSquare018Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare018Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare018_certificate : g32p_archiveWordCertificate g32p_integrationSquare018Word g32p_integrationSquare018Stages = true := by
  decide +kernel

theorem g32p_integrationSquare018_integral : g32p_archiveIntegralWord g32p_integrationSquare018Word = g32p_integrationSquare018Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare018_certificate
  have hx : x = g32p_integrationSquare018Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare018_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_018 g32p_literalMatrix_018) g32p_integrationSquare018Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare018Matrix g32p_literalMatrix_000 := by
  decide +kernel

theorem g32p_integrationSquare018_actual : IsConj (g32p_literalRepresentative 18 * g32p_literalRepresentative 18)
    (g32p_literalRepresentative (g32p_familiesSquare 18)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare018Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_018 g32p_literalMatrix_018) g32p_literalMatrix_000 g32p_integrationSquare018Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_018) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_018) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 0) = _
    exact g32p_literalRepresentative_matrix 0
  · exact g32p_integrationSquare018_integral
  · exact g32p_integrationSquare018_equation

def g32p_integrationSquare019Word : List (Fin 4) := [2, 1, 1, 0, 0, 3]

def g32p_integrationSquare019Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

def g32p_integrationSquare019Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare019_certificate : g32p_archiveWordCertificate g32p_integrationSquare019Word g32p_integrationSquare019Stages = true := by
  decide +kernel

theorem g32p_integrationSquare019_integral : g32p_archiveIntegralWord g32p_integrationSquare019Word = g32p_integrationSquare019Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare019_certificate
  have hx : x = g32p_integrationSquare019Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare019_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_019 g32p_literalMatrix_019) g32p_integrationSquare019Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare019Matrix g32p_literalMatrix_067 := by
  decide +kernel

theorem g32p_integrationSquare019_actual : IsConj (g32p_literalRepresentative 19 * g32p_literalRepresentative 19)
    (g32p_literalRepresentative (g32p_familiesSquare 19)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare019Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_019 g32p_literalMatrix_019) g32p_literalMatrix_067 g32p_integrationSquare019Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_019) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_019) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 67) = _
    exact g32p_literalRepresentative_matrix 67
  · exact g32p_integrationSquare019_integral
  · exact g32p_integrationSquare019_equation

def g32p_integrationSquare020Word : List (Fin 4) := [1, 1]

def g32p_integrationSquare020Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare020Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare020_certificate : g32p_archiveWordCertificate g32p_integrationSquare020Word g32p_integrationSquare020Stages = true := by
  decide +kernel

theorem g32p_integrationSquare020_integral : g32p_archiveIntegralWord g32p_integrationSquare020Word = g32p_integrationSquare020Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare020_certificate
  have hx : x = g32p_integrationSquare020Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare020_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_020 g32p_literalMatrix_020) g32p_integrationSquare020Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare020Matrix g32p_literalMatrix_023 := by
  decide +kernel

theorem g32p_integrationSquare020_actual : IsConj (g32p_literalRepresentative 20 * g32p_literalRepresentative 20)
    (g32p_literalRepresentative (g32p_familiesSquare 20)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare020Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_020 g32p_literalMatrix_020) g32p_literalMatrix_023 g32p_integrationSquare020Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_020) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_020) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 23) = _
    exact g32p_literalRepresentative_matrix 23
  · exact g32p_integrationSquare020_integral
  · exact g32p_integrationSquare020_equation

def g32p_integrationSquare021Word : List (Fin 4) := [1, 1, 2, 3, 2]

def g32p_integrationSquare021Matrix : HurwitzPrymRex_Mat := ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare021Stages : List HurwitzPrymRex_Mat :=
  [![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]],
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare021_certificate : g32p_archiveWordCertificate g32p_integrationSquare021Word g32p_integrationSquare021Stages = true := by
  decide +kernel

theorem g32p_integrationSquare021_integral : g32p_archiveIntegralWord g32p_integrationSquare021Word = g32p_integrationSquare021Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare021_certificate
  have hx : x = g32p_integrationSquare021Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare021_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_021 g32p_literalMatrix_021) g32p_integrationSquare021Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare021Matrix g32p_literalMatrix_024 := by
  decide +kernel

theorem g32p_integrationSquare021_actual : IsConj (g32p_literalRepresentative 21 * g32p_literalRepresentative 21)
    (g32p_literalRepresentative (g32p_familiesSquare 21)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare021Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_021 g32p_literalMatrix_021) g32p_literalMatrix_024 g32p_integrationSquare021Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_021) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_021) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 24) = _
    exact g32p_literalRepresentative_matrix 24
  · exact g32p_integrationSquare021_integral
  · exact g32p_integrationSquare021_equation

def g32p_integrationSquare022Word : List (Fin 4) := [3, 2, 2, 0, 0, 1, 0]

def g32p_integrationSquare022Matrix : HurwitzPrymRex_Mat := ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

def g32p_integrationSquare022Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]],
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]],
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]],
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]],
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]],
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare022_certificate : g32p_archiveWordCertificate g32p_integrationSquare022Word g32p_integrationSquare022Stages = true := by
  decide +kernel

theorem g32p_integrationSquare022_integral : g32p_archiveIntegralWord g32p_integrationSquare022Word = g32p_integrationSquare022Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare022_certificate
  have hx : x = g32p_integrationSquare022Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare022_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_022 g32p_literalMatrix_022) g32p_integrationSquare022Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare022Matrix g32p_literalMatrix_073 := by
  decide +kernel

theorem g32p_integrationSquare022_actual : IsConj (g32p_literalRepresentative 22 * g32p_literalRepresentative 22)
    (g32p_literalRepresentative (g32p_familiesSquare 22)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare022Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_022 g32p_literalMatrix_022) g32p_literalMatrix_073 g32p_integrationSquare022Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_022) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_022) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 73) = _
    exact g32p_literalRepresentative_matrix 73
  · exact g32p_integrationSquare022_integral
  · exact g32p_integrationSquare022_equation

def g32p_integrationSquare023Word : List (Fin 4) := []

def g32p_integrationSquare023Matrix : HurwitzPrymRex_Mat := ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

def g32p_integrationSquare023Stages : List HurwitzPrymRex_Mat :=
  [![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]]

theorem g32p_integrationSquare023_certificate : g32p_archiveWordCertificate g32p_integrationSquare023Word g32p_integrationSquare023Stages = true := by
  decide +kernel

theorem g32p_integrationSquare023_integral : g32p_archiveIntegralWord g32p_integrationSquare023Word = g32p_integrationSquare023Matrix := by
  obtain ⟨x, rest, hs, hv⟩ := g32p_archiveWordCertificate_sound _ _ g32p_integrationSquare023_certificate
  have hx : x = g32p_integrationSquare023Stages.headD HurwitzPrymRex_mone := by rw [hs]; rfl
  rw [hv, hx]
  rfl

theorem g32p_integrationSquare023_equation :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul g32p_literalMatrix_023 g32p_literalMatrix_023) g32p_integrationSquare023Matrix =
      HurwitzPrymRex_mmul g32p_integrationSquare023Matrix g32p_literalMatrix_076 := by
  decide +kernel

theorem g32p_integrationSquare023_actual : IsConj (g32p_literalRepresentative 23 * g32p_literalRepresentative 23)
    (g32p_literalRepresentative (g32p_familiesSquare 23)) := by
  apply g32p_integration_isConj_of_matrix _ _ g32p_integrationSquare023Word
    (HurwitzPrymRex_mmul g32p_literalMatrix_023 g32p_literalMatrix_023) g32p_literalMatrix_076 g32p_integrationSquare023Matrix
  · rw [map_mul, g32p_literalRepresentative_matrix]
    change HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_023) *
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_literalMatrix_023) = _
    rw [← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  · change b4b_toMatrix (g32p_literalRepresentative 76) = _
    exact g32p_literalRepresentative_matrix 76
  · exact g32p_integrationSquare023_integral
  · exact g32p_integrationSquare023_equation

end HodgeLean.Foundations.Program

end
end
