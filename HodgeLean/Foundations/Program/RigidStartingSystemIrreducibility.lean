import HodgeLean.Foundations.Program.RigidStartingSystemIrreducibleCertificates

noncomputable section
open Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b65r_four_point_irreducible
    (W : Submodule ℂ (Fin 4 → ℂ))
    (hW : ∀ i v, v ∈ W → (b4b_toMatrix (b4b_generators i)).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  let w := g32h_omega
  have hw : w^2+w+1=0 := g32h_omega_sq_add
  have h0 (v : Fin 4 → ℂ) (hv : v ∈ W) : (g32R1 w).mulVec v ∈ W := hW 0 v hv
  have h1 (v : Fin 4 → ℂ) (hv : v ∈ W) : (g32R2 w).mulVec v ∈ W := hW 1 v hv
  have h2 (v : Fin 4 → ℂ) (hv : v ∈ W) : (g32X w).mulVec v ∈ W := hW 2 v hv
  have hleft (i : Fin 4) (v : Fin 4 → ℂ) (hv : v ∈ W) :
      (b65r_leftWords w i).mulVec v ∈ W := by
    fin_cases i
    · change (1 : Matrix (Fin 4) (Fin 4) ℂ).mulVec v ∈ W
      simpa only [one_mulVec] using hv
    · exact h1 v hv
    · exact h2 v hv
    · change (g32X w * g32R2 w).mulVec v ∈ W
      rw [← mulVec_mulVec]
      exact h2 _ (h1 _ hv)
  have hright (i : Fin 4) (v : Fin 4 → ℂ) (hv : v ∈ W) :
      (b65r_rightWords w i).mulVec v ∈ W := by
    fin_cases i
    · change (1 : Matrix (Fin 4) (Fin 4) ℂ).mulVec v ∈ W
      simpa only [one_mulVec] using hv
    · exact h1 v hv
    · exact h2 v hv
    · change (g32R2 w * g32X w).mulVec v ∈ W
      rw [← mulVec_mulVec]
      exact h1 _ (h2 _ hv)
  obtain ⟨v, hv, hv0⟩ := W.ne_bot_iff.mp hbot
  have hBv : (b65r_cyclicRows w).mulVec v ≠ 0 := by
    intro hz
    have he := congrArg (Matrix.mulVec (b65r_cyclicRowsInverse w)) hz
    rw [mulVec_mulVec, mul_eq_one_comm.mp (b65r_cyclic_rows_inverse w hw),
      one_mulVec, mulVec_zero] at he
    exact hv0 he
  obtain ⟨j, hj⟩ : ∃ j, ((b65r_cyclicRows w).mulVec v) j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hBv
    exact funext hn
  have hu : b65r_reflectionVector w ∈ W := by
    have hrv := hright j v hv
    have hp : (g32R1 w - 1).mulVec ((b65r_rightWords w j).mulVec v) ∈ W := by
      rw [sub_mulVec, one_mulVec]
      exact W.sub_mem (h0 _ hrv) hrv
    rw [b65r_reflection_rank_one w hw, vecMulVec_mulVec, op_smul_eq_smul,
      dotProduct_mulVec, ← b65r_cyclic_rows w hw j] at hp
    change (((b65r_cyclicRows w).mulVec v) j) • b65r_reflectionVector w ∈ W at hp
    have hs := W.smul_mem ((((b65r_cyclicRows w).mulVec v) j)⁻¹) hp
    simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using hs
  apply Submodule.eq_top_iff'.mpr
  intro z
  have hz : z = ∑ i : Fin 4,
      ((b65r_cyclicColumnsInverse w).mulVec z) i • (b65r_cyclicColumns w)ᵀ i := by
    calc
      z = (b65r_cyclicColumns w).mulVec ((b65r_cyclicColumnsInverse w).mulVec z) := by
        rw [mulVec_mulVec, b65r_cyclic_columns_inverse w hw, one_mulVec]
      _ = _ := by simp only [mulVec_eq_sum, op_smul_eq_smul]
  rw [hz]
  apply W.sum_mem
  intro i _
  apply W.smul_mem
  rw [b65r_cyclic_columns w hw i]
  exact hleft i _ hu

end HodgeLean.Foundations.Program
