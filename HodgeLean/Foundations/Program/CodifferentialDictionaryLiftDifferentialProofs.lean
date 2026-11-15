import HodgeLean.Foundations.Program.CodifferentialDictionaryProjectionDerivativeProofs
import HodgeLean.Foundations.Program.CodifferentialDictionaryProjectionTransitionProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b66d_projectionCoeff_lift_differential
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a : b66f_Index D)
    (z : ℂ) (hz : z ∈ b66f_domain D t a)
    (hreg : D.atlas.f ((D.atlas.A a).symm (t.val, z)).2 ∉ Set.range (b6_branch c)) :
    ∃ F' : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ,
      HasFDerivAt (b66d_projectionCoeff D a) F' (t.val, z) ∧ F' (0, 1) ≠ 0 ∧
      ∀ k : Fin 10, F' (Pi.single k 1, 0) / F' (0, 1) = b66d_branchLift D k a z := by
  by_cases hfree : D.atlas.f a.2 ∉ Set.range (b6_branch c)
  · refine ⟨ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ,
      b66d_projectionCoeff_free_hasFDerivAt D a hfree _ hz, by norm_num, ?_⟩
    intro k
    have hne : D.atlas.f a.2 ≠ b6_branch c (Fin.castLE (by norm_num) k) :=
      fun h => hfree ⟨_, h.symm⟩
    simp [b66d_branchLift, hne]
  · obtain ⟨j, hj⟩ := Set.mem_range.mp (not_not.mp hfree)
    have heq := hj.symm
    have hzne := b66d_branchChart_nonzero D t a j heq z hz hreg
    have hn : (D.atlas.n a.2 : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (D.atlas.hn a.2))
    have hfixed (hjlt : ¬j.val < 10) (k : Fin 10) :
        D.atlas.f a.2 ≠ b6_branch c (Fin.castLE (by norm_num) k) := by
      intro he
      have hval := congrArg Fin.val (D.atlas.hb (heq.symm.trans he))
      simp only [Fin.val_castLE] at hval
      omega
    by_cases hinf : j.val = 12
    · let γ : ℂ := -((z ^ D.atlas.n a.2) ^ 2)⁻¹ *
        ((D.atlas.n a.2 : ℂ) * z ^ (D.atlas.n a.2 - 1))
      have hγ : γ ≠ 0 := mul_ne_zero
        (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (pow_ne_zero _ hzne))))
        (mul_ne_zero hn (pow_ne_zero _ hzne))
      refine ⟨γ • ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ,
        b66d_projectionCoeff_infinite_hasFDerivAt D a j heq hinf (t.val, z) hz hzne, ?_, ?_⟩
      · change γ * 1 ≠ 0
        simpa only [mul_one] using hγ
      · intro k
        have hk := hfixed (by omega) k
        simp [b66d_branchLift, hk]
    · let γ : ℂ := (D.atlas.n a.2 : ℂ) * z ^ (D.atlas.n a.2 - 1)
      have hγ : γ ≠ 0 := mul_ne_zero hn (pow_ne_zero _ hzne)
      have hshiftz : b66d_shiftD j (0, 1) = 0 := by
        unfold b66d_shiftD
        split_ifs <;> rfl
      refine ⟨b66d_shiftD j + γ • ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ,
        b66d_projectionCoeff_finite_hasFDerivAt D a j heq hinf (t.val, z) hz, ?_, ?_⟩
      · change b66d_shiftD j (0, 1) + γ * 1 ≠ 0
        rwa [hshiftz, zero_add, mul_one]
      · intro k
        change (b66d_shiftD j (Pi.single k 1, 0) + γ * 0) /
          (b66d_shiftD j (0, 1) + γ * 1) = _
        rw [hshiftz, zero_add, mul_one, mul_zero, add_zero]
        by_cases hjlt : j.val < 10
        · simp only [b66d_shiftD, dite_eq_left hjlt]
          change (Pi.single k 1 : Fin 10 → ℂ) ⟨j.val, hjlt⟩ / γ = _
          by_cases hk : (⟨j.val, hjlt⟩ : Fin 10) = k
          · have he : D.atlas.f a.2 = b6_branch c (Fin.castLE (by norm_num) k) := by
              apply heq.trans
              apply congrArg (b6_branch c)
              exact Fin.ext (congrArg (fun i : Fin 10 => i.val) hk)
            simp [b66d_branchLift, he, ← hk, one_div, γ]
          · have he : D.atlas.f a.2 ≠ b6_branch c (Fin.castLE (by norm_num) k) := by
              intro he
              apply hk
              exact Fin.ext (congrArg (fun i : Fin 13 => i.val) (D.atlas.hb (heq.symm.trans he)))
            simp [b66d_branchLift, he, Pi.single_apply, hk, Ne.symm hk]
        · have he := hfixed hjlt k
          simp [b66d_shiftD, hjlt, b66d_branchLift, he]

end HodgeLean.Foundations.Program
