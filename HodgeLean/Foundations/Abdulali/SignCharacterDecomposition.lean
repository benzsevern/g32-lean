import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum

noncomputable section
namespace HodgeLean.Foundations.Abdulali

/-- An element outside the kernel of a sign character separates its two sectors.
Source: Weyl, The Classical Groups, Chapter II, orthogonal invariant theory;
the index-two character decomposition over a field of characteristic zero. -/
theorem sign_character_fixed_decomposition
    {G T : Type*} [Group G] [AddCommGroup T] [Module ℂ T]
    (ρ : G →* Module.End ℂ T) (χ : G →* ℂ)
    (hχ : ∀ g, χ g = 1 ∨ χ g = -1)
    (s : G) (hχs : χ s = -1) :
    (⨅ g : G, ⨅ (_ : χ g = 1), LinearMap.ker (ρ g - LinearMap.id)) =
      (⨅ g : G, LinearMap.ker (ρ g - LinearMap.id)) ⊔
      (⨅ g : G, LinearMap.ker (ρ g - χ g • LinearMap.id)) := by
  classical
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx
    have hss (v : T) : ρ s (ρ s⁻¹ v) = v := by
      change (ρ s * ρ s⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have hχsi : χ s⁻¹ = -1 := by
      rcases hχ s⁻¹ with h | h
      · have hh := χ.map_mul s s⁻¹
        rw [mul_inv_cancel, map_one, hχs, h] at hh
        norm_num at hh
      · exact h
    have haction (g : G) (hg : χ g = -1) :
        ρ g x = ρ s x ∧ ρ g (ρ s x) = x := by
      have hgs := hx (g * s) (by rw [map_mul, hg, hχs]; norm_num)
      have hsg := hx (s⁻¹ * g) (by rw [map_mul, hχsi, hg]; norm_num)
      have hsg' : ρ s⁻¹ (ρ g x) = x := by
        simpa only [map_mul, Module.End.mul_apply] using hsg
      refine ⟨?_, ?_⟩
      · have hh := congrArg (ρ s) hsg'
        simpa only [hss] using hh
      · simpa only [map_mul, Module.End.mul_apply] using hgs
    have hplus : (2 : ℂ)⁻¹ • (x + ρ s x) ∈
        ⨅ g : G, LinearMap.ker (ρ g - LinearMap.id) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      rcases hχ g with hg | hg
      · have hconj : χ (s⁻¹ * g * s) = 1 := by
          rw [map_mul, map_mul, hχsi, hg, hχs]; norm_num
        have hh := congrArg (ρ s) (hx (s⁻¹ * g * s) hconj)
        have hy : ρ g (ρ s x) = ρ s x := by
          simpa only [map_mul, Module.End.mul_apply, hss] using hh
        rw [map_smul, map_add, hx g hg, hy]
      · obtain ⟨h₁, h₂⟩ := haction g hg
        rw [map_smul, map_add, h₁, h₂, add_comm]
    have hminus : (2 : ℂ)⁻¹ • (x - ρ s x) ∈
        ⨅ g : G, LinearMap.ker (ρ g - χ g • LinearMap.id) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      intro g
      rcases hχ g with hg | hg
      · have hconj : χ (s⁻¹ * g * s) = 1 := by
          rw [map_mul, map_mul, hχsi, hg, hχs]; norm_num
        have hh := congrArg (ρ s) (hx (s⁻¹ * g * s) hconj)
        have hy : ρ g (ρ s x) = ρ s x := by
          simpa only [map_mul, Module.End.mul_apply, hss] using hh
        rw [map_smul, map_sub, hx g hg, hy, hg, one_smul]
      · obtain ⟨h₁, h₂⟩ := haction g hg
        rw [map_smul, map_sub, h₁, h₂, hg, neg_one_smul, ← smul_neg,
          neg_sub]
    have hadd : (2 : ℂ)⁻¹ • (x + ρ s x) + (2 : ℂ)⁻¹ • (x - ρ s x) = x := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ x, smul_smul,
        inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
    exact hadd ▸ Submodule.add_mem_sup hplus hminus
  · apply sup_le
    · intro x hx
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hx ⊢
      exact fun g _ => hx g
    · intro x hx
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
      intro g hg
      simpa only [hg, one_smul] using hx g

end HodgeLean.Foundations.Abdulali
