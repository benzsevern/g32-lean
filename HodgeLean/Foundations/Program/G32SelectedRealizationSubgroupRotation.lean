import HodgeLean.Foundations.Program.G32SelectedRealizationSubgroupActions

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_subgroup_rotGen_power {E C G : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (H : Subgroup G) (x : C) (g : G) (hg : b4_IsRotGen E x g)
    (l : ℕ) (hl : 0 < l) (hmem : g ^ l ∈ H)
    (hcard : orderOf g = l * Nat.card (MulAction.stabilizer H x)) :
    b4_IsRotGen E x (⟨g ^ l, hmem⟩ : H) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hfix : (g ^ l) • x = x := (MulAction.stabilizer G x).pow_mem hg.1 l
  obtain ⟨k, hk⟩ := b4_exists_rotGen hE (fun h : H ↦ hG h) x
  have hExp : Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ)) ^ l =
      Complex.exp (2 * Real.pi * Complex.I /
        (Nat.card (MulAction.stabilizer H x) : ℂ)) := by
    have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have hsC : (Nat.card (MulAction.stabilizer H x) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [← Complex.exp_nat_mul, hcard, Nat.cast_mul]
    congr 1
    field_simp [hlC, hsC]
  have heq : (k : G) = g ^ l := by
    have hs : (⟨(k : G), hk.1⟩ : MulAction.stabilizer G x) = ⟨g ^ l, hfix⟩ := by
      apply b4cov_lamHom_injective hE hG x
      change b4cov_lam hE x (k : G) = b4cov_lam hE x (g ^ l)
      calc
        b4cov_lam hE x (k : G) = Complex.exp (2 * Real.pi * Complex.I /
            (Nat.card (MulAction.stabilizer H x) : ℂ)) := by
          apply b4cov_lam_eq_of_apply hE x (k : G)
          intro v
          have hh := hk.2.2 v
          rw [hk.2.1] at hh
          exact hh
        _ = Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ)) ^ l := hExp.symm
        _ = b4cov_lam hE x (g ^ l) := (b4_lam_rotGen_pow hE hG x g hg l).symm
    exact congrArg Subtype.val hs
  have hkEq : k = (⟨g ^ l, hmem⟩ : H) := Subtype.ext heq
  rw [← hkEq]
  exact hk

end HodgeLean.Foundations.Program
