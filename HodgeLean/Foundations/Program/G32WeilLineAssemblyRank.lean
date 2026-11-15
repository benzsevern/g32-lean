import HodgeLean.Foundations.Program.G32WeilLineAssemblyPrimitive
import HodgeLean.Foundations.Program.G32RepWeilProofs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
open CategoryTheory HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

theorem g32c_chi_nontrivial (S : g32p_Supplier) :
    ∃ h : S.H, g32rep_chi S h ≠ 1 := by
  obtain ⟨h, hh⟩ := S.surjective (Multiplicative.ofAdd 1)
  refine ⟨h, fun he => ?_⟩
  have hv := congrArg (fun z : ℂˣ => (z : ℂ)) he
  rw [g32rep_chi_apply, hh] at hv
  have : Fact (1 < S.m) := ⟨by have := S.three_le; omega⟩
  have hval : (1 : ZMod S.m).val = 1 := ZMod.val_one S.m
  change g32p_root S.m ^ (1 : ZMod S.m).val = 1 at hv
  rw [hval, pow_one] at hv
  have hd := (g32rep_root_prim S.m (NeZero.ne S.m)).pow_eq_one_iff_dvd 1
  have : S.m ∣ 1 := hd.mp (by simpa only [pow_one] using hv)
  have := Nat.le_of_dvd (by omega : 0 < 1) this
  have := S.three_le
  omega

theorem g32c_trivial_eigen_bot (S : g32p_Supplier) (σ : FDRep ℂ g32p_G)
    (htr : ∀ g, σ.ρ g = 1) :
    rfd_eigen σ.ρ S.H (g32rep_chi S) = ⊥ := by
  obtain ⟨h, hh⟩ := g32c_chi_nontrivial S
  refine le_antisymm ?_ bot_le
  intro v hv
  have he := hv h
  rw [htr] at he
  change v = ((g32rep_chi S h : ℂˣ) : ℂ) • v at he
  have hc : ((g32rep_chi S h : ℂˣ) : ℂ) ≠ 1 := by
    intro hc
    exact hh (Units.ext hc)
  have hz : (((g32rep_chi S h : ℂˣ) : ℂ) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

theorem g32c_eigen_rank_sum {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {I : Type} [Fintype I] (σ : I → FDRep ℂ G) (ρ : Representation ℂ G V)
    (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ σ i))
    (H : Subgroup G) (χ : H →* ℂˣ) :
    Module.finrank ℂ (rfd_eigen ρ H χ) =
      ∑ i, papersMult H (σ i) χ * Module.finrank ℂ (rfd_mult (σ i) ρ) := by
  have he := (LinearEquiv.ofBijective (rfd_eigenEval σ ρ H χ)
    (rfd_eigenEval_bijective σ ρ hσ hdist hcov H χ)).finrank_eq
  rw [Module.finrank_pi_fintype] at he
  simpa only [Module.finrank_tensorProduct, rfd_finrank_eigen_eq_papersMult] using he.symm

theorem g32c_supplier_rank_cw (A : g32t_Sixfold) (X : g32p_Cover A)
    (S : g32p_Supplier) {I : Type} [Fintype I] (σ : I → FDRep ℂ g32p_G)
    (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ g32p_G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    (Module.finrank ℂ (rfd_eigen (g32rep_rep X) S.H (g32rep_chi S)) : ℂ) =
      ∑ i, (papersMult S.H (σ i) (g32rep_chi S) : ℂ) * (g32p_cwMult (σ i) : ℂ) := by
  classical
  let := (torusCohomology_cupProductOf X.J).finite
  rw [g32c_eigen_rank_sum σ (g32rep_rep X) hσ hdist hcov]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases hnt : ∃ g, (σ i).ρ g ≠ 1
  · rw [g32rep_mult_finrank X (σ i) (hσ i) hnt]
  · have htr : ∀ g, (σ i).ρ g = 1 := by simpa only [not_exists, not_not] using hnt
    have hz : papersMult S.H (σ i) (g32rep_chi S) = 0 := by
      rw [← rfd_finrank_eigen_eq_papersMult,
        g32c_trivial_eigen_bot S (σ i) htr, finrank_bot]
    rw [hz, Nat.cast_zero, zero_mul, zero_mul]

theorem g32c_supplier_rank_cw_int (A : g32t_Sixfold) (X : g32p_Cover A)
    (S : g32p_Supplier) {I : Type} [Fintype I] (σ : I → FDRep ℂ g32p_G)
    (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ g32p_G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    (Module.finrank ℂ (rfd_eigen (g32rep_rep X) S.H (g32rep_chi S)) : ℤ) =
      ∑ i, (papersMult S.H (σ i) (g32rep_chi S) : ℤ) * g32p_cwMult (σ i) := by
  exact_mod_cast g32c_supplier_rank_cw A X S σ hσ hdist hcov

theorem g32c_supplier_rank_positive_iff (A : g32t_Sixfold) (X : g32p_Cover A)
    (S : g32p_Supplier) {I : Type} [Fintype I] (σ : I → FDRep ℂ g32p_G)
    (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ g32p_G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    0 < Module.finrank ℂ (rfd_eigen (g32rep_rep X) S.H (g32rep_chi S)) ↔
      0 < ∑ i, (papersMult S.H (σ i) (g32rep_chi S) : ℤ) * g32p_cwMult (σ i) := by
  rw [← g32c_supplier_rank_cw_int A X S σ hσ hdist hcov]
  exact_mod_cast (Iff.rfl :
    0 < Module.finrank ℂ (rfd_eigen (g32rep_rep X) S.H (g32rep_chi S)) ↔ _)

end HodgeLean.Foundations.Program
