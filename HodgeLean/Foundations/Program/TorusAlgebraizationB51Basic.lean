import HodgeLean.Foundations.Program.TorusAlgebraizationDefs
import HodgeLean.Foundations.Program.RelativeTorusAbelianLattice

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b5_lift_mem_conj (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (z : b5_V Λ F) :
    b5_lift Λ F hF z ∈ b2_conjSubmodule Λ F := by
  exact Submodule.coe_mem _

theorem b5_conj_lift_mem (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (z : b5_V Λ F) :
    b2_conj Λ (b5_lift Λ F hF z) ∈ F := by
  exact b2a_conj_mem_of_mem_conjSubmodule (b5_lift_mem_conj Λ F hF z)

theorem b5_lift_injective (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    Function.Injective (b5_lift Λ F hF) := by
  intro z w h
  exact (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).symm.injective
    ((F.quotientEquivOfIsCompl (b2_conjSubmodule Λ F) hF).injective (Subtype.ext h))

theorem b5_lift_lattice_decomposition (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (l : Λ) :
    (1 : ℂ) ⊗ₜ[ℤ] l = b2_conj Λ (b5_lift Λ F hF (b5_lattice Λ F l)) +
      b5_lift Λ F hF (b5_lattice Λ F l) := by
  let x : ℂ ⊗[ℤ] Λ := (1 : ℂ) ⊗ₜ[ℤ] l
  let g : ℂ ⊗[ℤ] Λ := b5_lift Λ F hF (b5_lattice Λ F l)
  let f : ℂ ⊗[ℤ] Λ := F.projection (b2_conjSubmodule Λ F) hF x
  have hg : g = (b2_conjSubmodule Λ F).projection F hF.symm x := by
    dsimp [g, b5_lift, b5_lattice]
    simp only [LinearEquiv.restrictScalars_apply]
    rw [LinearEquiv.symm_apply_apply]
    have hl : b2_latticeMap Λ F l = Submodule.Quotient.mk x := rfl
    rw [hl]
    exact congrArg Subtype.val
      (Submodule.quotientEquivOfIsCompl_apply_mk hF x)
  have hf_mem : f ∈ F := Submodule.projection_apply_mem hF x
  have hg_mem : g ∈ b2_conjSubmodule Λ F := b5_lift_mem_conj Λ F hF _
  have hsum : f + g = x := by
    rw [hg]
    exact Submodule.projection_add_projection_eq_self hF x
  have hxconj : b2_conj Λ x = x := by
    exact b2a_conj_incl l
  have hconjsum : b2_conj Λ f + b2_conj Λ g = x := by
    rw [← map_add, hsum, hxconj]
  have hd_eq : f - b2_conj Λ g = b2_conj Λ f - g := by
    rw [sub_eq_sub_iff_add_eq_add]
    calc
      f + g = x := hsum
      _ = b2_conj Λ f + b2_conj Λ g := hconjsum.symm
  have hdF : f - b2_conj Λ g ∈ F :=
    sub_mem hf_mem (b2a_conj_mem_of_mem_conjSubmodule hg_mem)
  have hdC : f - b2_conj Λ g ∈ b2_conjSubmodule Λ F := by
    rw [hd_eq]
    exact sub_mem (b2a_conj_mem_conjSubmodule hf_mem) hg_mem
  have hd0 : f - b2_conj Λ g = 0 := by
    have hm : f - b2_conj Λ g ∈ F ⊓ b2_conjSubmodule Λ F := ⟨hdF, hdC⟩
    rw [hF.inf_eq_bot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  have hfg : f = b2_conj Λ g := sub_eq_zero.mp hd0
  change x = b2_conj Λ g + g
  rw [← hfg, hsum]

end HodgeLean.Foundations.Program
