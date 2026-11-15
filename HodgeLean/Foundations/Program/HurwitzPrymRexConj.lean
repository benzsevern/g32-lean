import HodgeLean.Foundations.Program.HurwitzPrymCovHodge
import HodgeLean.Foundations.Program.RelativeTorusAlg

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: characters in `F̄` are conjugate characters in `F`

For a character `χ` of `G` acting on `ℂ ⊗ Λ` through lattice maps, the `χ`-eigenvectors in the
conjugate subspace `F̄` are the conjugates of the `χ̄`-eigenvectors in `F`. Hence the multiplicity
of `χ` in `F̄` equals the multiplicity of `χ̄` in `F`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct ComplexConjugate

namespace HodgeLean.Foundations.Program

section Eigen

variable {G : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The `χ`-eigenvectors of `act` inside `W`.
Source: the definition of an eigenspace (Mathlib `Module.End.eigenspace`), one per group element. -/
def HurwitzPrymRex_eig (act : G → M →ₗ[ℂ] M) (W : Submodule ℂ M) (χ : G → ℂ) :
    Submodule ℂ M :=
  W ⊓ ⨅ g, LinearMap.ker (act g - χ g • LinearMap.id)

example (act : G → M →ₗ[ℂ] M) (W : Submodule ℂ M) (χ : G → ℂ) :
    HurwitzPrymRex_eig act W χ ≤ W := inf_le_left

theorem HurwitzPrymRex_mem_eig {act : G → M →ₗ[ℂ] M} {W : Submodule ℂ M} {χ : G → ℂ}
    {m : M} : m ∈ HurwitzPrymRex_eig act W χ ↔ m ∈ W ∧ ∀ g, act g m = χ g • m := by
  simp only [HurwitzPrymRex_eig, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

/-- **`G`-maps from a character are its eigenvectors.** -/
theorem HurwitzPrymRex_finrank_homG_char [Group G] (ρ : Representation ℂ G ℂ) (χ : G → ℂ)
    (hρ : ∀ g, ρ g = χ g • LinearMap.id) (act : G → M →ₗ[ℂ] M) (W : Submodule ℂ M) :
    Module.finrank ℂ (b4_HomG ρ act W) = Module.finrank ℂ (HurwitzPrymRex_eig act W χ) := by
  refine LinearEquiv.finrank_eq
    { toFun := fun φ ↦ ⟨φ.1 1, HurwitzPrymRex_mem_eig.2 ⟨φ.2.1 1, fun g ↦ by
        rw [← φ.2.2 g 1, hρ]
        simp only [LinearMap.smul_apply, LinearMap.id_apply]
        rw [← map_smul, smul_eq_mul, mul_one]⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun m ↦ ⟨LinearMap.toSpanSingleton ℂ M m,
        fun v ↦ W.smul_mem v (HurwitzPrymRex_mem_eig.1 m.2).1, fun g v ↦ by
          rw [hρ]
          simp only [LinearMap.smul_apply, LinearMap.id_apply,
            LinearMap.toSpanSingleton_apply, map_smul, (HurwitzPrymRex_mem_eig.1 m.2).2 g,
            smul_smul, smul_eq_mul, mul_comm]⟩
      left_inv := fun φ ↦ by
        apply Subtype.ext
        ext
        simp
      right_inv := fun m ↦ by
        apply Subtype.ext
        simp }

end Eigen

section Conj

variable {Λ : Type*} [AddCommGroup Λ]

theorem HurwitzPrymRex_cplxMap_conj (f : Λ →+ Λ) (v : ℂ ⊗[ℤ] Λ) :
    b2_cplxMap f (b2_conj Λ v) = b2_conj Λ (b2_cplxMap f v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable {G : Type*} [Group G]

/-- **Eigenvectors in `F̄` are conjugates of conjugate eigenvectors in `F`.** -/
theorem HurwitzPrymRex_eig_conjSubmodule (f : G → (Λ →+ Λ)) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (χ : G → ℂ) :
    HurwitzPrymRex_eig (fun g ↦ b2_cplxMap (f g)) (b2_conjSubmodule Λ F) χ =
      b2_conjSubmodule Λ (HurwitzPrymRex_eig (fun g ↦ b2_cplxMap (f g)) F
        (fun g ↦ conj (χ g))) := by
  ext w
  constructor
  · intro hw
    obtain ⟨hwF, hwχ⟩ := HurwitzPrymRex_mem_eig.1 hw
    obtain ⟨v, hv, rfl⟩ := b2a_mem_conjSubmodule.1 hwF
    refine b2a_conj_mem_conjSubmodule (HurwitzPrymRex_mem_eig.2 ⟨hv, fun g ↦ ?_⟩)
    have h := congrArg (b2_conj Λ) (hwχ g)
    rw [← HurwitzPrymRex_cplxMap_conj, b2a_conj_conj, b4cov_conj_smul, b2a_conj_conj] at h
    exact h
  · intro hw
    obtain ⟨v, hv, rfl⟩ := b2a_mem_conjSubmodule.1 hw
    obtain ⟨hvF, hvχ⟩ := HurwitzPrymRex_mem_eig.1 hv
    refine HurwitzPrymRex_mem_eig.2 ⟨b2a_conj_mem_conjSubmodule hvF, fun g ↦ ?_⟩
    change b2_cplxMap (f g) (b2_conj Λ v) = _
    rw [HurwitzPrymRex_cplxMap_conj, hvχ g, b4cov_conj_smul, Complex.conj_conj]

/-- **The multiplicity of `χ` in `F̄` is the multiplicity of `χ̄` in `F`.** -/
theorem HurwitzPrymRex_finrank_eig_conj [Module.Finite ℤ Λ] (f : G → (Λ →+ Λ))
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (χ : G → ℂ) :
    Module.finrank ℂ (HurwitzPrymRex_eig (fun g ↦ b2_cplxMap (f g)) (b2_conjSubmodule Λ F) χ) =
      Module.finrank ℂ (HurwitzPrymRex_eig (fun g ↦ b2_cplxMap (f g)) F
        (fun g ↦ conj (χ g))) := by
  rw [HurwitzPrymRex_eig_conjSubmodule, b2a_finrank_conjSubmodule]

end Conj

/-- The count of `i^a` and its conjugate `i^{3a}` among the characters `i^3`. -/
theorem HurwitzPrymRex_char4_count (a : ℕ) :
    ((if a % 4 = 3 then 1 else 0) + (if 3 * a % 4 = 3 then 1 else 0) : ℕ) =
      if a % 4 = 1 ∨ a % 4 = 3 then 1 else 0 := by
  rcases (by omega : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3) with h | h | h | h
  · have h3 : 3 * a % 4 = 0 := by omega
    simp only [h, h3]; decide
  · have h3 : 3 * a % 4 = 3 := by omega
    simp only [h, h3]; decide
  · have h3 : 3 * a % 4 = 2 := by omega
    simp only [h, h3]; decide
  · have h3 : 3 * a % 4 = 1 := by omega
    simp only [h, h3]; decide

end HodgeLean.Foundations.Program
