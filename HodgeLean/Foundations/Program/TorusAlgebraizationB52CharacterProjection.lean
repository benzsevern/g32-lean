import HodgeLean.Foundations.Program.TorusAlgebraizationB52ProjectionFormula
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

noncomputable section
namespace HodgeLean.Foundations.Program

variable {G : Type*} [AddCommGroup G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem b52_averageEnd_right_invariant
    (ρ : G →+ Additive (Module.End ℂ V)) (g : G) :
    b52_averageEnd ρ * (ρ g).toMul = b52_averageEnd ρ := by
  unfold b52_averageEnd
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  have hρ : ∀ h, (ρ h).toMul * (ρ g).toMul = (ρ (h + g)).toMul :=
    fun h ↦ (congrArg Additive.toMul (ρ.map_add h g)).symm
  simp_rw [hρ]
  exact Fintype.sum_equiv (Equiv.addRight g) _ _ (fun h ↦ rfl)

theorem b52_averageEnd_eq_zero_of_eigen
    (ρ : G →+ Additive (Module.End ℂ V)) (g : G) (v : V) (a : ℂ)
    (ha : a ≠ 1) (hv : (ρ g).toMul v = a • v) : b52_averageEnd ρ v = 0 := by
  have he := congrArg (fun T : Module.End ℂ V ↦ T v) (b52_averageEnd_right_invariant ρ g)
  change b52_averageEnd ρ ((ρ g).toMul v) = b52_averageEnd ρ v at he
  rw [hv, map_smul] at he
  have hz : (a - 1) • b52_averageEnd ρ v = 0 := by
    rw [sub_smul, one_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

def b52_scalarTwist (ρ : G →+ Additive (Module.End ℂ V))
    (χ : AddChar G ℂ) : G →+ Additive (Module.End ℂ V) where
  toFun g := Additive.ofMul (χ g • (ρ g).toMul)
  map_zero' := by simp
  map_add' g h := by
    change χ (g + h) • (ρ (g + h)).toMul =
      (χ g • (ρ g).toMul) * (χ h • (ρ h).toMul)
    simp only [map_add, AddChar.map_add_eq_mul]
    rw [smul_mul_smul_comm]
    rfl

def b52_characterProjection (ρ : G →+ Additive (Module.End ℂ V))
    (χ : AddChar G ℂ) : Module.End ℂ V := b52_averageEnd (b52_scalarTwist ρ χ)

theorem b52_characterProjection_range
    (ρ : G →+ Additive (Module.End ℂ V)) (χ : AddChar G ℂ) (v : V) :
    v ∈ LinearMap.range (b52_characterProjection ρ χ) ↔
      ∀ g, (ρ g).toMul v = (χ g)⁻¹ • v := by
  rw [b52_characterProjection, b52_mem_range_averageEnd_iff]
  have hχ : ∀ g, χ g ≠ 0 := by
    intro g hg
    have hh := χ.map_add_eq_mul g (-g)
    simp [hg] at hh
  constructor
  · intro hv g
    have hh := congrArg (fun w : V ↦ (χ g)⁻¹ • w) (hv g)
    change (χ g)⁻¹ • (χ g • (ρ g).toMul v) = (χ g)⁻¹ • v at hh
    simpa only [smul_smul, inv_mul_cancel₀ (hχ g), one_smul] using hh
  · intro hv g
    change χ g • (ρ g).toMul v = v
    rw [hv, smul_smul, mul_inv_cancel₀ (hχ g), one_smul]

theorem b52_sum_characterProjection (ρ : G →+ Additive (Module.End ℂ V)) :
    ∑ χ : AddChar G ℂ, b52_characterProjection ρ χ = 1 := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change ∑ χ : AddChar G ℂ, (Fintype.card G : ℂ)⁻¹ •
    ∑ g, χ g • (ρ g).toMul = 1
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, AddChar.sum_apply_eq_ite]
  simp [smul_smul, hc]

open scoped TensorProduct
variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

theorem b52_descentTrace_eq_zero_of_eigen (k n : ℕ) (hn : n ≠ 0)
    (t : b5_sections Λ F hF Q (k * n ^ 2)) (l : Λ) (a : ℂ)
    (ha : a ≠ 1) (ht : b52_descentTranslate Λ F hF Q k n l t.val = a • t.val) :
    b52_descentTrace Λ F hF Q hherm himag hcocycle k n hn t = 0 := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  let ρ := b52_descentQuotientHom Λ F hF Q hherm himag hcocycle k n hn
  have he : (ρ (QuotientAddGroup.mk l)).toMul t = a • t := Subtype.ext ht
  have hz : b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn t = 0 :=
    b52_averageEnd_eq_zero_of_eigen ρ (QuotientAddGroup.mk l) t a ha he
  apply Subtype.ext
  funext z
  change (b52_descentAverage Λ F hF Q hherm himag hcocycle k n hn t).val
    ((n : ℂ)⁻¹ • z) = 0
  rw [hz]
  rfl

theorem b52_trace_product_eq_zero_of_eigen (i j n : ℕ) (hn : n ≠ 0)
    (u : b5_sections Λ F hF Q (i * n ^ 2))
    (v : b5_sections Λ F hF Q (j * n ^ 2)) (l : Λ) (a b : ℂ)
    (hab : a * b ≠ 1)
    (hu : b52_descentTranslate Λ F hF Q i n l u.val = a • u.val)
    (hv : b52_descentTranslate Λ F hF Q j n l v.val = b • v.val) :
    b52_descentTrace Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductLeft Λ F hF Q i j n u v) = 0 := by
  apply b52_descentTrace_eq_zero_of_eigen Λ F hF Q hherm himag hcocycle
    (i + j) n hn _ l (a * b) hab
  change b52_descentTranslate Λ F hF Q (i + j) n l (u.val * v.val) =
    (a * b) • (u.val * v.val)
  rw [b52_descentTranslate_mul, hu, hv]
  funext z
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

end HodgeLean.Foundations.Program
