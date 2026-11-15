import HodgeLean.Foundations.Program.TorusAlgebraizationB52Isogeny
import Mathlib.GroupTheory.FiniteAbelian.Basic

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_descentTranslate (k n : ℕ) (l : Λ) :
    (b5_V Λ F → ℂ) →ₗ[ℂ] (b5_V Λ F → ℂ) where
  toFun f z := (b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k)⁻¹ *
    f (z + (n : ℂ)⁻¹ • b5_lattice Λ F l)
  map_add' f g := by ext z; simp [mul_add]
  map_smul' a f := by ext z; simp [mul_left_comm]

theorem b52_descentTranslate_eq_thetaTranslate (k n : ℕ) (hn : n ≠ 0) (l : Λ) :
    b52_descentTranslate Λ F hF Q k n l =
      (b5_factor Λ F hF Q l 0 ^ k)⁻¹ •
        b52_thetaTranslate Λ F hF Q (k * n ^ 2)
          ((n : ℂ)⁻¹ • b5_lattice Λ F l) := by
  have hne : ∀ z, b5_factor Λ F hF Q l z ≠ 0 := fun z ↦
    mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _)
  ext f z
  change (b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k)⁻¹ * _ =
    (b5_factor Λ F hF Q l 0 ^ k)⁻¹ *
      (Complex.exp (-(((k * n ^ 2 : ℕ) : ℂ) * Real.pi *
        b5_H Λ F hF Q ((n : ℂ)⁻¹ • b5_lattice Λ F l) z)) * _)
  have he := b52_fractional_translation_factor Λ F hF Q k n hn l z
  have he' : Complex.exp (-(((k * n ^ 2 : ℕ) : ℂ) * Real.pi *
      b5_H Λ F hF Q ((n : ℂ)⁻¹ • b5_lattice Λ F l) z)) =
        b5_factor Λ F hF Q l 0 ^ k /
          b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k :=
    (eq_div_iff (pow_ne_zero _ (hne _))).mpr he
  rw [he']
  field_simp [hne]

theorem b52_descentTranslate_add
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)
    (k n : ℕ) (hn : n ≠ 0) (l m : Λ) :
    b52_descentTranslate Λ F hF Q k n (l + m) =
      (b52_descentTranslate Λ F hF Q k n l).comp
        (b52_descentTranslate Λ F hF Q k n m) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  ext f z
  change (b5_factor Λ F hF Q (l + m) ((n : ℂ) • z) ^ k)⁻¹ *
    f (z + (n : ℂ)⁻¹ • b5_lattice Λ F (l + m)) =
    (b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k)⁻¹ *
      ((b5_factor Λ F hF Q m
        ((n : ℂ) • (z + (n : ℂ)⁻¹ • b5_lattice Λ F l)) ^ k)⁻¹ *
        f (z + (n : ℂ)⁻¹ • b5_lattice Λ F l + (n : ℂ)⁻¹ • b5_lattice Λ F m))
  rw [add_comm l m, hcocycle]
  simp only [map_add, smul_add, smul_smul, mul_inv_cancel₀ hn', one_smul,
    mul_pow, mul_inv_rev, mul_assoc, add_assoc, add_comm, add_left_comm]

theorem b52_descentTranslate_nsmul (k n : ℕ) (hn : n ≠ 0)
    (l : Λ) (t : b5_sections Λ F hF Q (k * n ^ 2)) :
    b52_descentTranslate Λ F hF Q k n (n • l) t.val = t.val := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hne : ∀ z, b5_factor Λ F hF Q l z ≠ 0 := fun z ↦
    mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _)
  funext z
  change (b5_factor Λ F hF Q (n • l) ((n : ℂ) • z) ^ k)⁻¹ *
    t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F (n • l)) = t.val z
  rw [b52_factor_dilation]
  simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hn', one_smul, ← pow_mul, Nat.mul_comm (n ^ 2) k]
  rw [t.property.2, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (hne z)), one_mul]

def b52_descentEnd
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (k n : ℕ) (hn : n ≠ 0) (l : Λ) :
    Module.End ℂ (b5_sections Λ F hF Q (k * n ^ 2)) :=
  (b52_descentTranslate Λ F hF Q k n l).restrict (by
    intro f hf
    rw [b52_descentTranslate_eq_thetaTranslate Λ F hF Q k n hn l]
    exact (b5_sections Λ F hF Q (k * n ^ 2)).smul_mem _
      (b52_fractional_translation_preserves_sections Λ F hF Q hherm himag k n hn l ⟨f, hf⟩))

def b52_descentLatticeHom
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)
    (k n : ℕ) (hn : n ≠ 0) :
    Λ →+ Additive (Module.End ℂ (b5_sections Λ F hF Q (k * n ^ 2))) where
  toFun l := Additive.ofMul (b52_descentEnd Λ F hF Q hherm himag k n hn l)
  map_zero' := by
    change b52_descentEnd Λ F hF Q hherm himag k n hn 0 = 1
    ext t z
    change (b52_descentTranslate Λ F hF Q k n 0 t.val) z = t.val z
    simpa only [nsmul_zero] using
      congrFun (b52_descentTranslate_nsmul Λ F hF Q k n hn 0 t) z
  map_add' l m := by
    change b52_descentEnd Λ F hF Q hherm himag k n hn (l + m) =
      b52_descentEnd Λ F hF Q hherm himag k n hn l *
        b52_descentEnd Λ F hF Q hherm himag k n hn m
    ext t z
    exact congrFun (congrArg (fun T ↦ T t.val)
      (b52_descentTranslate_add Λ F hF Q hcocycle k n hn l m)) z

def b52_descentQuotientHom
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)
    (k n : ℕ) (hn : n ≠ 0) :
    Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range →+
      Additive (Module.End ℂ (b5_sections Λ F hF Q (k * n ^ 2))) :=
  QuotientAddGroup.lift _ (b52_descentLatticeHom Λ F hF Q hherm himag hcocycle k n hn)
    (by
      rintro _ ⟨l, rfl⟩
      change b52_descentEnd Λ F hF Q hherm himag k n hn (n • l) = 1
      ext t z
      exact congrFun (b52_descentTranslate_nsmul Λ F hF Q k n hn l t) z)

theorem b52_finite_lattice_quotient (n : ℕ) (hn : n ≠ 0) :
    Finite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) := by
  letI : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.mp inferInstance
  letI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg Λ hn
  infer_instance

end HodgeLean.Foundations.Program
