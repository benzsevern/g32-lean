import HodgeLean.Foundations.Program.TorusAlgebraizationB52Averaging
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Generation

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b52_averageEnd_naturality
    {G : Type*} [AddGroup G] [Fintype G]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : G →+ Additive (Module.End ℂ V)) (σ : G →+ Additive (Module.End ℂ W))
    (L : V →ₗ[ℂ] W) (hL : ∀ g v, L ((ρ g).toMul v) = (σ g).toMul (L v)) :
    L.comp (b52_averageEnd ρ) = (b52_averageEnd σ).comp L := by
  ext v
  simp only [LinearMap.comp_apply, b52_averageEnd, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, hL]

open scoped TensorProduct
variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_pullbackProductLeft (i j n : ℕ)
    (s : b5_sections Λ F hF Q (i * n ^ 2)) :
    b5_sections Λ F hF Q (j * n ^ 2) →ₗ[ℂ]
      b5_sections Λ F hF Q ((i + j) * n ^ 2) where
  toFun t := ⟨s.val * t.val, s.property.1.mul t.property.1, by
    intro l z
    simp only [Pi.mul_apply, s.property.2, t.property.2, Nat.add_mul, pow_add]
    ring⟩
  map_add' t u := by ext z; simp [mul_add]
  map_smul' c t := by ext z; simp [mul_left_comm]

theorem b52_descentTranslate_mul (i j n : ℕ) (l : Λ) (f g : b5_V Λ F → ℂ) :
    b52_descentTranslate Λ F hF Q (i + j) n l (f * g) =
      b52_descentTranslate Λ F hF Q i n l f *
        b52_descentTranslate Λ F hF Q j n l g := by
  funext z
  change (b5_factor Λ F hF Q l ((n : ℂ) • z) ^ (i + j))⁻¹ *
    (f (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) * g (z + (n : ℂ)⁻¹ • b5_lattice Λ F l)) =
    ((b5_factor Λ F hF Q l ((n : ℂ) • z) ^ i)⁻¹ *
      f (z + (n : ℂ)⁻¹ • b5_lattice Λ F l)) *
    ((b5_factor Λ F hF Q l ((n : ℂ) • z) ^ j)⁻¹ *
      g (z + (n : ℂ)⁻¹ • b5_lattice Λ F l))
  rw [pow_add, mul_inv_rev]
  ring

variable
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

theorem b52_average_pullbackProductLeft (i j n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q i) :
    (b52_pullbackProductLeft Λ F hF Q i j n (b52_dilatedSection Λ F hF Q i n s)).comp
      (b52_descentAverage Λ F hF Q hherm himag hcocycle j n hn) =
    (b52_descentAverage Λ F hF Q hherm himag hcocycle (i + j) n hn).comp
      (b52_pullbackProductLeft Λ F hF Q i j n (b52_dilatedSection Λ F hF Q i n s)) := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  apply b52_averageEnd_naturality
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle j n hn)
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle (i + j) n hn)
  intro q t
  refine QuotientAddGroup.induction_on q ?_
  intro l
  apply Subtype.ext
  change (b52_dilatedSection Λ F hF Q i n s).val *
      b52_descentTranslate Λ F hF Q j n l t.val =
    b52_descentTranslate Λ F hF Q (i + j) n l
      ((b52_dilatedSection Λ F hF Q i n s).val * t.val)
  rw [b52_descentTranslate_mul,
    (b52_mem_dilation_iff_descent_fixed Λ F hF Q i n hn _).mp ⟨s, rfl⟩ l]

theorem b52_trace_pullbackProductLeft (i j n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q i) (t : b5_sections Λ F hF Q (j * n ^ 2))
    (z : b5_V Λ F) :
    (b52_descentTrace Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductLeft Λ F hF Q i j n
        (b52_dilatedSection Λ F hF Q i n s) t)).val z =
    s.val z * (b52_descentTrace Λ F hF Q hherm himag hcocycle j n hn t).val z := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have he := congrArg (fun L : b5_sections Λ F hF Q (j * n ^ 2) →ₗ[ℂ]
      b5_sections Λ F hF Q ((i + j) * n ^ 2) ↦ (L t).val ((n : ℂ)⁻¹ • z))
    (b52_average_pullbackProductLeft Λ F hF Q hherm himag hcocycle i j n hn s)
  change s.val ((n : ℂ) • ((n : ℂ)⁻¹ • z)) *
      (b52_descentAverage Λ F hF Q hherm himag hcocycle j n hn t).val ((n : ℂ)⁻¹ • z) =
    (b52_descentAverage Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductLeft Λ F hF Q i j n
        (b52_dilatedSection Λ F hF Q i n s) t)).val ((n : ℂ)⁻¹ • z) at he
  change (b52_descentAverage Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductLeft Λ F hF Q i j n
        (b52_dilatedSection Λ F hF Q i n s) t)).val ((n : ℂ)⁻¹ • z) =
    s.val z * (b52_descentAverage Λ F hF Q hherm himag hcocycle j n hn t).val ((n : ℂ)⁻¹ • z)
  simpa only [smul_smul, mul_inv_cancel₀ hn', one_smul] using he.symm

theorem b52_trace_pullbackProduct_in_multiplication_image (i j n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q (3 * i))
    (t : b5_sections Λ F hF Q ((3 * j) * n ^ 2)) :
    ∃ w : b5_sections Λ F hF Q (3 * i) ⊗[ℂ] b5_sections Λ F hF Q (3 * j),
      ∀ z, (b52_sectionMultiplication Λ F hF Q i j w).val z =
        (b52_descentTrace Λ F hF Q hherm himag hcocycle (3 * i + 3 * j) n hn
          (b52_pullbackProductLeft Λ F hF Q (3 * i) (3 * j) n
            (b52_dilatedSection Λ F hF Q (3 * i) n s) t)).val z := by
  refine ⟨s ⊗ₜ[ℂ] b52_descentTrace Λ F hF Q hherm himag hcocycle (3 * j) n hn t, ?_⟩
  intro z
  exact (b52_trace_pullbackProductLeft Λ F hF Q hherm himag hcocycle
    (3 * i) (3 * j) n hn s t z).symm

end HodgeLean.Foundations.Program
