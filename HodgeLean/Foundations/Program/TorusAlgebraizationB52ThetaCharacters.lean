import HodgeLean.Foundations.Program.TorusAlgebraizationB52PairedCharacters

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_pullbackProductBilinear (i j n : ℕ) :
    b5_sections Λ F hF Q (i * n ^ 2) →ₗ[ℂ]
      b5_sections Λ F hF Q (j * n ^ 2) →ₗ[ℂ]
        b5_sections Λ F hF Q ((i + j) * n ^ 2) where
  toFun := b52_pullbackProductLeft Λ F hF Q i j n
  map_add' s t := by ext u z; simp [b52_pullbackProductLeft, add_mul]
  map_smul' c s := by ext u z; simp [b52_pullbackProductLeft, mul_assoc]

variable
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

theorem b52_pullbackProduct_quotient_equivariant (i j n : ℕ) (hn : n ≠ 0)
    (q : Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
    (s : b5_sections Λ F hF Q (i * n ^ 2))
    (t : b5_sections Λ F hF Q (j * n ^ 2)) :
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle (i + j) n hn q).toMul
      (b52_pullbackProductBilinear Λ F hF Q i j n s t) =
    b52_pullbackProductBilinear Λ F hF Q i j n
      ((b52_descentQuotientHom Λ F hF Q hherm himag hcocycle i n hn q).toMul s)
      ((b52_descentQuotientHom Λ F hF Q hherm himag hcocycle j n hn q).toMul t) := by
  refine QuotientAddGroup.induction_on q ?_
  intro l
  apply Subtype.ext
  exact b52_descentTranslate_mul Λ F hF Q i j n l s.val t.val

theorem b52_average_pullbackProduct_characters (i j n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q (i * n ^ 2))
    (t : b5_sections Λ F hF Q (j * n ^ 2)) :
    letI := b52_finite_lattice_quotient Λ n hn
    letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
    let ρ := b52_descentQuotientHom Λ F hF Q hherm himag hcocycle i n hn
    let σ := b52_descentQuotientHom Λ F hF Q hherm himag hcocycle j n hn
    b52_descentAverage Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductBilinear Λ F hF Q i j n s t) =
    ∑ χ : AddChar (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) ℂ,
      b52_pullbackProductBilinear Λ F hF Q i j n
        (b52_characterProjection ρ χ s) (b52_characterProjection σ (-χ) t) := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  exact b52_average_bilinear_character_formula
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle i n hn)
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle j n hn)
    (b52_descentQuotientHom Λ F hF Q hherm himag hcocycle (i + j) n hn)
    (b52_pullbackProductBilinear Λ F hF Q i j n)
    (b52_pullbackProduct_quotient_equivariant Λ F hF Q hherm himag hcocycle i j n hn)
    s t

theorem b52_trace_pullbackProduct_characters (i j n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q (i * n ^ 2))
    (t : b5_sections Λ F hF Q (j * n ^ 2)) (z : b5_V Λ F) :
    letI := b52_finite_lattice_quotient Λ n hn
    letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
    let ρ := b52_descentQuotientHom Λ F hF Q hherm himag hcocycle i n hn
    let σ := b52_descentQuotientHom Λ F hF Q hherm himag hcocycle j n hn
    (b52_descentTrace Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductBilinear Λ F hF Q i j n s t)).val z =
    ∑ χ : AddChar (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) ℂ,
      (b52_characterProjection ρ χ s).val ((n : ℂ)⁻¹ • z) *
        (b52_characterProjection σ (-χ) t).val ((n : ℂ)⁻¹ • z) := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  have he := congrArg (fun u : b5_sections Λ F hF Q ((i + j) * n ^ 2) ↦
    u.val ((n : ℂ)⁻¹ • z))
    (b52_average_pullbackProduct_characters Λ F hF Q hherm himag hcocycle i j n hn s t)
  simpa only [Submodule.coe_sum, Finset.sum_apply, b52_pullbackProductBilinear,
    b52_pullbackProductLeft, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply,
    b52_descentTrace, b52_descendedSection] using he

end HodgeLean.Foundations.Program
