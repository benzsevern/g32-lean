import HodgeLean.Foundations.Program.TorusAlgebraizationB52ThetaCharacters

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_characterSections (k : ℕ) (χ : AddChar Λ ℂ) :
    Submodule ℂ (b5_V Λ F → ℂ) where
  carrier := {f | Differentiable ℂ f ∧ ∀ l z,
    f (z + b5_lattice Λ F l) = χ l * b5_factor Λ F hF Q l z ^ k * f z}
  zero_mem' := ⟨differentiable_const 0, by intros; simp⟩
  add_mem' := fun hf hg ↦ ⟨hf.1.add hg.1, by
    intro l z
    simp only [Pi.add_apply, hf.2 l z, hg.2 l z, mul_add]⟩
  smul_mem' := fun c f hf ↦ ⟨hf.1.const_smul c, by
    intro l z
    simp only [Pi.smul_apply, smul_eq_mul, hf.2 l z]
    ring⟩

theorem b52_characterSections_zero (k : ℕ) :
    b52_characterSections Λ F hF Q k 0 = b5_sections Λ F hF Q k := by
  ext f
  simp [b52_characterSections, b5_sections]

def b52_oppositeCharacterProduct (i j : ℕ) (χ : AddChar Λ ℂ)
    (s : b52_characterSections Λ F hF Q i χ)
    (t : b52_characterSections Λ F hF Q j (-χ)) :
    b5_sections Λ F hF Q (i + j) := by
  refine ⟨s.val * t.val, s.property.1.mul t.property.1, ?_⟩
  intro l z
  have hχ : χ l ≠ 0 := by
    intro hl
    have hh := χ.map_add_eq_mul l (-l)
    simp [hl] at hh
  simp only [Pi.mul_apply, s.property.2, t.property.2, AddChar.neg_apply', pow_add]
  calc
    _ = (χ l * (χ l)⁻¹) *
        ((b5_factor Λ F hF Q l z ^ i * b5_factor Λ F hF Q l z ^ j) *
          (s.val z * t.val z)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hχ, one_mul]

theorem b52_eigenSection_fractional_automorphy (k n : ℕ)
    (χ : AddChar Λ ℂ) (t : b5_sections Λ F hF Q (k * n ^ 2))
    (ht : ∀ l, b52_descentTranslate Λ F hF Q k n l t.val = χ l • t.val)
    (l : Λ) (z : b5_V Λ F) :
    t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) =
      χ l * b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * t.val z := by
  have hj : b5_factor Λ F hF Q l ((n : ℂ) • z) ≠ 0 :=
    mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _)
  have he := congrArg (fun f : b5_V Λ F → ℂ ↦ f z) (ht l)
  change (b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k)⁻¹ *
    t.val (z + (n : ℂ)⁻¹ • b5_lattice Λ F l) = χ l * t.val z at he
  have hh := congrArg (fun a : ℂ ↦ b5_factor Λ F hF Q l ((n : ℂ) • z) ^ k * a) he
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hj), one_mul] at hh
  exact hh.trans (by ring)



def b52_descendedEigenSection (k n : ℕ) (hn : n ≠ 0)
    (χ : AddChar Λ ℂ) (t : b5_sections Λ F hF Q (k * n ^ 2))
    (ht : ∀ l, b52_descentTranslate Λ F hF Q k n l t.val = χ l • t.val) :
    b52_characterSections Λ F hF Q k χ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  refine ⟨fun z ↦ t.val ((n : ℂ)⁻¹ • z),
    t.property.1.comp (differentiable_id.const_smul (n : ℂ)⁻¹), ?_⟩
  intro l z
  change t.val ((n : ℂ)⁻¹ • (z + b5_lattice Λ F l)) = _
  rw [smul_add, b52_eigenSection_fractional_automorphy Λ F hF Q k n χ t ht]
  simp only [smul_smul, mul_inv_cancel₀ hn', one_smul]

variable
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

def b52_projectedCharacterSection (k n : ℕ) (hn : n ≠ 0)
    (χ : AddChar (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) ℂ)
    (s : b5_sections Λ F hF Q (k * n ^ 2)) :
    b52_characterSections Λ F hF Q k
      ((-χ).compAddMonoidHom (QuotientAddGroup.mk' _)) := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  let ρ := b52_descentQuotientHom Λ F hF Q hherm himag hcocycle k n hn
  refine b52_descendedEigenSection Λ F hF Q k n hn _
    (b52_characterProjection ρ χ s) ?_
  intro l
  have he := (b52_characterProjection_range ρ χ _).mp ⟨s, rfl⟩
    (QuotientAddGroup.mk' _ l)
  have hv := congrArg Subtype.val he
  change b52_descentTranslate Λ F hF Q k n l (b52_characterProjection ρ χ s).val =
    (χ (QuotientAddGroup.mk' _ l))⁻¹ • (b52_characterProjection ρ χ s).val at hv
  simpa only [AddChar.compAddMonoidHom_apply, AddChar.neg_apply', Submodule.coe_smul] using hv

def b52_projectedCharacterProduct (i j n : ℕ) (hn : n ≠ 0)
    (χ : AddChar (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) ℂ)
    (s : b5_sections Λ F hF Q (i * n ^ 2))
    (t : b5_sections Λ F hF Q (j * n ^ 2)) :
    b5_sections Λ F hF Q (i + j) := by
  let u := b52_projectedCharacterSection Λ F hF Q hherm himag hcocycle i n hn χ s
  let v := b52_projectedCharacterSection Λ F hF Q hherm himag hcocycle j n hn (-χ) t
  refine b52_oppositeCharacterProduct Λ F hF Q i j
    ((-χ).compAddMonoidHom (QuotientAddGroup.mk' _)) u ⟨v.val, ?_⟩
  have he : -((-χ).compAddMonoidHom (QuotientAddGroup.mk' _)) =
      (-(-χ)).compAddMonoidHom (QuotientAddGroup.mk' _) := by
    ext l
    simp only [AddChar.compAddMonoidHom_apply, AddChar.neg_apply']
  rw [he]
  exact v.property

theorem b52_trace_eq_sum_projectedCharacterProducts (i j n : ℕ) (hn : n ≠ 0)
    (s : b5_sections Λ F hF Q (i * n ^ 2))
    (t : b5_sections Λ F hF Q (j * n ^ 2)) :
    letI := b52_finite_lattice_quotient Λ n hn
    letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
    b52_descentTrace Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductBilinear Λ F hF Q i j n s t) =
    ∑ χ : AddChar (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) ℂ,
      b52_projectedCharacterProduct Λ F hF Q hherm himag hcocycle i j n hn χ s t := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  apply Subtype.ext
  funext z
  simpa only [Submodule.coe_sum, Finset.sum_apply, b52_projectedCharacterProduct,
    b52_oppositeCharacterProduct, b52_projectedCharacterSection, b52_descendedEigenSection,
    Pi.mul_apply] using
    b52_trace_pullbackProduct_characters Λ F hF Q hherm himag hcocycle i j n hn s t z

theorem b52_trace_product_mem_of_twisted_products (i j n : ℕ) (hn : n ≠ 0)
    (W : Submodule ℂ (b5_sections Λ F hF Q (i + j)))
    (hW : ∀ (χ : AddChar Λ ℂ) (u : b52_characterSections Λ F hF Q i χ)
      (v : b52_characterSections Λ F hF Q j (-χ)),
      b52_oppositeCharacterProduct Λ F hF Q i j χ u v ∈ W)
    (s : b5_sections Λ F hF Q (i * n ^ 2))
    (t : b5_sections Λ F hF Q (j * n ^ 2)) :
    b52_descentTrace Λ F hF Q hherm himag hcocycle (i + j) n hn
      (b52_pullbackProductBilinear Λ F hF Q i j n s t) ∈ W := by
  letI := b52_finite_lattice_quotient Λ n hn
  letI := Fintype.ofFinite (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range)
  rw [b52_trace_eq_sum_projectedCharacterProducts Λ F hF Q hherm himag hcocycle]
  apply W.sum_mem
  intro χ _
  exact hW _ _ _

end HodgeLean.Foundations.Program
