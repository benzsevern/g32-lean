import HodgeLean.Foundations.Program.TorusAlgebraizationB52CharacterRealization
import HodgeLean.Foundations.Program.TorusAlgebraizationB52AnalyticSpanning

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct
open Classical

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_unitary_character_section_nonzero
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (k : ℕ) (hk : k ≠ 0) (s : b5_sections Λ F hF Q k) (hs : s.val ≠ 0)
    (χ : AddChar Λ ℂ) (hχ : ∀ l, ‖χ l‖ = 1) :
    ∃ t : b52_characterSections Λ F hF Q k χ, t.val ≠ 0 := by
  obtain ⟨d, hd⟩ := b52_translationCharacter_surjective_unitary
    Λ F hF Q hherm hpos k hk χ hχ
  have hm := b52_thetaTranslate_character_sections Λ F hF Q k d 0
    ⟨s.val, by rw [b52_characterSections_zero]; exact s.property⟩
  rw [zero_add, hd] at hm
  refine ⟨⟨b52_thetaTranslate Λ F hF Q k d s.val, hm⟩, ?_⟩
  intro ht
  apply hs
  apply b52_thetaTranslate_injective Λ F hF Q k d
  simpa only [map_zero] using ht

def b52_dilatedCharacterSection (k n : ℕ) (χ : AddChar Λ ℂ)
    (hχ : ∀ l, χ (n • l) = 1) (s : b52_characterSections Λ F hF Q k χ) :
    b5_sections Λ F hF Q (k * n ^ 2) := by
  refine ⟨fun z ↦ s.val ((n : ℂ) • z),
    s.property.1.comp (differentiable_id.const_smul (n : ℂ)), ?_⟩
  intro l z
  change s.val ((n : ℂ) • (z + b5_lattice Λ F l)) = _
  rw [smul_add, show (n : ℂ) • b5_lattice Λ F l = b5_lattice Λ F (n • l) by
    simp only [map_nsmul, Nat.cast_smul_eq_nsmul],
    s.property.2, hχ, one_mul, b52_factor_dilation]
  simp only [← pow_mul, Nat.mul_comm]

theorem b52_exists_torsion_interpolator
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (k : ℕ) (hk : k ≠ 0) (s : b5_sections Λ F hF Q k) (hs : s.val ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ a : b5_V Λ F, ∃ t : b5_sections Λ F hF Q (k * n ^ 2), ∀ l : Λ,
      t.val ((n : ℂ)⁻¹ • (a + b5_lattice Λ F l)) =
        if (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := Λ) n).range) l = 0
          then b5_factor Λ F hF Q l a ^ k else 0 := by
  classical
  let G := Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range
  let q : Λ →+ G := QuotientAddGroup.mk' _
  letI := b52_finite_lattice_quotient Λ n hn
  letI : Fintype G := Fintype.ofFinite G
  let ψ (χ : AddChar G ℂ) : AddChar Λ ℂ := χ.compAddMonoidHom q
  have hex (χ : AddChar G ℂ) :
      ∃ t : b52_characterSections Λ F hF Q k (ψ χ), t.val ≠ 0 :=
    b52_unitary_character_section_nonzero Λ F hF Q hherm hpos k hk s hs
      (ψ χ) (fun l ↦ χ.norm_apply (q l))
  choose f hf using hex
  obtain ⟨a, ha⟩ := (b52_dense_simultaneous_nonzero
    (fun χ ↦ (f χ).val) (fun χ ↦ (f χ).property.1) hf).nonempty
  have htors (χ : AddChar G ℂ) (l : Λ) : ψ χ (n • l) = 1 := by
    have he := congrArg (fun η : AddChar Λ ℂ ↦ η l)
      (b52_quotient_character_torsion Λ n χ)
    simpa only [AddChar.map_nsmul_eq_pow, AddChar.nsmul_apply,
      AddChar.zero_apply] using he
  let u (χ : AddChar G ℂ) :=
    b52_dilatedCharacterSection Λ F hF Q k n (ψ χ) (htors χ) (f χ)
  let t : b5_sections Λ F hF Q (k * n ^ 2) :=
    (Fintype.card G : ℂ)⁻¹ • ∑ χ : AddChar G ℂ, ((f χ).val a)⁻¹ • u χ
  refine ⟨a, t, ?_⟩
  intro l
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he (χ : AddChar G ℂ) :
      ((f χ).val a)⁻¹ * (u χ).val ((n : ℂ)⁻¹ • (a + b5_lattice Λ F l)) =
        χ (q l) * b5_factor Λ F hF Q l a ^ k := by
    change ((f χ).val a)⁻¹ * (f χ).val
      ((n : ℂ) • ((n : ℂ)⁻¹ • (a + b5_lattice Λ F l))) = _
    rw [smul_smul, mul_inv_cancel₀ hn', one_smul, (f χ).property.2]
    change ((f χ).val a)⁻¹ * (χ (q l) * b5_factor Λ F hF Q l a ^ k * (f χ).val a) = _
    field_simp [ha χ]
  change ((Fintype.card G : ℂ)⁻¹ •
    ∑ χ : AddChar G ℂ, ((f χ).val a)⁻¹ • u χ).val _ = _
  simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  simp_rw [he]
  rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  by_cases hl : q l = 0
  · rw [if_pos hl]
    change _ = if q l = 0 then _ else _
    rw [if_pos hl, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · rw [if_neg hl, zero_mul, mul_zero]
    change 0 = if q l = 0 then _ else _
    rw [if_neg hl]

end HodgeLean.Foundations.Program
