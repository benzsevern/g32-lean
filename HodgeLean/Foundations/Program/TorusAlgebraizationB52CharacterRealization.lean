import HodgeLean.Foundations.Program.TorusAlgebraizationB52TwistedTranslation

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

theorem b52_addChar_ext_basis {Λ ι : Type*} [AddCommGroup Λ] [Fintype ι]
    (e : Module.Basis ι ℤ Λ) (χ ψ : AddChar Λ ℂ) (h : ∀ i, χ (e i) = ψ (e i)) :
    χ = ψ := by
  classical
  ext l
  rw [← e.sum_repr l]
  have he : ∀ S : Finset ι,
      χ (∑ i ∈ S, e.repr l i • e i) = ψ (∑ i ∈ S, e.repr l i • e i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi, AddChar.map_add_eq_mul,
        AddChar.map_zsmul_eq_zpow, h i, ih]
  exact he Finset.univ

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_translationCharacter_surjective_unitary
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (k : ℕ) (hk : k ≠ 0) (χ : AddChar Λ ℂ) (hχ : ∀ l, ‖χ l‖ = 1) :
    ∃ d : b5_V Λ F, b52_translationCharacter Λ F hF Q k d = χ := by
  classical
  let e := Module.finBasis ℤ Λ
  obtain ⟨c, hc⟩ := b2_latticeMap_basis_aux e F hF
  let b := c.map ((b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).restrictScalars ℝ)
  have hb : ∀ i, b i = b5_lattice Λ F (e i) := by
    intro i
    change b2_coord _ (c i) = _
    rw [hc i]
    rfl
  let a := fun i ↦ Complex.arg (χ (e i)) / (2 * Real.pi * (k : ℝ))
  let A : b5_V Λ F →ₗ[ℝ] ℝ := b.constr ℝ a
  obtain ⟨d, hd⟩ := b52_imaginaryDual_surjective Λ F hF Q hpos A
  have hd' : ∀ i, (b5_H Λ F hF Q (b5_lattice Λ F (e i)) d).im = a i := by
    intro i
    have he := congrArg (fun f : Module.Dual ℝ (b5_V Λ F) ↦ f (b i)) hd
    change (b5_H Λ F hF Q (b i) d).im = A (b i) at he
    rw [show A (b i) = a i from b.constr_basis ℝ a i, hb] at he
    exact he
  refine ⟨d, b52_addChar_ext_basis e _ χ ?_⟩
  intro i
  rw [b52_translationCharacter_exp_im Λ F hF Q hherm, hd']
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have ha : 2 * Real.pi * (k : ℝ) * a i = Complex.arg (χ (e i)) := by
    dsimp [a]
    field_simp
  rw [ha]
  simpa only [hχ, Complex.ofReal_one, one_mul] using
    Complex.norm_mul_exp_arg_mul_I (χ (e i))

theorem b52_paired_translation_characters
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (k m : ℕ) (hk : k ≠ 0) (χ : AddChar Λ ℂ)
    (hχ : ∀ l, ‖χ l‖ = 1) (htors : (m + 1) • χ = 0) :
    ∃ d : b5_V Λ F, b52_translationCharacter Λ F hF Q k d = χ ∧
      b52_translationCharacter Λ F hF Q (k * m) d = -χ ∧
      b52_translationCharacter Λ F hF Q (k * (m + 1)) d = 0 := by
  obtain ⟨d, hd⟩ := b52_translationCharacter_surjective_unitary Λ F hF Q hherm hpos k hk χ hχ
  refine ⟨d, hd, ?_, ?_⟩
  · rw [b52_translationCharacter_mul_degree, hd]
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_nsmul, one_nsmul] using htors
  · rw [b52_translationCharacter_mul_degree, hd]
    exact htors

theorem b52_twisted_product_as_translated_product
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (k m : ℕ) (hk : k ≠ 0) (χ : AddChar Λ ℂ)
    (hχ : ∀ l, ‖χ l‖ = 1) (htors : (m + 1) • χ = 0)
    (u : b52_characterSections Λ F hF Q k χ)
    (v : b52_characterSections Λ F hF Q (k * m) (-χ)) :
    ∃ d : b5_V Λ F, ∃ s : b5_sections Λ F hF Q k,
      ∃ t : b5_sections Λ F hF Q (k * m),
        b52_translationCharacter Λ F hF Q (k * (m + 1)) d = 0 ∧
        u.val * v.val = b52_thetaTranslate Λ F hF Q (k + k * m) d (s.val * t.val) := by
  obtain ⟨d, hd, hdm, hdt⟩ :=
    b52_paired_translation_characters Λ F hF Q hherm hpos k m hk χ hχ htors
  let u' : b52_characterSections Λ F hF Q k (b52_translationCharacter Λ F hF Q k d) :=
    ⟨u.val, by rw [hd]; exact u.property⟩
  let v' : b52_characterSections Λ F hF Q (k * m)
      (b52_translationCharacter Λ F hF Q (k * m) d) :=
    ⟨v.val, by rw [hdm]; exact v.property⟩
  obtain ⟨s, hs⟩ := b52_untwist_character_section Λ F hF Q k d u'
  obtain ⟨t, ht⟩ := b52_untwist_character_section Λ F hF Q (k * m) d v'
  refine ⟨d, s, t, hdt, ?_⟩
  rw [b52_thetaTranslate_mul, hs, ht]

theorem b52_quotient_character_torsion (n : ℕ)
    (χ : AddChar (Λ ⧸ (nsmulAddMonoidHom (α := Λ) n).range) ℂ) :
    n • χ.compAddMonoidHom (QuotientAddGroup.mk' _) = 0 := by
  ext l
  simp only [AddChar.nsmul_apply, AddChar.compAddMonoidHom_apply, AddChar.zero_apply]
  rw [← AddChar.map_nsmul_eq_pow, ← map_nsmul]
  have hz : (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := Λ) n).range) (n • l) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨l, rfl⟩
  rw [hz, AddChar.map_zero_eq_one]

theorem b52_characterSections_finite
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (k : ℕ) (hk : k ≠ 0) [Module.Finite ℂ (b5_sections Λ F hF Q k)]
    (χ : AddChar Λ ℂ) (hχ : ∀ l, ‖χ l‖ = 1) :
    Module.Finite ℂ (b52_characterSections Λ F hF Q k χ) := by
  obtain ⟨d, hd⟩ := b52_translationCharacter_surjective_unitary
    Λ F hF Q hherm hpos k hk χ hχ
  have hzero : Module.Finite ℂ (b52_characterSections Λ F hF Q k 0) := by
    rw [b52_characterSections_zero]
    infer_instance
  haveI := hzero
  have hfinite := Module.Finite.of_surjective
    (b52_twistedTranslation Λ F hF Q k d 0)
    (b52_twistedTranslation_surjective Λ F hF Q k d 0)
  rw [zero_add, hd] at hfinite
  exact hfinite

end HodgeLean.Foundations.Program
