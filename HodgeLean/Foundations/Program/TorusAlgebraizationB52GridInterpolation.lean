import HodgeLean.Foundations.Program.TorusAlgebraizationB52Addition
import HodgeLean.Foundations.Program.TorusAlgebraizationB52CharacterInterpolation
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Separation

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_sections_basepoint_free_ge_two
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (k : ℕ) (hk : 2 ≤ k) (z : b5_V Λ F) :
    ∃ t : b5_sections Λ F hF Q k, t.val z ≠ 0 := by
  have htwo : ∃ t : b5_sections Λ F hF Q 2, t.val z ≠ 0 := by
    obtain ⟨a, b, hab, ha, hb⟩ := b52_fixed_balanced_nonzero s.property.1 hs z 0
    have hb' : b = -a := by simpa using eq_neg_of_add_eq_zero_right (by simpa using hab)
    subst b
    exact ⟨b52_balancedPairSection Λ F hF Q 1 s s a,
      mul_ne_zero ha (by simpa only [sub_eq_add_neg] using hb)⟩
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h2 : k = 2
    · subst k; exact htwo
    by_cases h3 : k = 3
    · subst k; exact b52_basepoint_of_nonzero_section Λ F hF Q s hs z
    obtain ⟨u, hu⟩ := ih (k - 2) (by omega) (by omega)
    obtain ⟨v, hv⟩ := htwo
    refine ⟨⟨u.val * v.val, u.property.1.mul v.property.1, ?_⟩, mul_ne_zero hu hv⟩
    intro l w
    change u.val (w + _) * v.val (w + _) = _
    rw [u.property.2, v.property.2]
    change _ = _ * (u.val w * v.val w)
    rw [mul_mul_mul_comm, ← pow_add, Nat.sub_add_cancel hk]

theorem b52_character_sections_basepoint_free_ge_two
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (k : ℕ) (hk : 2 ≤ k) (χ : AddChar Λ ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    (z : b5_V Λ F) :
    ∃ t : b52_characterSections Λ F hF Q k χ, t.val z ≠ 0 := by
  obtain ⟨d, hd⟩ := b52_translationCharacter_surjective_unitary
    Λ F hF Q hherm hpos k (by omega) χ hχ
  obtain ⟨u, hu⟩ := b52_sections_basepoint_free_ge_two Λ F hF Q s hs k hk (z + d)
  have hm := b52_thetaTranslate_character_sections Λ F hF Q k d 0
    ⟨u.val, by rw [b52_characterSections_zero]; exact u.property⟩
  rw [zero_add, hd] at hm
  exact ⟨⟨_, hm⟩, mul_ne_zero (Complex.exp_ne_zero _) hu⟩

theorem b52_torsion_grid_delta
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (n r : ℕ) (hn : n ≠ 0) (hr : 2 ≤ r) :
    ∃ t : b5_sections Λ F hF Q (n ^ 2 + r), t.val 0 ≠ 0 ∧
      ∀ l : Λ, (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := Λ) n).range) l ≠ 0 →
        t.val ((n : ℂ)⁻¹ • b5_lattice Λ F l) = 0 := by
  obtain ⟨a, t, ht⟩ := b52_exists_torsion_interpolator
    Λ F hF Q hherm hpos 1 (by omega) s hs n hn
  let d : b5_V Λ F := (n : ℂ)⁻¹ • a
  let χ := b52_translationCharacter Λ F hF Q (n ^ 2) d
  let t' : b5_sections Λ F hF Q (n ^ 2) :=
    ⟨t.val, by simpa only [one_mul] using t.property⟩
  have hm := b52_thetaTranslate_character_sections Λ F hF Q (n ^ 2) d 0
    ⟨t'.val, by rw [b52_characterSections_zero]; exact t'.property⟩
  rw [zero_add] at hm
  let u : b52_characterSections Λ F hF Q (n ^ 2) χ := ⟨_, hm⟩
  have hu0 : u.val 0 = 1 := by
    change Complex.exp _ * t.val (0 + d) = 1
    simp only [b5_H, map_zero, LinearMap.zero_apply, mul_zero, neg_zero, Complex.exp_zero, one_mul, zero_add]
    have h := ht 0
    simpa only [map_zero, add_zero, ite_true, b52_factor_zero, pow_one] using h
  have huz (l : Λ) (hl : (QuotientAddGroup.mk'
      (nsmulAddMonoidHom (α := Λ) n).range) l ≠ 0) :
      u.val ((n : ℂ)⁻¹ • b5_lattice Λ F l) = 0 := by
    change Complex.exp _ * t.val ((n : ℂ)⁻¹ • b5_lattice Λ F l + d) = 0
    have he : (n : ℂ)⁻¹ • b5_lattice Λ F l + d =
        (n : ℂ)⁻¹ • (a + b5_lattice Λ F l) := by
      dsimp [d]
      rw [smul_add, add_comm]
    rw [he, ht l, if_neg hl, mul_zero]
  have hχ : ∀ l, ‖(-χ) l‖ = 1 := by
    intro l
    simp only [AddChar.neg_apply', norm_inv, χ,
      b52_translationCharacter_exp_im Λ F hF Q hherm, Complex.norm_exp_ofReal_mul_I, inv_one]
  obtain ⟨v, hv⟩ := b52_character_sections_basepoint_free_ge_two
    Λ F hF Q hherm hpos s hs r hr (-χ) hχ 0
  refine ⟨b52_oppositeCharacterProduct Λ F hF Q (n ^ 2) r χ u v, ?_, ?_⟩
  · change u.val 0 * v.val 0 ≠ 0
    rwa [hu0, one_mul]
  · intro l hl
    change u.val _ * v.val _ = 0
    rw [huz l hl, zero_mul]

end HodgeLean.Foundations.Program
