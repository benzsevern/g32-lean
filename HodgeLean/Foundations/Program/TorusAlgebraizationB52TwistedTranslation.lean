import HodgeLean.Foundations.Program.TorusAlgebraizationB52TwistedSections
import HodgeLean.Foundations.Program.TorusAlgebraizationB52ThetaAction

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b52_translationCharacter (k : ℕ) (d : b5_V Λ F) : AddChar Λ ℂ where
  toFun l := Complex.exp ((k : ℂ) * Real.pi *
    (b5_H Λ F hF Q (b5_lattice Λ F l) d - b5_H Λ F hF Q d (b5_lattice Λ F l)))
  map_zero_eq_one' := by simp [b5_H]
  map_add_eq_mul' l m := by
    simp only [map_add, b5_H_add_right, (b52_H_real_bilinear Λ F hF Q).add_left]
    rw [← Complex.exp_add]
    congr 1
    ring

theorem b52_thetaTranslate_character_sections (k : ℕ) (d : b5_V Λ F)
    (χ : AddChar Λ ℂ) (s : b52_characterSections Λ F hF Q k χ) :
    b52_thetaTranslate Λ F hF Q k d s.val ∈
      b52_characterSections Λ F hF Q k (χ + b52_translationCharacter Λ F hF Q k d) := by
  have hg : Differentiable ℂ (fun z ↦
      Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d z))) := by
    simpa only [b52_seedForPoint_apply, mul_assoc, Pi.neg_apply] using
      (((b52_seedForPoint Λ F hF Q d).differentiable.const_mul (k : ℂ)).neg.cexp)
  refine ⟨hg.mul (s.property.1.comp (differentiable_id.add_const d)), ?_⟩
  intro l z
  change Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d (z + b5_lattice Λ F l))) *
    s.val (z + b5_lattice Λ F l + d) = _
  rw [add_right_comm z (b5_lattice Λ F l) d, s.property.2, b5_factor_add_right,
    mul_pow, b5_H_add_right, mul_add, neg_add, Complex.exp_add]
  have he : Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d (b5_lattice Λ F l))) *
      Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) d) ^ k =
      b52_translationCharacter Λ F hF Q k d l := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    change Complex.exp _ = Complex.exp _
    congr 1
    ring
  change _ = (χ l * b52_translationCharacter Λ F hF Q k d l) *
    b5_factor Λ F hF Q l z ^ k *
      (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d z)) * s.val (z + d))
  rw [← he]
  ring

theorem b52_translationCharacter_add_degree (i j : ℕ) (d : b5_V Λ F) :
    b52_translationCharacter Λ F hF Q (i + j) d =
      b52_translationCharacter Λ F hF Q i d + b52_translationCharacter Λ F hF Q j d := by
  ext l
  change Complex.exp _ = Complex.exp _ * Complex.exp _
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem b52_translationCharacter_exp_im
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (k : ℕ) (d : b5_V Λ F) (l : Λ) :
    b52_translationCharacter Λ F hF Q k d l =
      Complex.exp (((2 * Real.pi * (k : ℝ) *
        (b5_H Λ F hF Q (b5_lattice Λ F l) d).im : ℝ) : ℂ) * Complex.I) := by
  change Complex.exp _ = Complex.exp _
  congr 1
  rw [← hherm d (b5_lattice Λ F l)]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem b52_translationCharacter_neg (k : ℕ) (d : b5_V Λ F) :
    b52_translationCharacter Λ F hF Q k (-d) =
      -b52_translationCharacter Λ F hF Q k d := by
  ext l
  simp only [AddChar.neg_apply']
  change Complex.exp _ = (Complex.exp _)⁻¹
  rw [← Complex.exp_neg]
  congr 1
  have hleft : ∀ x, b5_H Λ F hF Q (-d) x = -b5_H Λ F hF Q d x := by
    intro x
    simpa only [neg_one_smul, star_neg, star_one, neg_mul, one_mul] using
      b52_H_smul_left Λ F hF Q (-1 : ℂ) d x
  have hright : ∀ x, b5_H Λ F hF Q x (-d) = -b5_H Λ F hF Q x d := by
    intro x
    simpa only [neg_one_smul, neg_mul, one_mul] using
      b52_H_smul_right Λ F hF Q (-1 : ℂ) x d
  rw [hleft, hright]
  ring

theorem b52_translationCharacter_mul_degree (k n : ℕ) (d : b5_V Λ F) :
    b52_translationCharacter Λ F hF Q (k * n) d =
      n • b52_translationCharacter Λ F hF Q k d := by
  induction n with
  | zero =>
    ext l
    simp [b52_translationCharacter]
  | succ n ih =>
    rw [Nat.mul_succ, b52_translationCharacter_add_degree, ih, add_nsmul, one_nsmul]

theorem b52_thetaTranslate_inverse_formula (k : ℕ) (d : b5_V Λ F) (f : b5_V Λ F → ℂ) :
    b52_thetaTranslate Λ F hF Q k d
      (Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d d)) •
        b52_thetaTranslate Λ F hF Q k (-d) f) = f := by
  have hneg : b5_H Λ F hF Q (-d) d = -b5_H Λ F hF Q d d := by
    simpa only [neg_one_smul, star_neg, star_one, neg_mul, one_mul] using
      b52_H_smul_left Λ F hF Q (-1 : ℂ) d d
  have hz : b52_thetaTranslate Λ F hF Q k 0 f = f := by
    ext z
    simp [b52_thetaTranslate, b5_H]
  have he := congrArg (fun L : (b5_V Λ F → ℂ) →ₗ[ℂ] (b5_V Λ F → ℂ) ↦ L f)
    (b52_thetaTranslate_comp Λ F hF Q k d (-d))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, add_neg_cancel, hz, hneg] at he
  rw [map_smul, he, smul_smul, ← Complex.exp_add]
  have heq : -((k : ℂ) * Real.pi * b5_H Λ F hF Q d d) +
      -((k : ℂ) * Real.pi * -b5_H Λ F hF Q d d) = 0 := by ring
  rw [heq, Complex.exp_zero, one_smul]

theorem b52_untwist_character_section (k : ℕ) (d : b5_V Λ F)
    (s : b52_characterSections Λ F hF Q k (b52_translationCharacter Λ F hF Q k d)) :
    ∃ t : b5_sections Λ F hF Q k, b52_thetaTranslate Λ F hF Q k d t.val = s.val := by
  have hu := b52_thetaTranslate_character_sections Λ F hF Q k (-d)
    (b52_translationCharacter Λ F hF Q k d) s
  rw [b52_translationCharacter_neg, add_neg_cancel, b52_characterSections_zero] at hu
  refine ⟨⟨Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d d)) •
    b52_thetaTranslate Λ F hF Q k (-d) s.val,
    (b5_sections Λ F hF Q k).smul_mem _ hu⟩, ?_⟩
  exact b52_thetaTranslate_inverse_formula Λ F hF Q k d s.val

def b52_twistedTranslation (k : ℕ) (d : b5_V Λ F) (χ : AddChar Λ ℂ) :
    b52_characterSections Λ F hF Q k χ →ₗ[ℂ]
      b52_characterSections Λ F hF Q k (χ + b52_translationCharacter Λ F hF Q k d) :=
  LinearMap.codRestrict _
    ((b52_thetaTranslate Λ F hF Q k d).comp (b52_characterSections Λ F hF Q k χ).subtype)
    (fun s ↦ b52_thetaTranslate_character_sections Λ F hF Q k d χ s)

theorem b52_twistedTranslation_surjective (k : ℕ) (d : b5_V Λ F) (χ : AddChar Λ ℂ) :
    Function.Surjective (b52_twistedTranslation Λ F hF Q k d χ) := by
  intro s
  have hu := b52_thetaTranslate_character_sections Λ F hF Q k (-d)
    (χ + b52_translationCharacter Λ F hF Q k d) s
  rw [b52_translationCharacter_neg, add_neg_cancel_right] at hu
  refine ⟨⟨Complex.exp (-((k : ℂ) * Real.pi * b5_H Λ F hF Q d d)) •
    b52_thetaTranslate Λ F hF Q k (-d) s.val,
    (b52_characterSections Λ F hF Q k χ).smul_mem _ hu⟩, ?_⟩
  apply Subtype.ext
  exact b52_thetaTranslate_inverse_formula Λ F hF Q k d s.val

theorem b52_twistedTranslation_bijective (k : ℕ) (d : b5_V Λ F) (χ : AddChar Λ ℂ) :
    Function.Bijective (b52_twistedTranslation Λ F hF Q k d χ) := by
  refine ⟨?_, b52_twistedTranslation_surjective Λ F hF Q k d χ⟩
  intro s t h
  apply Subtype.ext
  exact b52_thetaTranslate_injective Λ F hF Q k d (congrArg Subtype.val h)

end HodgeLean.Foundations.Program
