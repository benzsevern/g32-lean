import HodgeLean.Foundations.Program.TorusAlgebraizationB52Jets

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

include hF in
theorem b52_lattice_separating_functional (v : b5_V Λ F)
    (hv : ¬ ∃ l : Λ, v = b5_lattice Λ F l) :
    ∃ A : b5_V Λ F →ₗ[ℝ] ℝ,
      (∀ l : Λ, ∃ n : ℤ, A (b5_lattice Λ F l) = n) ∧ ¬ ∃ n : ℤ, A v = n := by
  classical
  let e := Module.finBasis ℤ Λ
  obtain ⟨c, hc⟩ := b2_latticeMap_basis_aux e F hF
  let b := c.map ((b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).restrictScalars ℝ)
  have hb : ∀ i, b i = b5_lattice Λ F (e i) := by
    intro i
    change b2_coord _ (c i) = _
    rw [hc i]
    rfl
  have hex : ∃ i, ¬ ∃ n : ℤ, b.repr v i = n := by
    by_contra hn
    push_neg at hn
    choose n hn using hn
    apply hv
    refine ⟨∑ i, n i • e i, ?_⟩
    calc
      v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
      _ = b5_lattice Λ F (∑ i, n i • e i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hn i, hb i, map_zsmul, Int.cast_smul_eq_zsmul]
  obtain ⟨i, hi⟩ := hex
  refine ⟨b.coord i, ?_, hi⟩
  intro l
  refine ⟨e.repr l i, ?_⟩
  conv_lhs => rw [← e.sum_repr l]
  simp only [map_sum, map_zsmul, ← hb, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  simp

def b52_imaginaryDual : b5_V Λ F →ₗ[ℝ] Module.Dual ℝ (b5_V Λ F) :=
  LinearMap.mk₂ ℝ (fun d x ↦ (b5_H Λ F hF Q x d).im)
    (by intros; rw [(b52_H_real_bilinear Λ F hF Q).add_right]; simp)
    (by intros; rw [(b52_H_real_bilinear Λ F hF Q).smul_right]; simp)
    (by intros; rw [(b52_H_real_bilinear Λ F hF Q).add_left]; simp)
    (by intros; rw [(b52_H_real_bilinear Λ F hF Q).smul_left]; simp)

theorem b52_imaginaryDual_surjective
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re) :
    Function.Surjective (b52_imaginaryDual Λ F hF Q) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq.symm)).mp
  apply (injective_iff_map_eq_zero _).mpr
  intro d hd
  by_contra hn
  have he := congrArg (fun A : Module.Dual ℝ (b5_V Λ F) ↦ A (Complex.I • d)) hd
  change (b5_H Λ F hF Q (Complex.I • d) d).im = 0 at he
  simp [b52_H_smul_left, Complex.mul_im] at he
  have hp := hpos d hn
  linarith

theorem b52_dual_lattice_separates
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (v : b5_V Λ F) (hv : ¬ ∃ l : Λ, v = b5_lattice Λ F l) :
    ∃ d : b5_V Λ F,
      (∀ l : Λ, ∃ n : ℤ, (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n) ∧
      ¬ ∃ n : ℤ, (b5_H Λ F hF Q v d).im = n := by
  obtain ⟨A, hA, hvA⟩ := b52_lattice_separating_functional Λ F hF v hv
  obtain ⟨d, hd⟩ := b52_imaginaryDual_surjective Λ F hF Q hpos A
  refine ⟨d, ?_, ?_⟩
  · change ∀ l : Λ, ∃ n : ℤ, b52_imaginaryDual Λ F hF Q d (b5_lattice Λ F l) = n
    rwa [hd]
  · change ¬ ∃ n : ℤ, b52_imaginaryDual Λ F hF Q d v = n
    rwa [hd]

theorem b52_exp_hermitian_commutator_eq_one_iff
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (x y : b5_V Λ F) :
    Complex.exp ((Real.pi : ℂ) * (b5_H Λ F hF Q x y - b5_H Λ F hF Q y x)) = 1 ↔
      ∃ n : ℤ, (b5_H Λ F hF Q x y).im = n := by
  have he : (Real.pi : ℂ) * (b5_H Λ F hF Q x y - b5_H Λ F hF Q y x) =
      ((2 * Real.pi * (b5_H Λ F hF Q x y).im : ℝ) : ℂ) * Complex.I := by
    rw [← hherm y x]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [he, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hi := congrArg Complex.im hn
    simp [Complex.mul_im] at hi
    nlinarith [Real.pi_pos]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring

theorem b52_linear_eq_H_of_real_lattice
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (h : b5_V Λ F) (L : b5_V Λ F →L[ℂ] ℂ)
    (hre : ∀ l, (L (b5_lattice Λ F l)).re =
      ((Real.pi : ℂ) * b5_H Λ F hF Q (b5_lattice Λ F l) h).re) :
    ∀ x, L x = (Real.pi : ℂ) * b5_H Λ F hF Q h x := by
  have heq := b52_real_linear_ext_lattice Λ F hF
    (Complex.reCLM.toLinearMap.comp (L.toLinearMap.restrictScalars ℝ))
    (Real.pi • (Complex.reCLM.toLinearMap.comp
      ((b52_H_continuousBilinear Λ F hF Q).flip h).toLinearMap))
    (fun l ↦ by simpa [Complex.mul_re] using hre l)
  have heval : ∀ x, (L x).re = Real.pi * (b5_H Λ F hF Q x h).re :=
    fun x ↦ LinearMap.congr_fun heq x
  intro x
  have hi := heval (Complex.I • x)
  simp [map_smul, b52_H_smul_left, Complex.mul_re] at hi
  rw [← hherm h x]
  apply Complex.ext
  · simpa [Complex.mul_re] using heval x
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im, zero_mul, add_zero]
    linarith

end HodgeLean.Foundations.Program
