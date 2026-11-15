import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Presentation
import Mathlib.Analysis.Complex.Basic

/-! Real polynomial equations underlying complex polynomial carriers.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.ComplexTopology

lemma polynomial_real_imaginary {σ : Type} (p : MvPolynomial σ ℂ) :
    ∃ a b : MvPolynomial (σ ⊕ σ) ℝ, ∀ z : σ → ℂ,
      MvPolynomial.eval (Sum.elim (fun i => (z i).re) (fun i => (z i).im)) a =
        (MvPolynomial.eval z p).re ∧
      MvPolynomial.eval (Sum.elim (fun i => (z i).re) (fun i => (z i).im)) b =
        (MvPolynomial.eval z p).im := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact ⟨MvPolynomial.C c.re, MvPolynomial.C c.im, fun z => by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, hab⟩ := hp
    obtain ⟨c, d, hcd⟩ := hq
    refine ⟨a + c, b + d, fun z => ?_⟩
    simp only [map_add, Complex.add_re, Complex.add_im, (hab z).1, (hab z).2,
      (hcd z).1, (hcd z).2, and_self]
  | mul_X p i hp =>
    obtain ⟨a, b, hab⟩ := hp
    refine ⟨a * MvPolynomial.X (Sum.inl i) - b * MvPolynomial.X (Sum.inr i),
      a * MvPolynomial.X (Sum.inr i) + b * MvPolynomial.X (Sum.inl i), fun z => ?_⟩
    simp only [map_sub, map_mul, map_add, MvPolynomial.eval_X, Sum.elim_inl,
      Sum.elim_inr, (hab z).1, (hab z).2, Complex.mul_re, Complex.mul_im, and_self]

lemma finite_real_equations {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ) :
    ∃ a b : Fin m → MvPolynomial (Fin n ⊕ Fin n) ℝ,
      ∀ z : Fin n → ℂ, z ∈ zeroSet p ↔
        (∀ j, MvPolynomial.eval (Sum.elim (fun i => (z i).re) (fun i => (z i).im))
          (a j) = 0) ∧
        (∀ j, MvPolynomial.eval (Sum.elim (fun i => (z i).re) (fun i => (z i).im))
          (b j) = 0) := by
  choose a b hab using fun j => polynomial_real_imaginary (p j)
  refine ⟨a, b, fun z => ?_⟩
  simp only [(hab _ z).1, (hab _ z).2, zeroSet, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨fun j => by rw [h j]; rfl, fun j => by rw [h j]; rfl⟩
  · rintro ⟨ha, hb⟩ j
    apply Complex.ext
    · simpa only [Complex.zero_re] using ha j
    · simpa only [Complex.zero_im] using hb j

end HodgeLean.Foundations.ComplexTopology
