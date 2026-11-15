import HodgeLean.Foundations.Program.TorusAlgebraizationB52Avoidance

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

def b54_evalPolynomial (z : b5_V Λ F) : b5_S Λ F hF Q →+* Polynomial ℂ :=
  DirectSum.toSemiring
    (fun n ↦ { toFun := fun s ↦ Polynomial.monomial n (s.val z)
               map_zero' := by simp
               map_add' := by intros; simp })
    (by simp [GradedMonoid.GOne.one])
    (by intro i j s t; simp [Polynomial.monomial_mul_monomial]; rfl)

theorem b54_evalPolynomial_coeff (z : b5_V Λ F) (r : b5_S Λ F hF Q) (n : ℕ) :
    (b54_evalPolynomial Λ F hF Q z r).coeff n = (r n).val z := by
  classical
  induction r using DirectSum.induction_on with
  | zero => simp
  | of i s =>
    by_cases h : i = n
    · subst n
      simp [b54_evalPolynomial, DirectSum.of_apply]
    · simp [b54_evalPolynomial, DirectSum.of_apply, Polynomial.coeff_monomial, h]
  | add r s hr hs => simp [hr, hs]

theorem b54_S_isDomain : IsDomain (b5_S Λ F hF Q) := by
  classical
  letI : Nontrivial (b5_S Λ F hF Q) :=
    ⟨⟨1, 0, fun h ↦ (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using congrArg (b5_eval Λ F hF Q 0) h)⟩⟩
  letI : NoZeroDivisors (b5_S Λ F hF Q) := by
    constructor
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    by_cases hy : y = 0
    · exact Or.inr hy
    exfalso
    have hn (r : b5_S Λ F hF Q) (hr : r ≠ 0) : ∃ n, (r n).val ≠ 0 := by
      by_contra! he
      apply hr
      apply DFinsupp.ext
      intro n
      exact Subtype.ext (he n)
    obtain ⟨i, hi⟩ := hn x hx
    obtain ⟨j, hj⟩ := hn y hy
    have ho : IsOpen {z | (y j).val z ≠ 0} :=
      isOpen_ne.preimage (y j).property.1.continuous
    have hne : Set.Nonempty {z | (y j).val z ≠ 0} := by
      obtain ⟨z, hz⟩ := Function.ne_iff.mp hj
      exact ⟨z, hz⟩
    obtain ⟨z, hz, hz'⟩ := (b52_dense_nonzero (x i).property.1 hi).exists_mem_open ho hne
    have hp (r : b5_S Λ F hF Q) (n : ℕ) (hr : (r n).val z ≠ 0) :
        b54_evalPolynomial Λ F hF Q z r ≠ 0 := by
      intro he
      apply hr
      have hc := congrArg (fun p : Polynomial ℂ ↦ p.coeff n) he
      simpa only [b54_evalPolynomial_coeff, Polynomial.coeff_zero] using hc
    exact (mul_ne_zero (hp x i hz) (hp y j hz'))
      (by simpa only [map_mul, map_zero] using congrArg (b54_evalPolynomial Λ F hF Q z) hxy)
  exact NoZeroDivisors.to_isDomain _

end HodgeLean.Foundations.Program
