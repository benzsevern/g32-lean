import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductSymmetry
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorProductPower
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerQuotientField

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The coordinate product descends to the retained symmetric quotient field. -/
theorem s2v_l1b_divisor_product_function_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [IsIntegral B.left]
    [LocallyOfFiniteType Z.hom] (n : ℕ) [IsIntegral (g3_power Z n).left]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [IsDominant γ.left]
    (hγinv : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (v : Z.left.functionField) :
    ∃ b : B.left.functionField, s2v_l1b_functionFieldPullback γ.left b =
      s2v_l1b_divisor_product_function Z n v := by
  letI : ∀ σ : Equiv.Perm (Fin n), IsIso (s2_permute Z n σ) :=
    fun σ => (s2_permuteIso Z n σ).isIso_hom
  letI := (s2v_l1b_functionFieldPullback γ.left).hom.toAlgebra
  have hcover (σ : Equiv.Perm (Fin n)) :=
    s2v_l1b_cover_field_algEquiv γ.left (s2_permute Z n σ).left
      (congrArg Over.Hom.left (hγinv σ))
  choose τ hτ using hcover
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := genericPoint B.left) (U := ⊤) trivial
  letI : Nonempty U := ⟨⟨genericPoint B.left, hxU⟩⟩
  apply s2v_l1b_categorical_quotient_fixed_rational_function
    (g3_power Z n) B γ (s2_permute Z n) hγinv hγ ⟨U, hU⟩ τ hτ
  intro σ
  change (τ σ).toRingHom (s2v_l1b_divisor_product_function Z n v) = _
  rw [hτ σ]
  exact s2v_l1b_divisor_product_function_permute Z n σ v

/-- A curve binomial equation gives a nonzero symmetric base coefficient for its coordinate product. -/
theorem s2v_l1b_divisor_product_binomial_descent
    (Y Z B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsIntegral Z.left] [IsIntegral B.left]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (f : Y ⟶ Z) [IsDominant f.left] (n : ℕ)
    [IsIntegral (g3_power Y n).left] [IsIntegral (g3_power Z n).left]
    [IsDominant (s2_powerMap f n).left]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [IsDominant γ.left]
    (hγinv : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (g : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ g = g) → ∃! b : B ⟶ T, γ ≫ b = g)
    (u : Y.left.functionField) (v : Z.left.functionField) (m : ℕ)
    (hu : u ≠ 0) (hpow : u ^ m = s2v_l1b_functionFieldPullback f.left v) :
    ∃ b : B.left.functionField, b ≠ 0 ∧
      s2v_l1b_functionFieldPullback γ.left b = s2v_l1b_divisor_product_function Z n v ∧
      s2v_l1b_divisor_product_function Y n u ^ m =
        s2v_l1b_functionFieldPullback (s2_powerMap f n).left
          (s2v_l1b_functionFieldPullback γ.left b) := by
  have hv : v ≠ 0 := by
    intro hv
    rw [hv, map_zero] at hpow
    exact pow_ne_zero m hu hpow
  obtain ⟨b, hb⟩ := s2v_l1b_divisor_product_function_descent Z B n γ hγinv hγ v
  refine ⟨b, ?_, hb, ?_⟩
  · intro h
    have hz := s2v_l1b_divisor_product_function_ne_zero Z n v hv
    rw [h, map_zero] at hb
    exact hz hb.symm
  · rw [s2v_l1b_divisor_product_function_pow, hpow,
      s2v_l1b_divisor_product_function_pullback, hb]

end HodgeLean.Foundations.Program
