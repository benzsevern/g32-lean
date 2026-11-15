import HodgeLean.Foundations.Program.TorusAlgebraizationB52Avoidance

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b52_fixed_balanced_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) (z a : E) :
    ∃ b c : E, a + b + c = 0 ∧ f (z + b) ≠ 0 ∧ f (z + c) ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    exact hne (funext fun x ↦ by simpa using not_not.mp (not_exists.mp h x))
  let g : E → ℂ := fun b ↦ f (z + (-a - b))
  have hg : Differentiable ℂ g :=
    hf.comp (differentiable_const z |>.add ((differentiable_const (-a)).sub differentiable_id))
  have hg0 : g ≠ 0 := by
    intro h
    have he := congrFun h (z - a - x)
    have heq : z + (-a - (z - a - x)) = x := by abel
    exact hx (by simpa only [g, heq, Pi.zero_apply] using he)
  have ho : IsOpen {b : E | f (z + b) ≠ 0} :=
    isOpen_ne.preimage (hf.continuous.comp (continuous_const.add continuous_id))
  have hn : Set.Nonempty {b : E | f (z + b) ≠ 0} := by
    refine ⟨x - z, ?_⟩
    change f (z + (x - z)) ≠ 0
    convert hx using 1 <;> congr 1 <;> abel
  obtain ⟨b, hb, hb'⟩ := (b52_dense_nonzero hg hg0).exists_mem_open ho hn
  exact ⟨b, -a - b, by abel, hb', hb⟩

#print axioms b52_fixed_balanced_nonzero

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_cubic_zero_and_nonzero (s : b5_sections Λ F hF Q 1)
    (z w a : b5_V Λ F) (hsz : s.val (z + a) = 0) (hsw : s.val (w + a) ≠ 0) :
    ∃ t : b5_sections Λ F hF Q 3, t.val z = 0 ∧ t.val w ≠ 0 := by
  have hs : s.val ≠ 0 := fun h ↦ hsw (congrFun h (w + a))
  obtain ⟨b, c, habc, hb, hc⟩ := b52_fixed_balanced_nonzero s.property.1 hs w a
  refine ⟨b5_balancedCubeSection Λ F hF Q s s s a b c habc, ?_, ?_⟩
  · change s.val (z + a) * s.val (z + b) * s.val (z + c) = 0
    rw [hsz, zero_mul, zero_mul]
  · exact mul_ne_zero (mul_ne_zero hsw hb) hc

#print axioms b52_cubic_zero_and_nonzero

theorem b52_separates_points_of_theta_zero (s : b5_sections Λ F hF Q 1)
    (z w a : b5_V Λ F) (hsz : s.val (z + a) = 0) (hsw : s.val (w + a) ≠ 0) :
    ∃ u t : b5_sections Λ F hF Q 3, u.val z * t.val w ≠ u.val w * t.val z := by
  have hs : s.val ≠ 0 := fun h ↦ hsw (congrFun h (w + a))
  obtain ⟨t, htz, htw⟩ := b52_cubic_zero_and_nonzero Λ F hF Q s z w a hsz hsw
  obtain ⟨u, huz⟩ := b52_basepoint_of_nonzero_section Λ F hF Q s hs z
  refine ⟨u, t, ?_⟩
  rw [htz, mul_zero]
  exact mul_ne_zero huz htw

#print axioms b52_separates_points_of_theta_zero

theorem b52_fderiv_translated_triple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g h : E → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hh : Differentiable ℂ h) (a b c z v : E) (hz : f (z + a) = 0) :
    fderiv ℂ (fun x ↦ f (x + a) * g (x + b) * h (x + c)) z v =
      fderiv ℂ f (z + a) v * g (z + b) * h (z + c) := by
  have hfa := (hf (z + a)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const a)
  have hgb := (hg (z + b)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const b)
  have hhc := (hh (z + c)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const c)
  have he := congrArg (fun L : E →L[ℂ] ℂ ↦ L v) ((hfa.mul hgb).mul hhc).fderiv
  simpa only [Function.comp_def, id_eq, Pi.mul_def, Pi.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, hz, zero_mul, mul_zero, add_zero, zero_add, mul_assoc, mul_comm,
    mul_left_comm] using he

#print axioms b52_fderiv_translated_triple

theorem b52_separates_tangent_of_theta_simple_zero (s : b5_sections Λ F hF Q 1)
    (z v a : b5_V Λ F) (hsz : s.val (z + a) = 0)
    (hder : fderiv ℂ s.val (z + a) v ≠ 0) :
    ∃ t : b5_sections Λ F hF Q 3, t.val z = 0 ∧ fderiv ℂ t.val z v ≠ 0 := by
  have hs : s.val ≠ 0 := by
    intro h
    apply hder
    simp [h]
  obtain ⟨b, c, habc, hb, hc⟩ := b52_fixed_balanced_nonzero s.property.1 hs z a
  refine ⟨b5_balancedCubeSection Λ F hF Q s s s a b c habc, ?_, ?_⟩
  · change s.val (z + a) * s.val (z + b) * s.val (z + c) = 0
    rw [hsz, zero_mul, zero_mul]
  · change fderiv ℂ (fun x ↦ s.val (x + a) * s.val (x + b) * s.val (x + c)) z v ≠ 0
    rw [b52_fderiv_translated_triple s.val s.val s.val s.property.1 s.property.1
      s.property.1 a b c z v hsz]
    exact mul_ne_zero (mul_ne_zero hder hb) hc

#print axioms b52_separates_tangent_of_theta_simple_zero

end HodgeLean.Foundations.Program
