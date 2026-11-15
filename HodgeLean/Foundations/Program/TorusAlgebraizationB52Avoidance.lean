import HodgeLean.Foundations.Program.TorusAlgebraizationB52Theta
import HodgeLean.Foundations.AnalyticDivisorAlgebraicProofs

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem b52_dense_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) :
    Dense {x | f x ≠ 0} := by
  exact interior_eq_empty_iff_dense_compl.mp
    (AnalyticDivisorAlgebraic.spec_interior_zeroSet_eq_empty_of_differentiable_aux hf hne)

theorem b52_balanced_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) (z : E) :
    ∃ a b c : E, a + b + c = 0 ∧
      f (z + a) ≠ 0 ∧ f (z + b) ≠ 0 ∧ f (z + c) ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    exact hne (funext fun x ↦ by simpa using not_not.mp (not_exists.mp h x))
  let a := x - z
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
  refine ⟨a, b, -a - b, ?_, ?_, hb', hb⟩
  · abel
  · change f (z + (x - z)) ≠ 0
    convert hx using 1 <;> congr 1 <;> abel

theorem b52_basepoint_of_nonzero_section (Λ : Type*) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (s : b5_sections Λ F hF Q 1)
    (hs : s.val ≠ 0) (z : b5_V Λ F) :
    ∃ t : b5_sections Λ F hF Q 3, t.val z ≠ 0 := by
  obtain ⟨a, b, c, habc, ha, hb, hc⟩ := b52_balanced_nonzero s.property.1 hs z
  exact ⟨b5_balancedCubeSection Λ F hF Q s s s a b c habc,
    mul_ne_zero (mul_ne_zero ha hb) hc⟩

#print axioms b52_dense_nonzero
#print axioms b52_balanced_nonzero
#print axioms b52_basepoint_of_nonzero_section

end HodgeLean.Foundations.Program
