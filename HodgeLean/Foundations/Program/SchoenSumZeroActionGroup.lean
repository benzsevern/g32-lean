import HodgeLean.Foundations.Program.SchoenSumZeroAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual subgroup of product automorphisms given by zero-sum translations and permutations. -/
def s2_sumZeroActionGroup (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u) (h : ℕ) :
    Subgroup (Aut (g3_power Y h)) where
  carrier := {f | ∃ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
    ∑ i, v i = 0 ∧ f.asIso.hom = s2_action S Y a e h v σ}
  one_mem' := ⟨0, 1, by simp only [Pi.zero_apply, Finset.sum_const_zero],
    (s2_coordinateAction_laws S Y a e ha1 hamul h).1.symm⟩
  mul_mem' := by
    rintro f g ⟨v, σ, hv, hf⟩ ⟨w, τ, hw, hg⟩
    refine ⟨(fun i => v i + w (σ.symm i)), σ * τ, ?_, ?_⟩
    · rw [Finset.sum_add_distrib, Equiv.sum_comp, hv, hw, add_zero]
    · change g.asIso.hom ≫ f.asIso.hom = _
      rw [hg, hf, (s2_coordinateAction_laws S Y a e ha1 hamul h).2]
  inv_mem' := by
    rintro f ⟨v, σ, hv, hf⟩
    refine ⟨(fun i => -v (σ i)), σ⁻¹, ?_, ?_⟩
    · rw [Finset.sum_neg_distrib, Equiv.sum_comp, hv, neg_zero]
    · have heq : f = Aut.of (s2_coordinateActionIso S Y a e ha1 hamul h v σ) := by
        apply Aut.ext
        apply Iso.ext
        exact hf
      subst f
      rfl

end HodgeLean.Foundations.Program
