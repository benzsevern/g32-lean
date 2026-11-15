import HodgeLean.Foundations.Program.SchoenTransferPrimitiveBaseChange
import HodgeLean.Foundations.Program.SchoenTransferFiniteBaseChange
import HodgeLean.Foundations.Program.SchoenTransferCurveTensorActions

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- The specified action is the actual permutation followed by its actual deck tuple.
Source: Schoen (1988), §1, p. 5, the coordinate definition of the semidirect action. -/
theorem s4_deck_permutation_factor
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (h : ℕ) (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)) :
    s2_action S Y a e h v σ = s2_permute Y h σ ≫ s2_action S Y a e h v 1 := by
  apply s4_e1_power_hom_ext
  intro i
  have hp : s2_permute Y h σ ≫ g3_proj Y h i = g3_proj Y h (σ.symm i) :=
    s4_e1_power_lift_projection h (fun k => g3_proj Y h (σ.symm k)) i
  have hd := s4_e1_action_projection S Y a e h v 1 i
  change s2_action S Y a e h v 1 ≫ g3_proj Y h i =
    g3_proj Y h i ≫ a (e.symm (.ofAdd (v i))) at hd
  rw [s4_e1_action_projection, Category.assoc, hd, ← Category.assoc, hp]

/-- The defining primitive and fixed equations characterize the scalar-extended invariant space.
Source: Schoen (1988), Lemmas 1.1–1.2, pp. 5–6; finite intersections under scalar extension. -/
theorem s4_primitive_baseChange_mem_iff
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (h : ℕ) (hh : 0 < h)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (z : ℂ ⊗[ℚ] HQ (g3_power Y h) h) :
    z ∈ (s4_invariantPrimitive S Y a e h hh).baseChange ℂ ↔
      (Polynomial.aeval
        (homPullback (s2_action S Y a e h (s2_delta S h hh 1) 1) h)
        (Polynomial.cyclotomic S.m ℚ)).baseChange ℂ z = 0 ∧
      ∀ (v : Fin h → ZMod S.m), (∑ i, v i) = 0 →
        ∀ σ : Equiv.Perm (Fin h),
          (homPullback (s2_action S Y a e h v σ) h).baseChange ℂ z = z := by
  classical
  simp only [s4_invariantPrimitive, HodgeLean.Foundations.baseChange_inf,
    s4_baseChange_iInf, ← ker_baseChange, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.baseChange_sub, LinearMap.baseChange_id,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, Subtype.forall]

end HodgeLean.Foundations.Program
