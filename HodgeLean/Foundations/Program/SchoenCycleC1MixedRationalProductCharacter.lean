import HodgeLean.Foundations.Program.SchoenCycleC1PermutationRationalProduct
import HodgeLean.Foundations.Program.SchoenCycleC1LocalSquareComposition
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackScalars
import HodgeLean.Foundations.Program.SchoenCycleC1MixedActionIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual coordinate product transforms by the total translation
character under every specified mixed scheme action. -/
theorem s2e_c1_mixed_rational_product_character
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (N : ℕ) (φ : Fin N → (Y.left.functionField →+* (g3_power Y N).left.functionField))
    (hφ : ∀ i (p : (g3_power Y N).left) (r : Y.left.presheaf.stalk ((g3_proj Y N i).left p)),
      φ i (algebraMap (Y.left.presheaf.stalk ((g3_proj Y N i).left p)) Y.left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk p) (g3_power Y N).left.functionField
          (((g3_proj Y N i).left.stalkMap p).hom r))
    (χ : Multiplicative (ZMod S.m) →* ℂˣ) (f : Y.left.functionField)
    (heig : ∀ t : ZMod S.m,
      letI := s2e_step1_action_isIso Y (S.H ⧸ S.χ.ker) a ha1 hamul (e.symm (.ofAdd t))
      s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd t))).left f =
        HodgeLean.Foundations.Curves.stalkC (genericPoint Y.left) (χ (.ofAdd t) : ℂ) * f)
    (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)) :
    letI := s2e_c1_mixed_action_isIso S Y a e ha1 hamul N v σ
    s2e_step1_fieldPullback (g3_power Y N).left
      (s2_action S Y a e N v σ).left (∏ i, φ i f) =
        HodgeLean.Foundations.Curves.stalkC (genericPoint (g3_power Y N).left)
          (χ (.ofAdd (∑ i, v i)) : ℂ) * ∏ i, φ i f := by
  letI : ∀ u, IsIso (a u) := s2e_step1_action_isIso Y (S.H ⧸ S.χ.ker) a ha1 hamul
  letI := s2e_c1_mixed_action_isIso S Y a e ha1 hamul N v σ
  have hcoord (i : Fin N) :
      s2e_step1_fieldPullback (g3_power Y N).left
          (s2_action S Y a e N v σ).left (φ i f) =
        HodgeLean.Foundations.Curves.stalkC (genericPoint (g3_power Y N).left)
          (χ (.ofAdd (v i)) : ℂ) * φ (σ.symm i) f := by
    have hp : s2_action S Y a e N v σ ≫ g3_proj Y N i =
        g3_proj Y N (σ.symm i) ≫ a (e.symm (.ofAdd (v i))) :=
      s2_check_lift_proj _ _ _
    have hp' : (s2_action S Y a e N v σ).left ≫ (g3_proj Y N i).left =
        (g3_proj Y N (σ.symm i)).left ≫ (a (e.symm (.ofAdd (v i)))).left :=
      congrArg Over.Hom.left hp
    have hγ := s2e_c1_rational_local_square_comp (g3_proj Y N (σ.symm i)).left
      (a (e.symm (.ofAdd (v i)))).left (φ (σ.symm i))
      (s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd (v i)))).left)
      (hφ (σ.symm i))
      (s2e_c1_automorphism_rational_local_square Y.left (a (e.symm (.ofAdd (v i)))).left)
    rw [← hp'] at hγ
    have he := s2e_c1_generic_pullback_composition
      (s2_action S Y a e N v σ).left (g3_proj Y N i).left
      (s2e_step1_fieldPullback (g3_power Y N).left (s2_action S Y a e N v σ).left)
      (φ i) ((φ (σ.symm i)).comp
        (s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd (v i)))).left))
      (s2e_c1_automorphism_rational_local_square (g3_power Y N).left
        (s2_action S Y a e N v σ).left) (hφ i) hγ
    have heval := RingHom.congr_fun he f
    change φ (σ.symm i) (s2e_step1_fieldPullback Y.left
      (a (e.symm (.ofAdd (v i)))).left f) =
      s2e_step1_fieldPullback (g3_power Y N).left
        (s2_action S Y a e N v σ).left (φ i f) at heval
    rw [← heval]
    change φ (σ.symm i) (s2e_step1_fieldPullback Y.left
      (a (e.symm (.ofAdd (v i)))).left f) = _
    rw [heig, map_mul, s2e_c1_rational_pullback_complex_scalars (g3_power Y N) Y
      (g3_proj Y N (σ.symm i)) (φ (σ.symm i)) (hφ (σ.symm i))]
  rw [map_prod]
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  let θ : Multiplicative (ZMod S.m) →* (g3_power Y N).left.functionField :=
    (HodgeLean.Foundations.Curves.stalkC (genericPoint (g3_power Y N).left)).toMonoidHom.comp
      ((Units.coeHom ℂ).comp χ)
  have hc : (∏ i, θ (.ofAdd (v i))) = θ (.ofAdd (∑ i, v i)) := by
    rw [← map_prod]
    rfl
  change (∏ i, θ (.ofAdd (v i))) * _ = θ (.ofAdd (∑ i, v i)) * _
  rw [hc, σ.symm.prod_comp (fun i => φ i f)]

end HodgeLean.Foundations.Program
