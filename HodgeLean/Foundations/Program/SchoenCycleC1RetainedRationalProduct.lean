import HodgeLean.Foundations.Program.SchoenCycleC1PermutationRationalProduct
import HodgeLean.Foundations.Program.SchoenCycleC1LocalSquareComposition
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackScalars
import HodgeLean.Foundations.Program.SchoenCycleRetainedAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual coordinate product of a curve rational eigenfunction is
fixed by each retained zero-sum translation and permutation. -/
theorem s2e_c1_retained_rational_product_invariant
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
    (g : s2e_Retained S.m N) :
    letI := s2e_step1_action_isIso (g3_power Y N) (s2e_Retained S.m N)
      (s2e_retainedAction S Y a e N)
      (s2e_retainedAction_laws S Y a e ha1 hamul N).1
      (s2e_retainedAction_laws S Y a e ha1 hamul N).2 g
    s2e_step1_fieldPullback (g3_power Y N).left
      (s2e_retainedAction S Y a e N g).left (∏ i, φ i f) = ∏ i, φ i f := by
  letI : ∀ u, IsIso (a u) := s2e_step1_action_isIso Y (S.H ⧸ S.χ.ker) a ha1 hamul
  letI := s2e_step1_action_isIso (g3_power Y N) (s2e_Retained S.m N)
    (s2e_retainedAction S Y a e N)
    (s2e_retainedAction_laws S Y a e ha1 hamul N).1
    (s2e_retainedAction_laws S Y a e ha1 hamul N).2 g
  have hcoord (i : Fin N) :
      s2e_step1_fieldPullback (g3_power Y N).left
          (s2e_retainedAction S Y a e N g).left (φ i f) =
        HodgeLean.Foundations.Curves.stalkC (genericPoint (g3_power Y N).left)
          (χ (.ofAdd (g.vector i)) : ℂ) * φ (g.perm.symm i) f := by
    have hp : s2e_retainedAction S Y a e N g ≫ g3_proj Y N i =
        g3_proj Y N (g.perm.symm i) ≫ a (e.symm (.ofAdd (g.vector i))) :=
      s2_check_lift_proj _ _ _
    have hp' : (s2e_retainedAction S Y a e N g).left ≫ (g3_proj Y N i).left =
        (g3_proj Y N (g.perm.symm i)).left ≫ (a (e.symm (.ofAdd (g.vector i)))).left :=
      congrArg Over.Hom.left hp
    have hγ := s2e_c1_rational_local_square_comp (g3_proj Y N (g.perm.symm i)).left
      (a (e.symm (.ofAdd (g.vector i)))).left (φ (g.perm.symm i))
      (s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd (g.vector i)))).left)
      (hφ (g.perm.symm i))
      (s2e_c1_automorphism_rational_local_square Y.left (a (e.symm (.ofAdd (g.vector i)))).left)
    rw [← hp'] at hγ
    have he := s2e_c1_generic_pullback_composition
      (s2e_retainedAction S Y a e N g).left (g3_proj Y N i).left
      (s2e_step1_fieldPullback (g3_power Y N).left (s2e_retainedAction S Y a e N g).left)
      (φ i) ((φ (g.perm.symm i)).comp
        (s2e_step1_fieldPullback Y.left (a (e.symm (.ofAdd (g.vector i)))).left))
      (s2e_c1_automorphism_rational_local_square (g3_power Y N).left
        (s2e_retainedAction S Y a e N g).left) (hφ i) hγ
    have heval := RingHom.congr_fun he f
    change φ (g.perm.symm i) (s2e_step1_fieldPullback Y.left
      (a (e.symm (.ofAdd (g.vector i)))).left f) =
      s2e_step1_fieldPullback (g3_power Y N).left
        (s2e_retainedAction S Y a e N g).left (φ i f) at heval
    rw [← heval]
    change φ (g.perm.symm i) (s2e_step1_fieldPullback Y.left
      (a (e.symm (.ofAdd (g.vector i)))).left f) = _
    rw [heig, map_mul, s2e_c1_rational_pullback_complex_scalars (g3_power Y N) Y
      (g3_proj Y N (g.perm.symm i)) (φ (g.perm.symm i)) (hφ (g.perm.symm i))]
  rw [map_prod]
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  let θ : Multiplicative (ZMod S.m) →* (g3_power Y N).left.functionField :=
    (HodgeLean.Foundations.Curves.stalkC (genericPoint (g3_power Y N).left)).toMonoidHom.comp
      ((Units.coeHom ℂ).comp χ)
  have hc : (∏ i, θ (.ofAdd (g.vector i))) = 1 := by
    rw [← map_prod]
    change θ (.ofAdd (∑ i, g.vector i)) = 1
    rw [g.zero_sum, ofAdd_zero, map_one]
  change (∏ i, θ (.ofAdd (g.vector i))) * _ = _
  rw [hc, one_mul]
  exact g.perm.symm.prod_comp (fun i => φ i f)

end HodgeLean.Foundations.Program
