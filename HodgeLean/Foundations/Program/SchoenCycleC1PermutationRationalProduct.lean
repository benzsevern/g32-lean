import HodgeLean.Foundations.Program.SchoenCycleC1GenericPullbackComposition
import HodgeLean.Foundations.Program.SchoenCycleC1AutomorphismLocalSquare
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The product of actual coordinate rational pullbacks is fixed by the
specified scheme permutations, with their original inverse-index convention. -/
theorem s2e_c1_permutation_rational_product_invariant
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (N : ℕ) (φ : Fin N → (Y.left.functionField →+* (g3_power Y N).left.functionField))
    (hφ : ∀ i (p : (g3_power Y N).left) (r : Y.left.presheaf.stalk ((g3_proj Y N i).left p)),
      φ i (algebraMap (Y.left.presheaf.stalk ((g3_proj Y N i).left p)) Y.left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk p) (g3_power Y N).left.functionField
          (((g3_proj Y N i).left.stalkMap p).hom r))
    (f : Y.left.functionField) (σ : Equiv.Perm (Fin N)) :
    letI := s2e_step1_action_isIso (g3_power Y N) (Equiv.Perm (Fin N))
      (s2_permute Y N) (s2e_step1_permute_one Y N) (s2e_step1_permute_mul Y N) σ
    s2e_step1_fieldPullback (g3_power Y N).left (s2_permute Y N σ).left (∏ i, φ i f) =
      ∏ i, φ i f := by
  letI := s2e_step1_action_isIso (g3_power Y N) (Equiv.Perm (Fin N))
    (s2_permute Y N) (s2e_step1_permute_one Y N) (s2e_step1_permute_mul Y N) σ
  have hcoord (i : Fin N) :
      s2e_step1_fieldPullback (g3_power Y N).left (s2_permute Y N σ).left (φ i f) =
        φ (σ.symm i) f := by
    have hp : s2_permute Y N σ ≫ g3_proj Y N i = g3_proj Y N (σ.symm i) :=
      s2_check_lift_proj N (fun j => g3_proj Y N (σ.symm j)) i
    have hp' : (s2_permute Y N σ).left ≫ (g3_proj Y N i).left =
        (g3_proj Y N (σ.symm i)).left := congrArg Over.Hom.left hp
    have hγ := hφ (σ.symm i)
    rw [← hp'] at hγ
    have he := s2e_c1_generic_pullback_composition
      (s2_permute Y N σ).left (g3_proj Y N i).left
      (s2e_step1_fieldPullback (g3_power Y N).left (s2_permute Y N σ).left)
      (φ i) (φ (σ.symm i))
      (s2e_c1_automorphism_rational_local_square (g3_power Y N).left (s2_permute Y N σ).left)
      (hφ i) hγ
    exact RingHom.congr_fun he.symm f
  rw [map_prod]
  simp_rw [hcoord]
  exact σ.symm.prod_comp (fun i => φ i f)

end HodgeLean.Foundations.Program
