import HodgeLean.Foundations.Program.SchoenCycleInsertionParameters
import HodgeLean.Foundations.Program.SchoenCycleIntegralImageStalkKernel
import HodgeLean.Foundations.Program.SchoenCycleInsertionImmersion
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

/-! # Actual parameters killed by permuted marked insertion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- A permuted marked insertion kills the parameter at its specified marked coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_permutedInsertion_parameter_zero
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (σ : Equiv.Perm (Fin (n + 1)))
    (y : ComplexPoint (g3_power Z n)) :
    let f := s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ
    f.left.stalkMap y.underlying
      (s2e_curvePowerParameter Z (n + 1) (Point.map f y) (σ 0)) = 0 := by
  dsimp only
  change ((s2c_branchInsertion Z n a).left ≫ (s2_permute Z (n + 1) σ).left).stalkMap
    y.underlying (s2e_curvePowerParameter Z (n + 1)
      (Point.map (s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ) y) (σ 0)) = 0
  rw [Scheme.Hom.stalkMap_comp]
  change (s2c_branchInsertion Z n a).left.stalkMap y.underlying
    ((s2_permute Z (n + 1) σ).left.stalkMap
      (Point.map (s2c_branchInsertion Z n a) y).underlying
      (s2e_curvePowerParameter Z (n + 1)
        (Point.map (s2_permute Z (n + 1) σ)
          (Point.map (s2c_branchInsertion Z n a) y)) (σ 0))) = 0
  rw [s2e_curvePowerParameter_permute, Equiv.symm_apply_apply]
  exact s2e_branchInsertion_curvePowerParameter_zero Z n a y

/-- A parameter product containing the marked coordinate belongs to the actual permuted insertion image ideal in its target stalk.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_permutedInsertion_product_mem_image_stalk
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (σ : Equiv.Perm (Fin (n + 1)))
    (y : ComplexPoint (g3_power Z n)) (S : Finset (Fin (n + 1))) (hS : σ 0 ∈ S)
    (U : (g3_power Z (n + 1)).left.affineOpens)
    (hyU : (s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ).left y.underlying ∈ U.1) :
    let f := s2c_branchInsertion Z n a ≫ s2_permute Z (n + 1) σ
    (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) (Point.map f y) i) ∈
      Ideal.map ((g3_power Z (n + 1)).left.presheaf.germ U.1
        (f.left y.underlying) hyU).hom (f.left.ker.ideal U) := by
  let u := s2_permute Z (n + 1) σ
  letI : IsIso u := s2e_step1_action_isIso (g3_power Z (n + 1))
    (Equiv.Perm (Fin (n + 1))) (s2_permute Z (n + 1))
    (s2e_step1_permute_one Z (n + 1)) (s2e_step1_permute_mul Z (n + 1)) σ
  letI : IsClosedImmersion (s2c_branchInsertion Z n a).left :=
    s2e_branchInsertion_isClosedImmersion Z n a
  let f := s2c_branchInsertion Z n a ≫ u
  letI : IsFinite f.left := by
    change IsFinite ((s2c_branchInsertion Z n a).left ≫ u.left)
    infer_instance
  dsimp only
  rw [s2e_integral_image_ideal_stalk_kernel f.left U y.underlying hyU]
  change f.left.stalkMap y.underlying
    (∏ i ∈ S, s2e_curvePowerParameter Z (n + 1) (Point.map f y) i) = 0
  have hd := map_dvd (f.left.stalkMap y.underlying).hom
    (Finset.dvd_prod_of_mem (fun i =>
      s2e_curvePowerParameter Z (n + 1) (Point.map f y) i) hS)
  rw [s2e_permutedInsertion_parameter_zero Z n a σ y] at hd
  exact zero_dvd_iff.mp hd

end HodgeLean.Foundations.Program
