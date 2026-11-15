import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerJets
import HodgeLean.Foundations.Program.SchoenCycleParameterPullback
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkAction
import HodgeLean.Foundations.Program.SchoenCyclePointIdealStabilizer

/-! # Actual curve-power parameters under coordinate permutations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Equal actual power points have equal coordinate parameters after stalk transport.
Source: Hartshorne, Algebraic Geometry, II.2, stalk transport. -/
theorem s2e_curvePowerParameter_congr
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x y : ComplexPoint (g3_power X n)) (h : x = y) (i : Fin n) :
    ((g3_power X n).left.presheaf.stalkCongr (.of_eq (congrArg Point.underlying h))).hom
      (s2e_curvePowerParameter X n x i) = s2e_curvePowerParameter X n y i := by
  subst y
  simp

/-- Pullback by an actual coordinate permutation renames the consistently
chosen curve-power parameters, including at repeated points.
Source: Hartshorne, Algebraic Geometry, II.2; Schoen, Compositio Mathematica
65 (1988), §2, printed p. 12, symmetric-power coordinate permutations. -/
theorem s2e_curvePowerParameter_permute
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : ComplexPoint (g3_power X n)) (i : Fin n) :
    (s2_permute X n σ).left.stalkMap x.underlying
      (s2e_curvePowerParameter X n (Point.map (s2_permute X n σ) x) i) =
        s2e_curvePowerParameter X n x (σ.symm i) := by
  let P := g3_power X n
  let q := s2_permute X n σ
  change q.left.stalkMap x.underlying
      (s2e_curvePullbackParameter X P (g3_proj X n i) (Point.map q x)) =
    s2e_curvePullbackParameter X P (g3_proj X n (σ.symm i)) x
  rw [s2e_curvePullbackParameter_comp]
  have he : q ≫ g3_proj X n i = g3_proj X n (σ.symm i) := s2_check_lift_proj n _ i
  rw [he]

/-- At a fixed actual tuple, the transported stalk pullback of a coordinate
permutation renames the regular parameters.
Source: Hartshorne, Algebraic Geometry, II.2; Schoen, Compositio Mathematica
65 (1988), §2, printed p. 12, symmetric-power coordinate permutations. -/
theorem s2e_fixed_permutation_curvePowerParameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : ComplexPoint (g3_power X n))
    (hx : Point.map (s2_permute X n σ) x = x) (i : Fin n) :
    s2e_fixed_point_stalkPullback (g3_power X n).left (s2_permute X n σ).left x.underlying
      (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ) x hx)
      (s2e_curvePowerParameter X n x i) = s2e_curvePowerParameter X n x (σ.symm i) := by
  let P := g3_power X n
  let q := s2_permute X n σ
  let hp : q.left x.underlying = x.underlying := s2e_complex_point_fixed_underlying P q x hx
  have he : (P.left.presheaf.stalkCongr (.of_eq hp)).inv =
      (P.left.presheaf.stalkCongr (.of_eq hp.symm)).hom := by
    simp only [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.stalkCongr_hom]
  have hc : (P.left.presheaf.stalkCongr (.of_eq hp.symm)).hom
      (s2e_curvePowerParameter X n x i) =
        s2e_curvePowerParameter X n (Point.map q x) i :=
    s2e_curvePowerParameter_congr X n x (Point.map q x) hx.symm i
  change (q.left.stalkMap x.underlying).hom
    ((P.left.presheaf.stalkCongr (.of_eq hp)).inv.hom (s2e_curvePowerParameter X n x i)) = _
  rw [he]
  change q.left.stalkMap x.underlying
    ((P.left.presheaf.stalkCongr (.of_eq hp.symm)).hom (s2e_curvePowerParameter X n x i)) = _
  rw [hc]
  exact s2e_curvePowerParameter_permute X n σ x i

end HodgeLean.Foundations.Program
