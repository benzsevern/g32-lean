import HodgeLean.Foundations.Program.SchoenCycleInsertionPolynomialAction
import HodgeLean.Foundations.Program.SchoenCyclePowerPolynomialVanishing
import HodgeLean.Foundations.Program.SchoenCyclePolynomialIdealControl

/-! # Finite-order ideal control in actual insertion stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Vanishing to finite order after actual insertion forces membership in the
sum of the marked parameter ideal and that total-order power ideal.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_branchInsertion_stalk_power_kernel_control
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (a : ComplexPoint Z) (x : ComplexPoint (g3_power Z n))
    (N : ℕ) (hN : 0 < N)
    (r : (g3_power Z (n + 1)).left.presheaf.stalk
      (Point.map (s2c_branchInsertion Z n a) x).underlying)
    (hr : (s2c_branchInsertion Z n a).left.stalkMap x.underlying r ∈
      IsLocalRing.maximalIdeal ((g3_power Z n).left.presheaf.stalk x.underlying) ^ N) :
    r ∈ Ideal.span (Set.singleton (s2e_curvePowerParameter Z (n + 1)
      (Point.map (s2c_branchInsertion Z n a) x) 0)) ⊔
        IsLocalRing.maximalIdeal ((g3_power Z (n + 1)).left.presheaf.stalk
          (Point.map (s2c_branchInsertion Z n a) x).underlying) ^ N := by
  let q := s2c_branchInsertion Z n a
  let z := Point.map q x
  let Rt := (g3_power Z (n + 1)).left.presheaf.stalk z.underlying
  let Rs := (g3_power Z n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ Rt := (HodgeLean.Foundations.Curves.stalkC z.underlying).toAlgebra
  letI : Algebra ℂ Rs := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let F : Rt →ₐ[ℂ] Rs :=
    { toRingHom := (q.left.stalkMap x.underlying).hom
      commutes' := fun c => s2e_stalkMap_complex_scalars (g3_power Z n)
        (g3_power Z (n + 1)) q x.underlying c }
  letI : IsLocalHom F.toRingHom :=
    inferInstanceAs (IsLocalHom (q.left.stalkMap x.underlying).hom)
  apply s2e_polynomial_erasure_ideal_control ℂ Rt Rs n N F
    (s2e_curvePowerParameter Z (n + 1) z) (s2e_curvePowerParameter Z n x)
    (IsLocalRing.maximalIdeal Rt ^ N) (IsLocalRing.maximalIdeal Rs ^ N)
    _ _ _ _ _ r hr
  · intro b hb
    have hm : Ideal.map F.toRingHom (IsLocalRing.maximalIdeal Rt ^ N) ≤
        IsLocalRing.maximalIdeal Rs ^ N := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le F.toRingHom) N
    exact hm (Ideal.mem_map_of_mem F.toRingHom hb)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact s2e_branchInsertion_curvePowerParameter_zero Z n a x
    · exact s2e_branchInsertion_curvePowerParameter_succ Z n a x j
  · exact s2e_curve_power_parameter_polynomial_representative Z (n + 1) z N hN
  · intro p hp
    exact (s2e_curve_power_parameter_polynomial_mem_power_iff Z (n + 1) z N hN p).mpr hp
  · intro p hp
    exact (s2e_curve_power_parameter_polynomial_mem_power_iff Z n x N hN p).mp hp

end HodgeLean.Foundations.Program
