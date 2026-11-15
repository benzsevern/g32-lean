import HodgeLean.Foundations.Program.SchoenCycleInsertionParameterPrime
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric
import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

/-! # Primality of every actual curve-power coordinate parameter -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every coordinate parameter on an actual smooth curve power generates a prime ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_curvePowerParameter_ideal_prime
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z (n + 1))) (i : Fin (n + 1)) :
    (Ideal.span {s2e_curvePowerParameter Z (n + 1) x i}).IsPrime := by
  classical
  let σ := Equiv.swap (0 : Fin (n + 1)) i
  let u := s2_permute Z (n + 1) σ
  let y := Point.map u x
  letI : IsIso u := s2e_step1_action_isIso (g3_power Z (n + 1))
    (Equiv.Perm (Fin (n + 1))) (s2_permute Z (n + 1))
    (s2e_step1_permute_one Z (n + 1)) (s2e_step1_permute_mul Z (n + 1)) σ
  let e := (asIso (u.left.stalkMap x.underlying)).commRingCatIsoToRingEquiv
  letI := s2e_curvePowerParameter_first_ideal_prime Z n y
  have hp : (Ideal.map e (Ideal.span {s2e_curvePowerParameter Z (n + 1) y 0})).IsPrime :=
    Ideal.map_isPrime_of_equiv e
  have he : e (s2e_curvePowerParameter Z (n + 1) y 0) =
      s2e_curvePowerParameter Z (n + 1) x i := by
    change u.left.stalkMap x.underlying (s2e_curvePowerParameter Z (n + 1) y 0) = _
    rw [s2e_curvePowerParameter_permute Z (n + 1) σ x 0]
    simp only [σ, Equiv.symm_swap, Equiv.swap_apply_left]
  rw [Ideal.map_span, Set.image_singleton] at hp
  change (Ideal.span {e (s2e_curvePowerParameter Z (n + 1) y 0)}).IsPrime at hp
  rwa [he] at hp

end HodgeLean.Foundations.Program
