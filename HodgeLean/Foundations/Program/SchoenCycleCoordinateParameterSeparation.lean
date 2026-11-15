import HodgeLean.Foundations.Program.SchoenCycleFirstParameterSeparation
import HodgeLean.Foundations.Program.SchoenCycleCoordinateParameterPrime

/-! # Pairwise separation of actual coordinate parameter ideals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Distinct actual curve-power coordinate parameters do not divide one another.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_curvePowerParameter_not_dvd_of_ne
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z (n + 1)))
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ¬s2e_curvePowerParameter Z (n + 1) x i ∣
      s2e_curvePowerParameter Z (n + 1) x j := by
  classical
  let σ := Equiv.swap (0 : Fin (n + 1)) i
  let u := s2_permute Z (n + 1) σ
  let y := Point.map u x
  letI : IsIso u := s2e_step1_action_isIso (g3_power Z (n + 1))
    (Equiv.Perm (Fin (n + 1))) (s2_permute Z (n + 1))
    (s2e_step1_permute_one Z (n + 1)) (s2e_step1_permute_mul Z (n + 1)) σ
  let e := (asIso (u.left.stalkMap x.underlying)).commRingCatIsoToRingEquiv
  have he (k : Fin (n + 1)) : e (s2e_curvePowerParameter Z (n + 1) y k) =
      s2e_curvePowerParameter Z (n + 1) x (σ.symm k) :=
    s2e_curvePowerParameter_permute Z (n + 1) σ x k
  have he0 : e (s2e_curvePowerParameter Z (n + 1) y 0) =
      s2e_curvePowerParameter Z (n + 1) x i := by
    simpa only [σ, Equiv.symm_swap, Equiv.swap_apply_left] using he 0
  have hej : e (s2e_curvePowerParameter Z (n + 1) y (σ j)) =
      s2e_curvePowerParameter Z (n + 1) x j := by
    simpa only [Equiv.symm_apply_apply] using he (σ j)
  have hk : σ j ≠ 0 := by
    intro h
    have hji : j = i := σ.injective (by simpa only [σ, Equiv.swap_apply_right] using h)
    exact hij hji.symm
  have hsep (k : Fin (n + 1)) : k ≠ 0 →
      ¬s2e_curvePowerParameter Z (n + 1) y 0 ∣ s2e_curvePowerParameter Z (n + 1) y k := by
    refine Fin.cases ?_ (fun l _ => s2e_first_curvePowerParameter_not_dvd_succ Z n y l) k
    intro h
    exact (h rfl).elim
  intro hd
  have hd' : e (s2e_curvePowerParameter Z (n + 1) y 0) ∣
      e (s2e_curvePowerParameter Z (n + 1) y (σ j)) := by
    rwa [he0, hej]
  obtain ⟨r, hr⟩ := hd'
  have hd'' : s2e_curvePowerParameter Z (n + 1) y 0 ∣
      s2e_curvePowerParameter Z (n + 1) y (σ j) := by
    refine ⟨e.symm r, e.injective ?_⟩
    simpa only [map_mul, e.apply_symm_apply] using hr
  exact hsep (σ j) hk hd''

end HodgeLean.Foundations.Program
