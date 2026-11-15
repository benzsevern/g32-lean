import HodgeLean.Foundations.Program.SchoenCycleSmoothPowerAdicCoordinates
import Mathlib.RingTheory.AdicCompletion.Noetherian

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual smooth curve-power stalk embeds in formal series, preserving
its complex scalars and its geometric parameters. -/
theorem s2v_l1b_rotation_curve_power_expansion
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    ∃ ι : R →+* MvPowerSeries (Fin n) ℂ,
      Function.Injective ι ∧
      (∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC x.underlying c) =
        MvPowerSeries.C c) ∧
      ∀ j, ι (s2e_curvePowerParameter X n x j) = MvPowerSeries.X j := by
  let R := (g3_power X n).left.presheaf.stalk x.underlying
  let J := IsLocalRing.maximalIdeal R
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : IsLocallyNoetherian (g3_power X n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power X n).hom
  obtain ⟨E, hE⟩ := s2e_smooth_curve_power_stalk_powerSeries_algCoordinates X n x
  let ι : R →+* MvPowerSeries (Fin n) ℂ :=
    E.symm.toRingHom.comp (algebraMap R (AdicCompletion J R))
  refine ⟨ι, E.symm.injective.comp (AdicCompletion.of_injective J R), ?_, ?_⟩
  · intro c
    have h := E.symm.commutes c
    change E.symm (AdicCompletion.of J R
      (HodgeLean.Foundations.Curves.stalkC x.underlying c)) = MvPowerSeries.C c
    exact h
  · intro j
    have h := hE (MvPolynomial.X j)
    simp only [MvPolynomial.coe_X, MvPolynomial.aeval_X] at h
    change E.symm (AdicCompletion.of J R (s2e_curvePowerParameter X n x j)) = _
    rw [← h, E.symm_apply_apply]

end HodgeLean.Foundations.Program
