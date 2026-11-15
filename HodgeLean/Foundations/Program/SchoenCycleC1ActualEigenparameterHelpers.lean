import HodgeLean.Foundations.Program.SchoenCycleC1ActualStalkActionHomHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1LocalEigenparameterHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1ActualCurveEigenorderHelpers

/-! # Exact regular parameters for the actual finite curve stabilizer -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The actual finite group action fixing a smooth curve point has an
associated regular parameter on which every specified scheme pullback acts
by its constructed complex character. -/
theorem s2e_c1_actual_curve_finite_eigenparameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (p : ComplexPoint X) (hfixed : ∀ g, (a g).left p.underlying = p.underlying) :
    let R := X.left.presheaf.stalk p.underlying
    let t := s2e_native_curve_parameter X p
    ∃ χ : G →* ℂˣ, ∃ u : Rˣ, ∀ g : G,
      s2e_fixed_point_stalkPullback X.left (a g).left p.underlying (hfixed g)
        (t * (u : R)) =
      HodgeLean.Foundations.Curves.stalkC p.underlying (χ g : ℂ) * (t * (u : R)) := by
  let R := X.left.presheaf.stalk p.underlying
  let t := s2e_native_curve_parameter X p
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  haveI : IsDiscreteValuationRing R := s2e_smooth_curve_point_stalk_dvr X p
  obtain ⟨ρ, hρ⟩ := s2e_c1_actual_fixed_stalk_action_hom X G a ha1 hamul p.underlying hfixed
  obtain ⟨χ, u, hu, _⟩ := s2e_c1_dvr_finite_action_eigenparameter
    (s2e_complex_point_augmentation X p) ρ t (s2e_native_curve_parameter_irreducible X p)
  refine ⟨χ⁻¹, u, ?_⟩
  intro g
  have hh := hu g⁻¹
  change (ρ g⁻¹).toRingHom (t * (u : R)) = _ at hh
  rw [hρ] at hh
  change s2e_fixed_point_stalkPullback X.left (a (g⁻¹)⁻¹).left p.underlying _
    (t * (u : R)) = HodgeLean.Foundations.Curves.stalkC p.underlying
      (χ g⁻¹ : ℂ) * (t * (u : R)) at hh
  simpa only [inv_inv, map_inv, MonoidHom.inv_apply] using hh

end HodgeLean.Foundations.Program
