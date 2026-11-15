import HodgeLean.Foundations.Program.SchoenTowerHardt6RbAmbientAffineInterpolation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismCoordinates

/-! Actual affine maps evaluate every simplex barycentric combination by vertex values. -/
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_affine_simplex_evaluation {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (f : E →ᵃ[ℝ] ℝ) (w : stdSimplex ℝ ι) :
    f (∑ i, w.val i • v i) = ∑ i, w.val i * f (v i) := by
  have hh := Finset.map_affineCombination Finset.univ v w.val w.property.2 f
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ w.property.2,
    Function.comp_apply, smul_eq_mul] using hh

end HodgeLean.Foundations.Program
