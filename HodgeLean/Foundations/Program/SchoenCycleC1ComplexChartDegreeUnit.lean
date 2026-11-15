import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual complex structure map constructs the inverse of every
positive covering degree in an affine chart ring. -/
theorem s2e_c1_complex_chart_degree_unit
    (X : Over (Spec ↧ℂ)) {A : Type} [CommRing A]
    (i : Spec (.of A) ⟶ X.left) (m : ℕ) (hm : 0 < m) :
    ∃ d : Aˣ, (d : A) = (m : A) := by
  let φ := (Spec.preimage (i ≫ X.hom)).hom
  have hc : IsUnit (m : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne')
  have ha := hc.map φ
  obtain ⟨d, hd⟩ := ha
  exact ⟨d, by simpa only [map_natCast] using hd⟩

end HodgeLean.Foundations.Program
