import HodgeLean.Foundations.Program.SchoenTowerL1bChartFactorization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Reduced total branches retain the weighted identity on any affine open missing the centre. -/
theorem s2v_l1b_weighted_transform_off_centre
    {X Y : Scheme} (f : X ⟶ Y) {J : Type*} [Fintype J]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : X.affineOpens) (hK : (K.comap f).ideal U = ⊤)
    (hred : ∀ j, (((D j).comap f).ideal U).IsRadical)
    (n : J → ℕ) (m : ℕ) :
    (∏ j, ((D j).comap f) ^ n j).ideal U =
      ((∏ j, (s2c_strictTransform f (D j) K) ^ n j) *
        (K.comap f) ^ m).ideal U := by
  simp only [s2v_l1b_ideal_sections_prod, Scheme.IdealSheafData.ideal_pow,
    Scheme.IdealSheafData.ideal_mul, Pi.pow_apply, Pi.mul_apply]
  have hD (j : J) : (s2c_strictTransform f (D j) K).ideal U =
      ((D j).comap f).ideal U := by
    rw [s2v_l1b_strictTransform_off_centre_chart f (D j) K U hK,
      (hred j).radical]
  simp only [hD, hK, ← Ideal.one_eq_top, one_pow, mul_one]

end HodgeLean.Foundations.Program
