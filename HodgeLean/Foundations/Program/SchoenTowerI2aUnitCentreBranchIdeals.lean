import HodgeLean.Foundations.Program.SchoenTowerI2aUnitCentreStrictTransform
import HodgeLean.Foundations.Program.SchoenTowerI2aStrictOpenSquare

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every actual radical affine branch ideal is unchanged on an open retained
chart over a unit centre.
Source: Hartshorne, Algebraic Geometry, II.7, strict transforms. -/
theorem s2v_i2a_unit_centre_affine_strict_ideal
    {X Y U : Scheme.{0}} [IsAffine U]
    (b : X ⟶ Y) (s : U ⟶ X) [IsOpenImmersion s] (j : U ⟶ Y)
    (hs : s ≫ b = j) (D K : Y.IdealSheafData) (hK : K.comap j = ⊤)
    (I : Ideal Γ(U, ⊤)) (hD : (D.comap j).ideal ⟨⊤, isAffineOpen_top U⟩ = I)
    (hI : I.IsRadical) :
    ((s2c_strictTransform b D K).comap s).ideal ⟨⊤, isAffineOpen_top U⟩ = I := by
  rw [s2v_i2a_strict_transform_open_square b s j (𝟙 U) (by simpa using hs),
    hK, s2v_i2a_strict_transform_unit_centre, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.radical_ideal, hD, hI.radical]

end HodgeLean.Foundations.Program
