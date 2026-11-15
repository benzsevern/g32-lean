import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual inverse affine spectrum map pulls coefficients back by the
canonical inverse spectrum section isomorphism.
Source: Mathlib, `Scheme.toSpecΓ_appTop` and `Scheme.isoSpec`. -/
theorem s2v_i2a_affine_isoSpec_inv_coefficients
    (U : Scheme.{0}) [IsAffine U] :
    U.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(U, ⊤)).inv := by
  apply (cancel_mono U.isoSpec.hom.appTop).mp
  rw [← Scheme.Hom.comp_appTop, U.isoSpec.hom_inv_id]
  change 𝟙 Γ(U, ⊤) = (Scheme.ΓSpecIso Γ(U, ⊤)).inv ≫ U.toSpecΓ.appTop
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]

/-- Every specified ideal equation on an actual affine open chart passes to
its coefficient spectrum through the canonical section map.
Source: Hartshorne, Algebraic Geometry, II.5, affine ideal sheaves;
Mathlib, `Scheme.IdealSheafData.comap_comp`. -/
theorem s2v_i2a_affine_chart_spectrum_ideal
    {U X : Scheme.{0}} [IsAffine U] (u : U ⟶ X) (D : X.IdealSheafData)
    (I : Ideal Γ(U, ⊤)) (hI : (D.comap u).ideal ⟨⊤, isAffineOpen_top U⟩ = I) :
    (D.comap (U.isoSpec.inv ≫ u)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso Γ(U, ⊤)).inv.hom := by
  rw [Scheme.IdealSheafData.comap_comp, s2e_affine_comap_ideal, hI,
    s2v_i2a_affine_isoSpec_inv_coefficients]

end HodgeLean.Foundations.Program
