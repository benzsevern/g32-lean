import HodgeLean.Foundations.Program.SchoenTowerI2aAffineSpectrumCoefficients
import HodgeLean.Foundations.Program.SchoenTowerI2aPairStructureConstants

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The scalar-compatible coordinate map of an actual affine chart determines
exactly its retained structure morphism from the coefficient spectrum.
Source: Mathlib, `Scheme.isoSpec_hom_naturality` and
`toSpecΓ_SpecMap_ΓSpecIso_inv`. -/
theorem s2v_i2a_affine_coordinate_spectrum_structure
    (U : Over (Spec ↧ℂ)) [IsAffine U.left] (n : ℕ)
    (c : MvPolynomial (Fin n) ℂ →+* Γ(U.left, ⊤))
    (hc : c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom) :
    Spec.map (CommRingCat.ofHom (c.comp MvPolynomial.C)) = U.left.isoSpec.inv ≫ U.hom := by
  have hc' : CommRingCat.ofHom (c.comp MvPolynomial.C) =
      (Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop := congrArg CommRingCat.ofHom hc
  apply (cancel_epi U.left.isoSpec.hom).mp
  rw [hc', Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality]
  simp only [Category.assoc]
  rw [Scheme.isoSpec_hom, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end HodgeLean.Foundations.Program
