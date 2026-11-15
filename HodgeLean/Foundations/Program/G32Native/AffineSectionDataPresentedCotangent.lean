import HodgeLean.Foundations.Program.G32Native.ModuleAffinePresentedFibre
import HodgeLean.Foundations.TubularEuler.AffineConormalCotangentSectionValueHelpers

/-! # Cotangent values at an explicitly supplied affine point -/
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

/-- Descended affine equations have their original cotangent tensor at a
specified spectrum point.
Source: `ModuleAffineSectionData.point_value_presented` and
`affineConormalFibreCotangentIso_section_value`. -/
theorem affineSectionData_presented_cotangent
    {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (U : Q.left.Opens) (hU : IsAffineOpen U)
    (R : CommRingCat.{0}) (φ : R ⟶ Q.left.presheaf.obj (.op U))
    (ψ : Q.left.presheaf.obj (.op U) ⟶ CommRingCat.of ℂ)
    (e : (Scheme.Modules.pullback hU.isoSpec.inv).obj
      ((Scheme.Modules.pullback U.ι).obj M) ≅ Conormal.sheaf (Spec.map φ))
    (u : RingHom.ker φ.hom)
    (s : ModuleAffineSectionData M U hU (Conormal.sheaf (Spec.map φ)) e
      (affineConormalSection R (Q.left.presheaf.obj (.op U)) φ u))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    (hp : ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom = Spec.map ψ) :
    letI : Algebra R ℂ := (φ ≫ ψ).hom.toAlgebra
    ((moduleAffinePresentedFibreIso M U hU (Conormal.sheaf (Spec.map φ)) e x hx
      (Spec.map ψ) hp) ≪≫
      affineConormalFibreCotangentIso R (Q.left.presheaf.obj (.op U)) φ ψ).hom
      (i1_moduleSectionValue M U s.localSection x hx) =
      (1 : ℂ) ⊗ₜ[R] (RingHom.ker φ.hom).toCotangent u := by
  dsimp only
  exact moduleIso_apply_eq_of_trans_values
    (moduleAffinePresentedFibreIso M U hU (Conormal.sheaf (Spec.map φ)) e x hx (Spec.map ψ) hp)
    (affineConormalFibreCotangentIso R (Q.left.presheaf.obj (.op U)) φ ψ)
    ((moduleAffinePresentedFibreIso M U hU (Conormal.sheaf (Spec.map φ)) e x hx
      (Spec.map ψ) hp) ≪≫
      affineConormalFibreCotangentIso R (Q.left.presheaf.obj (.op U)) φ ψ) rfl
    (i1_moduleSectionValue M U s.localSection x hx) _ _
    (s.point_value_presented x hx (Spec.map ψ) hp)
    (affineConormalFibreCotangentIso_section_value R (Q.left.presheaf.obj (.op U)) φ ψ u)

#print axioms affineSectionData_presented_cotangent
end HodgeLean.Foundations.TubularEuler
