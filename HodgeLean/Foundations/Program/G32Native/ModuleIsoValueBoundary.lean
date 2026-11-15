import HodgeLean.Foundations.Program.G32Native.AffineSectionDataPresentedCotangent

/-! # A module-level boundary for affine fibre evaluation -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler

/-- Evaluate a module isomorphism with its source and target kept as modules.
Source: the underlying linear map of a `ModuleCat` isomorphism. -/
def moduleIsoValue {R : Type*} [Ring R] {P T : ModuleCat R}
    (e : P ≅ T) (x : P) : T := e.hom x

theorem moduleIsoValue_eq {R : Type*} [Ring R] {P T : ModuleCat R}
    (e : P ≅ T) (x : P) : moduleIsoValue e x = e.hom x := rfl

/-- Module evaluation agrees with the underlying linear equivalence.
Source: `ModuleCat.Iso.toLinearEquiv`. -/
theorem moduleIsoValue_toLinearEquiv {R : Type*} [Ring R] {P T : ModuleCat R}
    (e : P ≅ T) (x : P) : moduleIsoValue e x = e.toLinearEquiv x := rfl

/-- Descended equation values transported through the specified fibre chart,
with evaluation retained behind a module-level boundary.
Source: `affineSectionData_presented_cotangent`. -/
theorem affineSectionData_presented_cotangent_value
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
    moduleIsoValue
      (moduleAffinePresentedFibreIso M U hU (Conormal.sheaf (Spec.map φ)) e x hx
        (Spec.map ψ) hp ≪≫ affineConormalFibreCotangentIso R
          (Q.left.presheaf.obj (.op U)) φ ψ)
      (BundleResolution.i1_moduleSectionValue M U s.localSection x hx) =
      (1 : ℂ) ⊗ₜ[R] (RingHom.ker φ.hom).toCotangent u := by
  exact affineSectionData_presented_cotangent M U hU R φ ψ e u s x hx hp

#print axioms moduleIsoValue_toLinearEquiv
#print axioms moduleIsoValue_eq
#print axioms affineSectionData_presented_cotangent_value
end HodgeLean.Foundations.TubularEuler
