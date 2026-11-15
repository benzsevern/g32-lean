import HodgeLean.Foundations.TubularEuler.ModuleAffinePointFibreHelpers
import HodgeLean.Foundations.TubularEuler.ModuleAffineFibreChartIsoHelpers
import HodgeLean.Foundations.TubularEuler.ActualConormalAffineChartIsoHelpers
import HodgeLean.Foundations.TubularEuler.AffineModuleFibreHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalChartIsoHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2OpenConormalRestrictionHelpers

/-! # Affine ideal presentation of the retained conormal fibre

The immersion, actual complex point, affine restrictions, and original kernel ideal remain specified.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.Program HodgeLean.Foundations.BundleThom

def actualConormalFibreAffineCotangentIso
    {Q : Over (Spec ↧ℂ)} {W : Scheme} (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ V)) :
    let U := j ⁻¹ᵁ V
    let φ := j.app V
    let b := ComplexPoint.liftToOpen Q U x hx ≫ (hV.preimage j).isoSpec.hom
    letI : Algebra Γ(W, V) ℂ := (φ ≫ Spec.preimage b).hom.toAlgebra
    i1_conormalFibre j x ≅ ModuleCat.of ℂ (ℂ ⊗[Γ(W, V)] (RingHom.ker φ.hom).Cotangent) := by
  let U := j ⁻¹ᵁ V
  let hP := hV.preimage j
  let R := W.presheaf.obj (.op V)
  let S := Q.left.presheaf.obj (.op U)
  let φ : R ⟶ S := j.app V
  let b := ComplexPoint.liftToOpen Q U x hx ≫ hP.isoSpec.hom
  letI : Algebra Γ(W, V) ℂ := (φ ≫ Spec.preimage b).hom.toAlgebra
  exact moduleAffineFibreChartIso (Conormal.sheaf j) U hP
    (Conormal.sheaf (Spec.map φ)) (actualConormalAffineChartIso j V hV) x hx ≪≫
    affineConormalFibreCotangentIso R S φ (Spec.preimage b)

def actualNormalFibreAffineEquiv
    {Q : Over (Spec ↧ℂ)} {W : Scheme} (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ V)) :
    let U := j ⁻¹ᵁ V
    let φ := j.app V
    let b := ComplexPoint.liftToOpen Q U x hx ≫ (hV.preimage j).isoSpec.hom
    letI : Algebra Γ(W, V) ℂ := (φ ≫ Spec.preimage b).hom.toAlgebra
    Module.Dual ℂ (ℂ ⊗[Γ(W, V)] (RingHom.ker φ.hom).Cotangent) ≃ₗ[ℂ] i1_normalFibre j x :=
  (actualConormalFibreAffineCotangentIso j V hV x hx).toLinearEquiv.dualMap

theorem actualNormalFibreAffineEquiv_apply
    {Q : Over (Spec ↧ℂ)} {W : Scheme} (j : Q.left ⟶ W) [IsClosedImmersion j]
    (V : W.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ V)) :
    let U := j ⁻¹ᵁ V
    let φ := j.app V
    let b := ComplexPoint.liftToOpen Q U x hx ≫ (hV.preimage j).isoSpec.hom
    letI : Algebra Γ(W, V) ℂ := (φ ≫ Spec.preimage b).hom.toAlgebra
    ∀ (n : Module.Dual ℂ (ℂ ⊗[Γ(W, V)] (RingHom.ker φ.hom).Cotangent))
      (u : i1_conormalFibre j x), actualNormalFibreAffineEquiv j V hV x hx n u =
        n ((actualConormalFibreAffineCotangentIso j V hV x hx).hom u) := by
  intros
  rfl

#print axioms actualNormalFibreAffineEquiv_apply

#print axioms actualConormalFibreAffineCotangentIso

end HodgeLean.Foundations.TubularEuler
