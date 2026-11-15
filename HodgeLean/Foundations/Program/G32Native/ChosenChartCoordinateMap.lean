import HodgeLean.Foundations.Program.G32Native.AnalyticPointDerivation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

/-! # The original chosen chart coordinates on their actual ambient affine open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- The chosen chart's original coordinate map, transported to the actual
ambient coordinate open with its original complex scalar structure. -/
def chosenChartCoordinateMap (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W) :
    let D := localEtaleCoordinates W d p
    letI := overSpecAlgebra W D.ambientCoordinateOpen
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(W.left, D.ambientCoordinateOpen) := by
  let D := localEtaleCoordinates W d p
  letI := overSpecAlgebra W D.ambientCoordinateOpen
  let f := (D.neighborhood.ι.appIso ⊤).inv.hom.comp D.coordinateRingHomOnOpen
  have hC : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom f =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ W.hom.appLE ⊤ D.ambientCoordinateOpen le_top := by
    change (CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom D.coordinateRingHomOnOpen) ≫
      (D.neighborhood.ι.appIso ⊤).inv = _
    rw [D.C_comp_coordinateRingHomOnOpen, Scheme.Hom.comp_appTop]
    simp only [Category.assoc, Scheme.Opens.ι_appIso, Iso.refl_inv, Category.comp_id]
    rfl
  refine { toRingHom := f, commutes' := ?_ }
  intro c
  exact congrArg (fun q : CommRingCat.of ℂ ⟶ Γ(W.left, D.ambientCoordinateOpen) => q c) hC

/-- The coordinate map retains exactly the original ambient coordinate section. -/
theorem chosenChartCoordinateMap_apply (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W) (i : Fin d) :
    chosenChartCoordinateMap W d p (MvPolynomial.X i) =
      (localEtaleCoordinates W d p).ambientCoordinateSection i := rfl

/-- Transporting the original coordinate map to its actual ambient open
preserves its etale property. -/
theorem chosenChartCoordinateMap_etale (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W) :
    letI := overSpecAlgebra W (localEtaleCoordinates W d p).ambientCoordinateOpen
    (chosenChartCoordinateMap W d p).toRingHom.Etale := by
  let D := localEtaleCoordinates W d p
  exact RingHom.Etale.respectsIso.1 D.coordinateRingHomOnOpen
    (D.neighborhood.ι.appIso ⊤).symm.commRingCatIsoToRingEquiv D.coordinateRingHomOnOpen_etale

#print axioms chosenChartCoordinateMap_etale
#print axioms chosenChartCoordinateMap
#print axioms chosenChartCoordinateMap_apply
end HodgeLean.Foundations.Program.G32Native
