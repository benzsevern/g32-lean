import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.AffineChartPointFibre
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis
import Mathlib.Topology.LocalAtTarget

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual chart inclusion sends the ratio coordinate into the specified point fibre. -/
def affineChartSliceMap
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (X : Over (Spec ↧ℂ))
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R))
    (j : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
    (hj : ∀ a, Point.map p (Point.map j a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a) :
    ℂ → {x : ComplexPoint X // Point.map p x = (ComplexPoint.affineSpecEquiv R).symm φ} :=
  fun z =>
    let a := (affineChartPointFibreHomeomorph u v φ hu hv).symm z
    ⟨Point.map j a.val, (hj a.val).trans a.property⟩

/-- An actual open chart gives an open embedding of its ratio coordinate into the point fibre. -/
theorem isOpenEmbedding_affineChartSliceMap
    {R : Type} [CommRing R] [Algebra ℂ R]
    (u v : R) (φ : R →ₐ[ℂ] ℂ) (hu : φ u = 0) (hv : φ v = 0)
    (X : Over (Spec ↧ℂ))
    (p : X ⟶ Over.mk (ComplexPoint.affineSpecStructureMap R))
    (j : Over.mk (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v)) ⟶ X)
    [IsOpenImmersion j.left]
    (hj : ∀ a, Point.map p (Point.map j a) =
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a) :
    Topology.IsOpenEmbedding (affineChartSliceMap u v φ hu hv X p j hj) := by
  let q := (ComplexPoint.affineSpecEquiv R).symm φ
  let H := affineChartPointFibreHomeomorph u v φ hu hv
  let e : {a : ComplexPoint (Over.mk
      (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v))) //
      ComplexPoint.affineSpecComplexPointMap (regularPairCoefficientAlgHom u v) a = q} ≃ₜ
      {a : ComplexPoint (Over.mk
        (ComplexPoint.affineSpecStructureMap (RegularPairChart.ring u v))) //
        Point.map p (Point.map j a) = q} :=
    (Homeomorph.refl _).subtype (fun a => by rw [hj]; rfl)
  have hopen := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  exact (hopen.restrictPreimage {x : ComplexPoint X | Point.map p x = q}).comp
    (e.isOpenEmbedding.comp H.symm.isOpenEmbedding)

end AlgebraicGeometry.RamifiedNormalization.StageFour
