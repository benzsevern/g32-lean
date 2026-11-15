import HodgeLean.Foundations.TubularEuler.TubeDefs
import HodgeLean.Foundations.BundleResolution.ChernDefs

/-! # Complex bundle data for the retained analytic normal

The fibres, topology, and atlas are exactly the selected dual-conormal data.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Bundle
namespace HodgeLean.Foundations.TubularEuler
open BundleThom BundleResolution

def analyticNormalComplexBundle {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [IsClosedImmersion j] [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV] : I1ComplexBundle (ComplexPoint Q) k where
  fibre := i1_normalFibre j
  addGroup := inferInstance
  module := inferInstance
  fibreTopology := i1_normalFibreTopology j
  totalTopology := i1_normalTotalTopology j k
  fiberBundle := (i1_analyticNormal j k sV hj).fiberBundle
  vectorBundle := (i1_analyticNormal j k sV hj).vectorBundle

#print axioms analyticNormalComplexBundle

end HodgeLean.Foundations.TubularEuler
