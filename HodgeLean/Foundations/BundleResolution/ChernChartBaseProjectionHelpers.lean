import HodgeLean.Foundations.BundleResolution.ChernChartThomMultiplicationHelpers
import HodgeLean.Foundations.BundleThom.ContractibleFactorProjectionHelpers

/-! # The actual linear chart base projection on singular chains

The specified chart homeomorphism identifies this map with projection
along the contractible complex coordinate fibre.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Bundle TopologicalSpace HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_chartBaseProjection_quasiIso {B : Type} [TopologicalSpace B] {k : ℕ}
    (E : I1ComplexBundle B k)
    (e : Trivialization (Fin k → ℂ)
      (TotalSpace.proj : TotalSpace (Fin k → ℂ) E.fibre → B)) [e.IsLinear ℂ] :
    QuasiIso (singularChainComplexMap ℚ (i1_chartBaseProjection E e)) := by
  let F : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
    (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let et : (i1_chartPair k E.fibre e).fst ≅ TopCat.of (e.baseSet × (Fin k → ℂ)) :=
    TopCat.isoOfHomeo e.sourceHomeomorphBaseSetProd
  let pr : TopCat.of (e.baseSet × (Fin k → ℂ)) ⟶ TopCat.of e.baseSet :=
    TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  have h : i1_chartBaseProjection E e = et.hom ≫ pr := by
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    change v.val.proj = (e.sourceHomeomorphBaseSetProd v).1.val
    rw [e.sourceHomeomorphBaseSetProd_apply]
  haveI : QuasiIso (F.map pr) :=
    i1_productContractibleProjection_quasiIso e.baseSet (Fin k → ℂ)
  haveI : QuasiIso (F.map et.hom) := inferInstance
  change QuasiIso (F.map (i1_chartBaseProjection E e))
  rw [h, F.map_comp]
  infer_instance

end HodgeLean.Foundations.BundleResolution
