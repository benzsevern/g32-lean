import HodgeLean.Foundations.TubularEuler.FibreNormalizationHelpers
import HodgeLean.Foundations.TubularEuler.TransportFibreHelpers
import HodgeLean.Foundations.TubularEuler.NormalFrameCoordinateHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2MultiplicityHelpers

/-! # The transported supplied class in selected transverse frames

Local multiplicity one and the complex transverse derivative fix the global Thom coefficient.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle Topology AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.TubularEuler
open BundleThom BundleResolution

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]
variable [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

theorem transportedClass_eq_normalThom_of_transverse_charts
    (t : SmoothNormalTube ι k v j hj)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c) :
    transportedClass ι k v j hj t.toNormalTube c = normalThom ι k v j hj := by
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  let E := analyticNormalComplexBundle j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  change transportedClass ι k v j hj t.toNormalTube c = i1_bundleThom k E.fibre
  apply bundleCoclass_eq_thom_of_selected_fibres E
  intro x
  let z := zeroSection (Fin k → ℂ) (i1_normalFibre j) x
  have hz : z ∈ t.source := t.contains_zero x
  obtain ⟨b, e, a, hb, he, ha, hxb, hze, hza, hs, hcz, hcf, hcg, D, hD⟩ := t.localCharts z hz
  letI := he
  have heBase : x ∈ e.baseSet := e.mem_source.mp hze
  have hcenter : t.ambient z ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) := by
    rw [t.ambient_map ⟨z, hz⟩]
    apply (t.support ⟨z, hz⟩).mpr
    rfl
  obtain ⟨O, hOa, hO, h0O, hnorm⟩ := hc k a hs (t.ambient z) hza hcenter ha
  have hrange : (t.ambient z).underlying ∈ Set.range ι.left := by
    rw [s2e_componentCycle_analytic_support] at hcenter
    exact hcenter
  rw [s2e_componentCycle_multiplicity ι (t.ambient z) hrange, one_smul] at hnorm
  have hDfibre : HasFDerivAt (fun w : Fin k → ℂ =>
      (a (t.ambient (⟨x, (e.continuousLinearEquivAt ℂ x heBase).symm w⟩ :
        TotalSpace (Fin k → ℂ) (i1_normalFibre j)))).2) D.toContinuousLinearMap 0 := by
    have hEq : (fun w : Fin k → ℂ =>
        (a (t.ambient (⟨x, (e.continuousLinearEquivAt ℂ x heBase).symm w⟩ :
          TotalSpace (Fin k → ℂ) (i1_normalFibre j)))).2) =
        (fun w : Fin k → ℂ => (tubeCoordinates ι k v j hj t.toNormalTube b e a (b x, w)).2) := by
      funext w
      change (a (t.ambient (⟨x, (e.continuousLinearEquivAt ℂ x heBase).symm w⟩ :
        TotalSpace (Fin k → ℂ) (i1_normalFibre j)))).2 =
        (a (t.ambient ((e.toOpenPartialHomeomorph.trans
          (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))).symm (b x, w)))).2
      rw [frame_product_inverse_fibre k (i1_normalFibre j) e b x heBase hxb w]
    rw [hEq]
    exact hD
  refine ⟨e, he, heBase, ?_⟩
  exact transportedClass_fibre_of_local_normalization ι k v j hj t.toNormalTube c
    e x heBase a hs O hO hOa h0O hnorm D hDfibre

#print axioms transportedClass_eq_normalThom_of_transverse_charts

end HodgeLean.Foundations.TubularEuler
