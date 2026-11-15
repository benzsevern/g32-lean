import HodgeLean.Foundations.Program.G32Native.CoefficientNormalChartNormalization
import HodgeLean.Foundations.Program.G32Native.LocalNormalizedThomPullback
import HodgeLean.Foundations.Program.G32Native.NormalizedThomPullback
import HodgeLean.Foundations.Program.G32Native.SupportedSelfRestriction
import HodgeLean.Foundations.Program.G32Native.NormalEulerModelLocalization

/-! # Complex-oriented Thom transport for the canonical coefficient map -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle
open HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.BundleThom
open HodgeLean.Foundations.Program.G32Native.EulerModel
namespace HodgeLean.Foundations.Program.G32Native

/-- Complex-oriented Thom naturality for the specified coefficient identification.
The coordinate equation fixes the map to U10's functional evaluated on the ordered basis.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, Thom class,
complex orientation and naturality under vector-bundle isomorphisms. -/
theorem canonical_coefficient_thom_transport_aux
    (G : CanonicalAbelGeometry) (D : CoefficientNormalIdentification G)
    [CompactSpace (ComplexPoint G.Q)] [T2Space (ComplexPoint G.Q)] :
    letI (x : ComplexPoint G.Q) := i1_normalFibreTopology G.ι.left x
    letI := i1_normalTotalTopology G.ι.left G.k
    let N := i1_analyticNormal G.ι.left G.k G.W.hom (Over.w G.ι)
    letI := N.fiberBundle
    letI := N.vectorBundle
    ∃ F : TopPair.ofSubset (X := i1_totalSpace G.k (i1_normalFibre G.ι.left))
        (i1_zeroSupport G.k (i1_normalFibre G.ι.left))ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (ProjectiveNormalTotalSpace G.k)) {w | w.1.2 = 0}ᶜ,
      (∀ x : ComplexPoint G.Q,
        TopPair.Hom.fst F (i1_zeroSection G.k (i1_normalFibre G.ι.left) x) =
          projectiveNormalZeroSection G.k
            ((normalProjectiveSchemeHomeomorph G.k).symm (Point.map G.eQ.hom x))) ∧
      (∀ z : TotalSpace (Fin G.k → ℂ) (i1_normalFibre G.ι.left),
        (TopPair.Hom.fst F z).val.1 =
          (normalProjectiveSchemeHomeomorph G.k).symm (Point.map G.eQ.hom z.proj) ∧
        (TopPair.Hom.fst F z).val.2 =
          ((D.fibre z.proj z.2).val (Pi.single 0 1),
            fun i => (D.fibre z.proj z.2).val (Pi.single i.succ 1))) ∧
      relativeCohomologyMap ℚ (2 * G.k) F (normalKernelGlobalThomClass G.k) =
        i1_bundleThom G.k (i1_normalFibre G.ι.left) := by
  letI (x : ComplexPoint G.Q) := i1_normalFibreTopology G.ι.left x
  letI := i1_normalTotalTopology G.ι.left G.k
  let N := i1_analyticNormal G.ι.left G.k G.W.hom (Over.w G.ι)
  letI := N.fiberBundle
  letI := N.vectorBundle
  refine ⟨coefficientNormalPairMap G D, ?_, ?_, ?_⟩
  · exact coefficientNormalPairMap_zeroSection G D
  · intro z
    exact ⟨coefficientNormalPairMap_base G D z, coefficientNormalPairMap_vector G D z⟩
  · apply bundleThom_pullback_of_local_chart_normalization G.k
      (i1_normalFibre G.ι.left) (coefficientNormalPairMap G D)
      (normalKernelGlobalThomClass G.k)
    intro e he b
    letI := he
    obtain ⟨j, hj⟩ := normalPermutationBase_chart_cover G.k
      (coefficientBaseHomeomorph G b.1)
    refine ⟨coefficientNormalChartBaseOpen G e j, hj, ?_⟩
    exact coefficientNormalChartComposite_normalization G D e j

#print axioms canonical_coefficient_thom_transport_aux
end HodgeLean.Foundations.Program.G32Native
