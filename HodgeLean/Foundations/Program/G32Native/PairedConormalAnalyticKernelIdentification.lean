import HodgeLean.Foundations.Program.G32Native.PairedConormalActualLift
import HodgeLean.Foundations.Program.G32Native.PairedConormalDivisorSequence
import HodgeLean.Foundations.Program.G32Native.PairedConormalDivisorPresentation
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelRelationNonzero
import HodgeLean.Foundations.Program.G32Native.PairedConormalActualRelationMatrix
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelPullbackTransport
import HodgeLean.Foundations.Program.G32Native.PairedConormalActualPointMatrix
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeQuotient
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelMatrixFibre
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelPresentationObservations
import HodgeLean.Foundations.Program.G32Native.PairedConormalComponentChartPoint
import HodgeLean.Foundations.Program.G32Native.PairedConormalBundleAssembly
import HodgeLean.Foundations.Program.G32Native.PairedConormalModelLocallyFree
import HodgeLean.Foundations.Program.G32Native.PairedConormalModuleFibres
import HodgeLean.Foundations.BundleThom.AnalyticNormal
import HodgeLean.Foundations.BundleThom.ImmersionDefs
import HodgeLean.Foundations.BundleThom.LowRankThomExistenceHelpers
import HodgeLean.Foundations.BundleThom.NeighbourhoodDefs
import HodgeLean.Foundations.BundleThom.Proofs
import HodgeLean.Foundations.BundleThom.Thom
import HodgeLean.Foundations.BundleThom.ZeroRankThomUniquenessHelpers
/-! # Euler class of an elementary projective conormal modification -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.BundleThom
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The dual of the actual elementary quotient is the analytic evaluation-kernel bundle.
The homogeneous coefficient matrix comes from the supplied quotient; its
invertibility and fibre identifications are supplied by the retained constructions.
Global generator evaluations give continuous fibre maps; linear recovery in
bundle charts supplies inverse continuity.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.6;
Hartshorne, Algebraic Geometry, II.8, Euler sequence;
Fulton, Intersection Theory, §3.2, dual bundles. -/
theorem paired_conormal_analytic_kernel_identification_aux
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (V : Scheme) (j : Q.left ⟶ V) [IsClosedImmersion j]
    (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV]
    [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    (M : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules)
    (E : s2c_conormal j ≅ (Scheme.Modules.pullback eQ.hom.left).obj M)
    (f : (SheafOfModules.free
      (R := (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).ringCatSheaf) (Fin k) :
        (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).Modules) ⟶ M)
    (g : M ⟶ (Scheme.Modules.pushforward
      (s2c_subschemeι (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
        (s2e_hyperplaneIdeal k)).left).obj
      (SheafOfModules.unit (s2c_subscheme
        (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
        (s2e_hyperplaneIdeal k)).left.ringCatSheaf))
    (hfg : f ≫ g = 0) (hseq : (ShortComplex.mk f g hfg).ShortExact) :
    letI (x : ComplexPoint Q) := i1_normalFibreTopology j x
    letI := i1_normalTotalTopology j k
    ∃ D : ProjectiveKernelBundleComparison k (i1_normalFibre j),
      D.base = (EulerModel.normalComponentHomeomorph k eQ).symm := by
  classical
  let iH := (s2c_subschemeι
    (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (s2e_hyperplaneIdeal k)).left
  letI : IsClosedImmersion iH := by
    change IsClosedImmersion (s2e_hyperplaneIdeal k).subschemeι
    infer_instance
  let q := SheafOfModules.unitToPushforwardObjUnit iH.toRingCatSheafHom
  obtain ⟨l, hl⟩ := paired_conormal_actual_unit_lift Q k eQ V j sV hj M _ E
    f g hfg hseq q
  obtain ⟨b, eM, d, hd, hprojection, hfree, hdivisor⟩ :=
    elementary_divisor_presentation_of_lift (kernel.ι q) q (kernel.condition q)
      (paired_closedImmersion_ideal_shortExact iH) f g hfg hseq l hl
  have hrelation : ∀ x : ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))),
      (Scheme.Modules.pullback x.left).map
        (HodgeLean.Foundations.NormalPresentation.relation (kernel.ι q) b) ≠ 0 := by
    intro x
    let ι : Q ⟶ Over.mk sV := Over.homMk j hj
    letI : IsClosedImmersion ι.left := ‹IsClosedImmersion j›
    letI : SmoothOfRelativeDimension (k + k) (Over.mk sV).hom :=
      ‹SmoothOfRelativeDimension (k + k) sV›
    exact conormal_smooth_model_relation_pullback_ne_zero Q (Over.mk sV)
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) k ι
      ((Over.forget (Spec ↧ℂ)).mapIso eQ) M _ E _ eM x
  obtain ⟨linearRows, hmatrixUnit, hlinearRows⟩ :=
    conormal_actual_relation_matrix k hk b hrelation
  let π := HodgeLean.Foundations.NormalPresentation.projection (kernel.ι q) b ≫ eM.hom
  letI : Epi π := by
    dsimp only [π, HodgeLean.Foundations.NormalPresentation.projection]
    infer_instance
  have hπ : HodgeLean.Foundations.NormalPresentation.relation (kernel.ι q) b ≫ π = 0 := by
    dsimp only [π, HodgeLean.Foundations.NormalPresentation.projection]
    rw [← Category.assoc, cokernel.condition, zero_comp]
  let dP := s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))
  let N := (Scheme.Modules.pullback dP.hom).obj M
  let e₀ := (Over.forget (Spec ↧ℂ)).mapIso eQ
  let eN := e₀ ≪≫ dP.symm
  let EN := paired_module_modelIso_transport e₀ dP (s2c_conormal j) M E
  let W : Over (Spec ↧ℂ) := Over.mk sV
  let ι : Q ⟶ W := Over.homMk j hj
  letI : SmoothOfRelativeDimension (k + k) W.hom :=
    inferInstanceAs (SmoothOfRelativeDimension (k + k) sV)
  letI : IsClosedImmersion ι.left := inferInstanceAs (IsClosedImmersion j)
  letI : N.IsLocallyFree := paired_smooth_conormal_model_locallyFree Q W k k ι _ eN N EN
  have hframes := paired_smooth_conormal_model_frames Q W k k ι _ eN N EN
  let πN := conormalPresentationPullback dP.hom k M π
  letI : Epi πN := conormal_presentation_pullback_epi dP.hom k M π
  have hπN := conormal_native_quotient_relation_zero k b M π hπ
  let aN := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (conormalNativeHyperplaneIdeal ℂ k).subschemeι.toRingCatSheafHom)
  let bN := conormalNativeRetainedArrow k b
  let s : Fin (k + 1) →
      (SheafOfModules.unit Q.left.ringCatSheaf ⟶ Conormal.sheaf j) := fun r =>
    i1_moduleSectionPullback eQ.hom.left M
      (conormalPresentationGenerator _ k r ≫ π) ≫ E.inv
  let T := (conormalModelMatrixDualEquiv k (conormalRelationMatrix k linearRows)
    hmatrixUnit).toLinearMap.comp (EulerModel.normalHomogeneousCoordinates k).symm.toLinearMap
  have hφ : ∀ x : ComplexPoint Q, ∃ φ : i1_normalFibre j x ≃ₗ[ℂ]
      EulerModel.projectiveNormalKernel k ((EulerModel.normalComponentHomeomorph k eQ).symm x),
      ∀ ψ, (φ ψ).val = T (pairedNormalGlobalObservations j (k + 1) s x ψ) := by
    intro x
    obtain ⟨p, rfl⟩ := (EulerModel.normalComponentHomeomorph k eQ).surjective x
    induction p using Projectivization.ind with
    | h w hw =>
      let v := EulerModel.normalHomogeneousCoordinates k w
      have hv : v ≠ 0 := (EulerModel.normalHomogeneousCoordinates k).map_ne_zero_iff.mpr hw
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
      let z := conormalPolynomialChartComplexPoint v i hi
      let hz : z ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1 :=
        conormal_polynomial_chart_complex_point_mem v i hi
      have heq := conormal_component_chart_point k eQ w hw i hi
      have hdim := (paired_module_fibre_rank_of_fixedFrames N k hframes z).2
      let r := conormalPointRelationVector k aN bN z.left
        (conormalNativeIdealPointFrame k i z hz)
      have hcoords : EulerModel.normalHomogeneousCoordinates k r =
          (v i)⁻¹ • (conormalRelationMatrix k linearRows).mulVec v :=
        conormal_actual_point_relation_matrix k b linearRows hlinearRows v i hi
      have hr : conormalPresentationPointMap k πN z.left r = 0 :=
        conormal_point_relation_vector_in_kernel k aN bN πN hπN z.left
          (conormalNativeIdealPointFrame k i z hz)
      let K := pairedModelMatrixFibreEquiv j eQ.hom.left dP.hom M E k π
        (EulerModel.normalComponentHomeomorph k eQ (Projectivization.mk ℂ w hw))
        z.left heq hdim (conormalRelationMatrix k linearRows) hmatrixUnit v hv r
        (v i)⁻¹ (inv_ne_zero hi) hcoords hr
      have hbase : Projectivization.mk ℂ ((EulerModel.normalHomogeneousCoordinates k).symm v)
          ((EulerModel.normalHomogeneousCoordinates k).symm.map_ne_zero_iff.mpr hv) =
          (EulerModel.normalComponentHomeomorph k eQ).symm
            (EulerModel.normalComponentHomeomorph k eQ (Projectivization.mk ℂ w hw)) := by
        rw [Homeomorph.symm_apply_apply]
        simp only [v, LinearEquiv.symm_apply_apply]
      let C := LinearEquiv.ofEq _ _ (congrArg (EulerModel.projectiveNormalKernel k) hbase)
      refine ⟨K.trans C, ?_⟩
      intro ψ
      change (C (K ψ)).val = _
      simp only [C, LinearEquiv.coe_ofEq_apply]
      exact pairedModelMatrixFibreEquiv_val j eQ.hom.left dP.hom M E k π
        _ z.left heq hdim (conormalRelationMatrix k linearRows) hmatrixUnit v hv r
        (v i)⁻¹ (inv_ne_zero hi) hcoords hr ψ
  choose φ hφval using hφ
  letI (x : ComplexPoint Q) := i1_normalFibreTopology j x
  letI := i1_normalTotalTopology j k
  let normal := i1_analyticNormal j k sV hj
  letI := normal.fiberBundle
  letI := normal.vectorBundle
  have hc : Continuous (fun z : Bundle.TotalSpace (Fin k → ℂ) (i1_normalFibre j) =>
      (φ z.proj z.2).val) := by
    have h := T.continuous_of_finiteDimensional.comp
      (paired_normalGlobalObservations_continuous j k (k + 1) s)
    exact h.congr (fun z => (hφval z.proj z.2).symm)
  exact ⟨projectiveKernelBundleComparisonOfContinuousFibres k (i1_normalFibre j)
    (EulerModel.normalComponentHomeomorph k eQ).symm φ hc, rfl⟩

#print axioms paired_conormal_analytic_kernel_identification_aux
end HodgeLean.Foundations.Program.G32Native
