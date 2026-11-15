import HodgeLean.Foundations.Program.G32Native.FixedPeriodKernel
import HodgeLean.Foundations.Program.G32Native.ConormalEquationEvaluationContinuity
import HodgeLean.Foundations.Program.G32Native.ContinuousLinearRecovery
import HodgeLean.Foundations.Program.G32Native.ConormalEvaluationContinuity

/-! # Forward continuity of the original coherent period coefficient map -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle Filter Topology
open HodgeLean.Foundations.Curves.Picard.LineBundles
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Coherent original analytic lifts give a continuous coefficient map from
the actual dual conormal evaluation topology. -/
theorem coherentPeriodLifts_forward_continuous (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (hanalytic : ∀ x : ComplexPoint G.Q, AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hoverlap : ∀ x : ComplexPoint G.Q, ∃ V : Set (ComplexPoint G.W),
      IsOpen V ∧ Point.map G.ι x ∈ V ∧
      ∀ y : ComplexPoint G.Q, Point.map G.ι y ∈ V →
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
          =ᶠ[𝓝 (Point.map G.ι y)]
        (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w)))
    (hgeom : ∀ x : ComplexPoint G.Q,
      LinearMap.ker (canonicalAbelDifferential G F x) = LinearMap.range
        (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
          (localChart G.Q G.k x x)).toLinearMap ∧
      ∀ v, canonicalAbelDifferential G F x v (g32n_homogeneousLine G.k G.eQ x).rep = 0) :
    let E := fun x => (canonicalConormalFibreEquiv G x).trans
      (g32n_normalCoefficientEquiv G.W G.Q G.ι G.k G.eQ x
        (canonicalAbelDifferential G F x) (hgeom x).1.le (hgeom x).2)
    @Continuous
      (TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G))
      (TotalSpace (Fin G.k → ℂ)
        (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator))
      (normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k) (coefficientTotalTopology G)
      (fun z => ⟨z.proj, E z.proj z.2⟩) := by
  let N := TotalSpace (Fin G.k → ℂ) (canonicalNormalFibre G)
  letI : TopologicalSpace N := normalEvaluationTopology (Conormal.sheaf G.ι.left) G.k
  let E := fun x => (canonicalConormalFibreEquiv G x).trans
    (g32n_normalCoefficientEquiv G.W G.Q G.ι G.k G.eQ x
      (canonicalAbelDifferential G F x) (hgeom x).1.le (hgeom x).2)
  let H : N → (Fin (G.k + 1) → ℂ) := fun z => coefficientCoordinateEquiv G.k (E z.proj z.2).1
  have hb : Continuous (fun z : N => z.proj) :=
    continuous_normalEvaluation_proj (Conormal.sheaf G.ι.left) G.k
  have hH : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let x := z₀.proj
    let chartData := localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)
    let U := chartData.ambientCoordinateOpen
    have hU : IsAffineOpen U := by
      simpa only [U, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
        using chartData.isAffine
    have hxU : Point.map G.ι x ∈ Point.overOpen U := by
      simpa only [U, Point.overOpen, Set.mem_setOf_eq, LocalEtaleCoordinates.ambientCoordinateOpen,
        Scheme.Opens.ι_image_top] using chartData.mem
    obtain ⟨s, hs⟩ := exists_equationFixedDerivative_surjective G x U hU hxU
    let ep := localChart G.W (G.k + G.k) (Point.map G.ι x)
    have hxs : Point.map G.ι x ∈ ep.source := mem_localChart_source _ _ _
    have hnear : ∀ᶠ w in 𝓝 (Point.map G.ι x), AnalyticAt ℂ (F x) (ep w) :=
      (ep.continuousAt hxs).eventually (hanalytic x).eventually_analyticAt
    obtain ⟨V₁, hV₁, hV₁o, hxV₁⟩ := mem_nhds_iff.mp hnear
    obtain ⟨V₀, hV₀o, hxV₀, hV₀⟩ := hoverlap x
    let V := ((Point.overOpen U : Set (ComplexPoint G.W)) ∩ ep.source) ∩ (V₀ ∩ V₁)
    have hVo : IsOpen V := ((Point.isOpen_overOpen U).inter ep.open_source).inter (hV₀o.inter hV₁o)
    have hxV : Point.map G.ι x ∈ V := ⟨⟨hxU, hxs⟩, hxV₀, hxV₁⟩
    let S := {z : N | Point.map G.ι z.proj ∈ V}
    let b : S → ComplexPoint G.Q := fun z => z.1.proj
    let A : S → (Fin (G.k + G.k) → ℂ) →L[ℂ] (Fin G.k → ℂ) :=
      fun z => equationFixedDerivative G x U s (b z)
    let D : S → (Fin (G.k + G.k) → ℂ) →L[ℂ] (Fin (G.k + 1) → ℂ) :=
      fun z => fderiv ℂ (F x) (ep (Point.map G.ι (b z)))
    let v : S → (Fin (G.k + G.k) → ℂ) := fun z =>
      pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι (b z))
        (canonicalConormalFibreEquiv G (b z) z.1.2).val
    have hbS : Continuous b := hb.comp continuous_subtype_val
    have hw : Continuous (fun z : S => Point.map G.ι (b z)) := (Point.continuous_map G.ι).comp hbS
    have he : Continuous (fun z : S => ep (Point.map G.ι (b z))) :=
      ep.continuousOn.comp_continuous hw (fun z => z.2.1.2)
    have hA : Continuous A := (continuousOn_equationFixedDerivative G x U s).comp_continuous
      hbS (fun z => z.2.1)
    have hD : Continuous D := by
      apply continuous_iff_continuousAt.mpr
      intro z
      have hd : ContinuousAt (fderiv ℂ (F x)) (ep (Point.map G.ι (b z))) :=
        ((hV₁ z.2.2.2).contDiffAt (n := 1)).continuousAt_fderiv (by simp)
      have hh : ContinuousAt (fun u : S => fderiv ℂ (F x) (ep (Point.map G.ι (b u)))) z :=
        hd.comp (f := fun u : S => ep (Point.map G.ι (b u))) (x := z)
          (he.continuousAt (x := z))
      exact hh
    have hker : ∀ z, Function.Surjective (A z) →
        LinearMap.ker (A z).toLinearMap ≤ LinearMap.ker (D z).toLinearMap := by
      intro z hz
      exact fixedPeriodDerivative_ker_le G F x U s (b z) z.2.1.1 z.2.1.2
        (hV₁ z.2.2.2) (hanalytic (b z)) (hV₀ (b z) z.2.2.1) (hgeom (b z)).1 hz
    have hAv : Continuous (fun z => A z (v z)) := by
      have hh : (fun z : S => A z (v z)) =
          (fun z : S => equationPointCoordinates G U s (b z) z.2.1.1 z.1.2) := by
        funext z
        have h := DFunLike.congr_fun
          (equationFixedDerivative_comp_pointToFixed G x U s (b z) z.2.1.1 z.2.1.2)
          (canonicalConormalFibreEquiv G (b z) z.1.2).val
        change A z (v z) = equationPointCoordinates G U s (b z) z.2.1.1
          (canonicalConormalDerivative G (b z) (canonicalConormalFibreEquiv G (b z) z.1.2).val) at h
        rw [canonicalConormalFibreEquiv_pairing] at h
        exact h
      rw [hh]
      apply continuous_pi
      intro j
      let q : S → {z : N | Point.map G.ι z.proj ∈ Point.overOpen U} := fun z => ⟨z.1, z.2.1.1⟩
      have hq : Continuous q := continuous_subtype_val.subtype_mk _
      exact (continuous_normalEquationEvaluation G.ι G.k U (s j)).comp hq
    have hDv : (fun z : S => D z (v z)) = (fun z : S => H z.1) := by
      funext z
      have h := DFunLike.congr_fun (coefficientPointDerivative_fixedChart G F x (b z)
        z.2.1.2 (hV₁ z.2.2.2) (hanalytic (b z)) (hV₀ (b z) z.2.2.1))
        (canonicalConormalFibreEquiv G (b z) z.1.2).val
      change coefficientCoordinateEquiv G.k (canonicalAbelDifferential G F (b z)
        (canonicalConormalFibreEquiv G (b z) z.1.2).val) = D z (v z) at h
      apply h.symm.trans
      exact congrArg (coefficientCoordinateEquiv G.k)
        (g32n_normalCoefficientEquiv_apply G.W G.Q G.ι G.k G.eQ (b z)
          (canonicalAbelDifferential G F (b z)) (hgeom (b z)).1.le (hgeom (b z)).2
          (canonicalConormalFibreEquiv G (b z) z.1.2)).symm
    have hz₀ : z₀ ∈ ({z : N | Point.map G.ι z.proj ∈ V} : Set N) := hxV
    let zref : S := ⟨z₀, hz₀⟩
    have hlocal : ContinuousAt (fun z : S => H z.1) zref := by
      rw [← hDv]
      exact continuousAt_linear_factor_of_surjective_kernel A D v zref
        hA.continuousAt hD.continuousAt hs hker hAv.continuousAt
    have hSo : IsOpen {z : N | Point.map G.ι z.proj ∈ V} :=
      hVo.preimage ((Point.continuous_map G.ι).comp hb)
    exact ((continuousWithinAt_iff_continuousAt_domRestrict H hz₀).mpr hlocal).continuousAt
      (hSo.mem_nhds hz₀)
  apply (continuous_coefficientTotal_coordinates_iff G _).mpr
  refine ⟨hb, fun j => ?_⟩
  exact ((continuous_apply j).comp hH).congr
    (fun z => coefficientCoordinateEquiv_apply G.k (E z.proj z.2).1 j)

#print axioms coherentPeriodLifts_forward_continuous
end HodgeLean.Foundations.Program.G32Native
