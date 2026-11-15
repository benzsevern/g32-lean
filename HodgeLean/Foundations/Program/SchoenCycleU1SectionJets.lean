import HodgeLean.Foundations.Program.SchoenCycleU1SectionGerms
import HodgeLean.Foundations.Program.SchoenCycleU1SectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleU1AffineCharts

/-! # Actual section Taylor jets over the specified complex base -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The Taylor jet of regular sections along an analytic curve respects the actual
complex scalar structure on the section ring.
Source: Hartshorne, Algebraic Geometry, II.8; Serre, GAGA, section 2. -/
def s2e_u1_sectionJetAlong (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (c : ℂ → ComplexPoint X)
    (hU : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (c z)) 0) :
    letI := s2e_step1_sectionAlgebra X U
    Γ(X.left, U) →ₐ[ℂ] DualNumber ℂ := by
  letI := s2e_step1_sectionAlgebra X U
  refine ⟨s2e_u1_analyticGermJet.comp (s2e_u1_sectionGermAlong X U c hU hc), ?_⟩
  intro a
  have he : s2e_u1_sectionGermAlong X U c hU hc (algebraMap ℂ Γ(X.left, U) a) =
      s2e_u1_analyticGerm (fun _ : ℂ => a) analyticAt_const := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    rw [← s2e_u1_pointEvaluation_eq_evaluate X U (c z) hz]
    exact (s2e_step1_pointEvaluation X U (c z) _).commutes a
  change s2e_u1_analyticGermJet
    (s2e_u1_sectionGermAlong X U c hU hc (algebraMap ℂ Γ(X.left, U) a)) = _
  rw [he, s2e_u1_analyticGermJet_representative]
  simp only [deriv_const, TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.algebraMap_eq_inl]

/-- The first jet of an analytic curve is an actual dual-number-valued scheme
map into its affine neighbourhood, over the specified complex base.
Source: Hartshorne, Algebraic Geometry, II.8, tangent vectors. -/
def s2e_u1_curveJet (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hUa : IsAffineOpen U)
    (c : ℂ → ComplexPoint X)
    (hU : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (c z)) 0) :
    s2e_u1_specOver (DualNumber ℂ) ⟶ X := by
  letI := s2e_step1_sectionAlgebra X U
  exact s2e_u1_specOverMap (s2e_u1_sectionJetAlong X U c hU hc) ≫
    s2e_u1_fromSpecOver X U hUa

/-- Curve Taylor jets commute with the pullback of regular sections along an
actual complex scheme morphism.
Source: Hartshorne, Algebraic Geometry, II.8; Serre, GAGA, section 2. -/
theorem s2e_u1_sectionJetAlong_map
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (V : Y.left.Opens)
    (c : ℂ → ComplexPoint X)
    (hV : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ f.left ⁻¹ᵁ V)
    (hY : ∀ᶠ z in 𝓝 (0 : ℂ), (Point.map f (c z)).underlying ∈ V)
    (hc : ∀ s : Γ(X.left, f.left ⁻¹ᵁ V),
      AnalyticAt ℂ (fun z => Point.evaluate (f.left ⁻¹ᵁ V) s (c z)) 0)
    (hd : ∀ s : Γ(Y.left, V),
      AnalyticAt ℂ (fun z => Point.evaluate V s (Point.map f (c z))) 0) :
    letI := s2e_step1_sectionAlgebra X (f.left ⁻¹ᵁ V)
    letI := s2e_step1_sectionAlgebra Y V
    (s2e_u1_sectionJetAlong X (f.left ⁻¹ᵁ V) c hV hc).comp
      (s2e_u1_appLE_algHom X Y f V (f.left ⁻¹ᵁ V) le_rfl) =
        s2e_u1_sectionJetAlong Y V (fun z => Point.map f (c z)) hY hd := by
  letI := s2e_step1_sectionAlgebra X (f.left ⁻¹ᵁ V)
  letI := s2e_step1_sectionAlgebra Y V
  apply AlgHom.ext
  intro s
  change s2e_u1_analyticGermJet
      (s2e_u1_sectionGermAlong X (f.left ⁻¹ᵁ V) c hV hc ((f.left.appLE V (f.left ⁻¹ᵁ V) le_rfl).hom s)) =
    s2e_u1_analyticGermJet
      (s2e_u1_sectionGermAlong Y V (fun z => Point.map f (c z)) hY hd s)
  rw [← Scheme.Hom.app_eq_appLE]
  congr 1
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun z => (Point.evaluate_map f V s (c z)).symm)

/-- The actual dual-number-valued map of a mapped analytic curve equals its
curve jet followed by the scheme morphism.
Source: Hartshorne, Algebraic Geometry, II.8, functoriality of tangent vectors. -/
theorem s2e_u1_curveJet_map
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (V : Y.left.Opens)
    (hVa : IsAffineOpen V) (hWa : IsAffineOpen (f.left ⁻¹ᵁ V))
    (c : ℂ → ComplexPoint X)
    (hV : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ f.left ⁻¹ᵁ V)
    (hY : ∀ᶠ z in 𝓝 (0 : ℂ), (Point.map f (c z)).underlying ∈ V)
    (hc : ∀ s : Γ(X.left, f.left ⁻¹ᵁ V),
      AnalyticAt ℂ (fun z => Point.evaluate (f.left ⁻¹ᵁ V) s (c z)) 0)
    (hd : ∀ s : Γ(Y.left, V),
      AnalyticAt ℂ (fun z => Point.evaluate V s (Point.map f (c z))) 0) :
    s2e_u1_curveJet Y V hVa (fun z => Point.map f (c z)) hY hd =
      s2e_u1_curveJet X (f.left ⁻¹ᵁ V) hWa c hV hc ≫ f := by
  letI := s2e_step1_sectionAlgebra X (f.left ⁻¹ᵁ V)
  letI := s2e_step1_sectionAlgebra Y V
  have he := s2e_u1_sectionJetAlong_map X Y f V c hV hY hc hd
  ext1
  change Spec.map (CommRingCat.ofHom
      (s2e_u1_sectionJetAlong Y V (fun z => Point.map f (c z)) hY hd).toRingHom) ≫ hVa.fromSpec =
    (Spec.map (CommRingCat.ofHom
      (s2e_u1_sectionJetAlong X (f.left ⁻¹ᵁ V) c hV hc).toRingHom) ≫ hWa.fromSpec) ≫ f.left
  rw [Category.assoc, ← hVa.SpecMap_appLE_fromSpec f.left hWa le_rfl,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom he.symm

/-- Equality of actual scheme-valued curve jets forces equality on every regular
section Taylor jet of a common affine neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_curveJet_sections
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hUa : IsAffineOpen U)
    (c d : ℂ → ComplexPoint X)
    (hU : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ U)
    (hV : ∀ᶠ z in 𝓝 (0 : ℂ), (d z).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (c z)) 0)
    (hd : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (d z)) 0)
    (he : s2e_u1_curveJet X U hUa c hU hc = s2e_u1_curveJet X U hUa d hV hd) :
    letI := s2e_step1_sectionAlgebra X U
    s2e_u1_sectionJetAlong X U c hU hc = s2e_u1_sectionJetAlong X U d hV hd := by
  letI := s2e_step1_sectionAlgebra X U
  have hh := congrArg Over.Hom.left he
  change Spec.map (CommRingCat.ofHom (s2e_u1_sectionJetAlong X U c hU hc).toRingHom) ≫
      hUa.fromSpec =
    Spec.map (CommRingCat.ofHom (s2e_u1_sectionJetAlong X U d hV hd).toRingHom) ≫
      hUa.fromSpec at hh
  have hr := Spec.map_injective ((cancel_mono hUa.fromSpec).mp hh)
  apply AlgHom.ext
  intro s
  exact congrArg (fun g : CommRingCat.of Γ(X.left, U) ⟶ CommRingCat.of (DualNumber ℂ) =>
    g.hom s) hr

end HodgeLean.Foundations.Program
