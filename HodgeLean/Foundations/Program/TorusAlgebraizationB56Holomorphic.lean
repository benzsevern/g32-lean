import HodgeLean.Foundations.Program.TorusAlgebraizationB56Analytic
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2
import HodgeLean.Foundations.Program.TorusAlgebraizationB56Dimension

/-! # Holomorphy of the theta map in the algebraic charts

A continuous map from a finite-dimensional complex vector space into the complex points of a
smooth scheme, along which every regular function is holomorphic, is holomorphic for the
algebraic charts: the chart coordinates are regular functions
(`localChart_apply_component_eq_evaluate`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology Filter
open scoped TensorProduct Manifold ContDiff

namespace HodgeLean.Foundations.Program

/-- Read in an algebraic chart, a map along which regular functions are holomorphic is analytic.
Source: HodgeConjecture `localChart_apply_component_eq_evaluate`; Osgood's lemma
(`spec_analyticOnNhd_of_differentiableOn`). -/
theorem b56_analyticAt_chart_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : E → ComplexPoint X) (hc : Continuous f)
    (hev : ∀ (W : X.left.Opens) (s : Γ(X.left, W)),
      DifferentiableOn ℂ (fun z ↦ Point.evaluate W s (f z)) (f ⁻¹' Point.overOpen W))
    (x : ComplexPoint X) (z₀ : E) (hz₀ : f z₀ ∈ (localChart X d x).source) :
    AnalyticAt ℂ (fun z ↦ localChart X d x (f z)) z₀ := by
  let D := localEtaleCoordinates X d x
  have hsrc : ∀ᶠ z in 𝓝 z₀, f z ∈ (localChart X d x).source :=
    hc.continuousAt ((localChart X d x).open_source.mem_nhds hz₀)
  have hopen : IsOpen (f ⁻¹' Point.overOpen D.ambientCoordinateOpen) :=
    (Point.isOpen_overOpen _).preimage hc
  have hzD : f z₀ ∈ Point.overOpen D.ambientCoordinateOpen := by
    have hmem := mem_coordinateNeighborhood_of_mem_localChart_source X d x (f z₀) hz₀
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using hmem
  have han : AnalyticAt ℂ (fun z i ↦ Point.evaluate D.ambientCoordinateOpen
      (D.ambientCoordinateSection i) (f z)) z₀ := by
    refine AnalyticAt.pi fun i ↦ ?_
    exact HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn
      hopen (hev _ _) z₀ hzD
  refine han.congr ?_
  filter_upwards [hsrc] with z hz
  funext i
  exact (localChart_apply_component_eq_evaluate X d x (f z) hz i).symm

/-- Holomorphy into complex points is tested on regular functions.
Source: HodgeConjecture `localChart_apply_component_eq_evaluate`; Osgood's lemma
(`spec_analyticOnNhd_of_differentiableOn`). -/
theorem b56_contMDiff_of_evaluate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : E → ComplexPoint X) (hc : Continuous f)
    (hev : ∀ (W : X.left.Opens) (s : Γ(X.left, W)),
      DifferentiableOn ℂ (fun z ↦ Point.evaluate W s (f z)) (f ⁻¹' Point.overOpen W)) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin d → ℂ) ω f := by
  intro z₀
  rw [contMDiffAt_iff_target]
  refine ⟨hc.continuousAt, ?_⟩
  rw [contMDiffAt_iff_contDiffAt]
  exact (b56_analyticAt_chart_comp X d f hc hev (f z₀) z₀
    (mem_localChart_source X d (f z₀))).contDiffAt

variable {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {hF : b2_IsWeightOne Λ F} {Q : LinearMap.BilinForm ℤ Λ}
  (hirr : ∀ z, (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
  (P : b5_V Λ F → ComplexPoint (b5_model Λ F hF Q))
  (hP : ∀ z, (P z).left =
    Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) (hirr z))
  (hbpf : ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0)
include hP hbpf

/-- The theta map is holomorphic for the algebraic charts.
Source: Mumford, *Abelian Varieties*, §3; Birkenhake–Lange, Theorem 4.5.1. -/
theorem b56_theta_contMDiff (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom] :
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin d → ℂ) ω P :=
  b56_contMDiff_of_evaluate _ d P (b56_continuous hirr P hP hbpf)
    (b56_differentiableOn_evaluate hirr P hP hbpf)

/-- The theta map read in an algebraic chart is analytic on the chart source. -/
theorem b56_theta_analyticAt_chart (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (x : ComplexPoint (b5_model Λ F hF Q)) (z₀ : b5_V Λ F)
    (hz₀ : P z₀ ∈ (localChart (b5_model Λ F hF Q) d x).source) :
    AnalyticAt ℂ (fun z ↦ localChart (b5_model Λ F hF Q) d x (P z)) z₀ :=
  b56_analyticAt_chart_comp _ d P (b56_continuous hirr P hP hbpf)
    (b56_differentiableOn_evaluate hirr P hP hbpf) x z₀ hz₀

/-- The differential of the theta map read in the algebraic chart at its value is injective.
Source: Mumford, *Abelian Varieties*, §3 (theta functions separate tangent vectors);
Birkenhake–Lange, Theorem 4.5.1. -/
theorem b56_fderiv_injective (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (htan : ∀ z v, v ≠ 0 → ∃ s ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z s = 0 ∧
      fderiv ℂ (fun w ↦ b5_eval Λ F hF Q w s) z v ≠ 0)
    (z₀ : b5_V Λ F) :
    Function.Injective
      (fderiv ℂ (fun z ↦ localChart (b5_model Λ F hF Q) d (P z₀) (P z)) z₀) := by
  set e := localChart (b5_model Λ F hF Q) d (P z₀) with he
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hv0
  obtain ⟨s, hs, hs0, hsd⟩ := htan z₀ v hv0
  obtain ⟨t, ht, htz₀⟩ := hbpf z₀
  have hs' : s ∈ b5_grade Λ F hF Q (1 • 1) := by simpa using hs
  let U : (b5_model Λ F hF Q).left.Opens := Proj.basicOpen (b5_grade Λ F hF Q) t
  let σ : Γ((b5_model Λ F hF Q).left, U) := Proj.awayToSection (b5_grade Λ F hF Q) t
    (HomogeneousLocalization.Away.mk _ ht 1 s hs')
  let q : b5_V Λ F → ℂ := fun z ↦ Point.evaluate U σ (P z)
  have hq (z : b5_V Λ F) (htz : b5_eval Λ F hF Q z t ≠ 0) :
      b5_eval Λ F hF Q z s = q z * b5_eval Λ F hF Q z t := by
    have h := b56_awayEval_mk Λ F hF Q z htz ht 1 s hs'
    simp only [q, σ, U]
    rw [b56_evaluate_awayToSection z (hirr z) (P z) (hP z) htz one_pos ht, ← h, pow_one,
      mul_comm]
  have hsrc := mem_localChart_source (b5_model Λ F hF Q) d (P z₀)
  have hEan := b56_theta_analyticAt_chart hirr P hP hbpf d (P z₀) z₀ hsrc
  have htarget : e (P z₀) ∈ e.target := e.map_source hsrc
  have hsymm : e.symm (e (P z₀)) = P z₀ := e.left_inv hsrc
  let h : (Fin d → ℂ) → ℂ := fun w ↦ Point.evaluate U σ (e.symm w)
  have hhan : AnalyticAt ℂ h (e (P z₀)) := by
    refine analyticAt_localChart_symm_evaluate (b5_model Λ F hF Q) d (P z₀) htarget U σ ?_
    rw [hsymm]
    exact b56_mem_basicOpen z₀ (hirr z₀) (P z₀) (hP z₀) htz₀ one_pos ht
  have hcont := b56_continuous hirr P hP hbpf
  have hqE : q =ᶠ[𝓝 z₀] h ∘ (fun z ↦ e (P z)) := by
    have hev : ∀ᶠ z in 𝓝 z₀, P z ∈ e.source :=
      hcont.continuousAt (e.open_source.mem_nhds hsrc)
    filter_upwards [hev] with z hz
    simp only [h, q, Function.comp_apply, e.left_inv hz]
  have hqd : HasFDerivAt q ((fderiv ℂ h (e (P z₀))).comp
      (fderiv ℂ (fun z ↦ e (P z)) z₀)) z₀ :=
    (hhan.differentiableAt.hasFDerivAt.comp z₀ hEan.differentiableAt.hasFDerivAt).congr_of_eventuallyEq
      hqE
  have htd := ((b56_differentiable_eval (hF := hF) (Q := Q) t) z₀).hasFDerivAt
  have hst : (fun w ↦ b5_eval Λ F hF Q w s) =ᶠ[𝓝 z₀]
      (fun w ↦ q w * b5_eval Λ F hF Q w t) := by
    have hev : ∀ᶠ w in 𝓝 z₀, b5_eval Λ F hF Q w t ≠ 0 :=
      (b56_continuous_eval t).continuousAt.eventually_ne htz₀
    filter_upwards [hev] with w hw
    exact hq w hw
  have hsd' := (hqd.mul htd).congr_of_eventuallyEq hst
  have hq0 : q z₀ = 0 := by
    have h0 := hq z₀ htz₀
    rw [hs0] at h0
    exact (mul_eq_zero.mp h0.symm).resolve_right htz₀
  rw [hsd'.fderiv] at hsd
  apply hsd
  simp [hq0, hv]

/-- The dimension of the theta Proj is at most the number of cover coordinates: the chart image
of the theta map is open.
Source: Birkenhake–Lange, Theorem 4.5.1; `b56_le_of_open_subset_image`. -/
theorem b56_dim_le (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (hPopen : IsOpenMap P) : d ≤ Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F) := by
  let e := localChart (b5_model Λ F hF Q) d (P 0)
  have hcont := b56_continuous hirr P hP hbpf
  let B : Set (b5_V Λ F) := P ⁻¹' e.source
  have hB : IsOpen B := e.open_source.preimage hcont
  have hdiff : DifferentiableOn ℂ (fun z ↦ e (P z)) B := fun z hz ↦
    (b56_theta_analyticAt_chart hirr P hP hbpf d (P 0) z hz).differentiableAt.differentiableWithinAt
  have hPB : IsOpen (P '' B) := hPopen B hB
  refine b56_le_of_open_subset_image (fun z ↦ e (P z)) B hdiff (e '' (P '' B))
    (e.isOpen_image_of_subset_source hPB (Set.image_preimage_subset P _))
    ⟨e (P 0), P 0, ⟨0, mem_localChart_source _ d (P 0), rfl⟩, rfl⟩ ?_
  rw [Set.image_image]

/-- Near each of its values the theta map has a holomorphic local section.
Source: inverse function theorem (Mathlib `ContDiffAt.to_localInverse`) with
`b56_fderiv_injective` and `b56_dim_le`. -/
theorem b56_local_section (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (htan : ∀ z v, v ≠ 0 → ∃ s ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z s = 0 ∧
      fderiv ℂ (fun w ↦ b5_eval Λ F hF Q w s) z v ≠ 0)
    (hPopen : IsOpenMap P) (z₀ : b5_V Λ F) :
    ∃ ψ : ComplexPoint (b5_model Λ F hF Q) → b5_V Λ F, ψ (P z₀) = z₀ ∧
      (∀ᶠ x in 𝓝 (P z₀), P (ψ x) = x) ∧
      ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, b5_V Λ F) ω ψ (P z₀) := by
  set e := localChart (b5_model Λ F hF Q) d (P z₀) with he
  have hcont := b56_continuous hirr P hP hbpf
  have hsrc : P z₀ ∈ e.source := mem_localChart_source _ d (P z₀)
  have hEan := b56_theta_analyticAt_chart hirr P hP hbpf d (P z₀) z₀ hsrc
  have hinj := b56_fderiv_injective hirr P hP hbpf d htan z₀
  have hdim := b56_dim_le hirr P hP hbpf d hPopen
  have hfin : Module.finrank ℂ (b5_V Λ F) = Module.finrank ℂ (Fin d → ℂ) := by
    refine le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) ?_
    simpa using hdim
  let L₀ : b5_V Λ F ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofBijective
    (fderiv ℂ (fun z ↦ e (P z)) z₀).toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩
  let L : b5_V Λ F ≃L[ℂ] (Fin d → ℂ) := L₀.toContinuousLinearEquiv
  have hE' : HasFDerivAt (fun z ↦ e (P z)) (L : b5_V Λ F →L[ℂ] (Fin d → ℂ)) z₀ := by
    have h := hEan.differentiableAt.hasFDerivAt
    convert h using 1
    exact ContinuousLinearMap.ext fun v ↦ rfl
  have hcd : ContDiffAt ℂ ω (fun z ↦ e (P z)) z₀ := hEan.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let φ := hcd.toOpenPartialHomeomorph (fun z ↦ e (P z)) hE' hn
  have hφ : ⇑φ = fun z ↦ e (P z) := rfl
  have hz₀φ : z₀ ∈ φ.source := hcd.mem_toOpenPartialHomeomorph_source hE' hn
  have htφ : e (P z₀) ∈ φ.target := hcd.image_mem_toOpenPartialHomeomorph_target hE' hn
  have hinvd : ContDiffAt ℂ ω φ.symm (e (P z₀)) := hcd.to_localInverse hE' hn
  let ψ : ComplexPoint (b5_model Λ F hF Q) → b5_V Λ F := fun x ↦ φ.symm (e x)
  have hψ0 : ψ (P z₀) = z₀ := by
    change φ.symm (φ z₀) = z₀
    exact φ.left_inv hz₀φ
  have hψc : ContinuousAt ψ (P z₀) :=
    hinvd.continuousAt.comp (e.continuousAt hsrc)
  have hev1 : ∀ᶠ x in 𝓝 (P z₀), x ∈ e.source := e.open_source.mem_nhds hsrc
  have hev2 : ∀ᶠ x in 𝓝 (P z₀), e x ∈ φ.target :=
    (e.continuousAt hsrc).preimage_mem_nhds (φ.open_target.mem_nhds htφ)
  have hev3 : ∀ᶠ x in 𝓝 (P z₀), P (ψ x) ∈ e.source := by
    have hPψ : ContinuousAt (fun x ↦ P (ψ x)) (P z₀) := hcont.continuousAt.comp hψc
    have hmem : e.source ∈ 𝓝 (P (ψ (P z₀))) := by
      rw [hψ0]
      exact e.open_source.mem_nhds hsrc
    exact hPψ.preimage_mem_nhds hmem
  refine ⟨ψ, hψ0, ?_, ?_⟩
  · filter_upwards [hev1, hev2, hev3] with x hx1 hx2 hx3
    apply e.injOn hx3 hx1
    have h := φ.right_inv hx2
    rw [hφ] at h
    exact h
  · rw [contMDiffAt_iff]
    refine ⟨hψc, ?_⟩
    simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, OpenPartialHomeomorph.coe_toPartialEquiv,
      PartialEquiv.refl_coe, Function.id_comp,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm, modelWithCornersSelf_coe, Set.range_id]
    change ContDiffWithinAt ℂ ω (ψ ∘ (localChart (b5_model Λ F hF Q) d (P z₀)).symm) Set.univ
      (localChart (b5_model Λ F hF Q) d (P z₀) (P z₀))
    rw [contDiffWithinAt_univ, ← he]
    refine hinvd.congr_of_eventuallyEq ?_
    have htgt : e.target ∈ 𝓝 (e (P z₀)) := e.open_target.mem_nhds (e.map_source hsrc)
    filter_upwards [htgt] with w hw
    simp only [ψ, Function.comp_apply, e.right_inv hw]

end HodgeLean.Foundations.Program
