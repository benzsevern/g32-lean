import HodgeLean.Foundations.Program.SchoenCycleCanonicalFamily

/-! # Local analytic graph descent
Analytic loci descend through finite fibres controlled by local sections.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
namespace HodgeLean.Foundations.Program

/-- Pullback of a local analytic locus only requires analyticity at the base point. -/
theorem s2e_analyticNear_preimage_at {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (φ : E → F) (x : E) (S : Set F)
    (hφ : AnalyticAt ℂ φ x)
    (hS : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear S (φ x)) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear (φ ⁻¹' S) x := by
  obtain ⟨U, hU, hx, κ, hκ, g, hg, he⟩ := hS
  have hmem : ∀ᶠ y in nhds x, φ y ∈ U := hφ.continuousAt.eventually (hU.mem_nhds hx)
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.mp (hmem.and hφ.eventually_analyticAt)
  refine ⟨W, hWo, hxW, κ, hκ, (fun i y => g i (φ y)), ?_, ?_⟩
  · intro i y hy
    exact (hg i (φ y) (hW y hy).1).comp (hW y hy).2
  · intro y hy
    exact he (φ y) (hW y hy).1


/-- Analytic graph incidence descends through an injective fibre with a continuous local section. -/
theorem s2e_analytic_graph_descent {n b k : ℕ}
    (A : Set ((Fin n → ℂ) × (Fin k → ℂ))) (y : Fin n → ℂ) (z : Fin k → ℂ)
    (hA : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A (y, z)) (hz : (y, z) ∈ A)
    (F : (Fin k → ℂ) → (Fin b → ℂ)) (hF : AnalyticAt ℂ F z)
    (hinj : Set.InjOn F {w | (y, w) ∈ A})
    (G : Set ((Fin n → ℂ) × (Fin b → ℂ)))
    (r : (Fin b → ℂ) → (Fin k → ℂ)) (hr : ContinuousAt r (F z)) (hrz : r (F z) = z)
    (himage : ∀ y' w, (y', w) ∈ A → (y', F w) ∈ G)
    (hsection : ∀ᶠ p in nhds (y, F z), p ∈ G → (p.1, r p.2) ∈ A ∧ F (r p.2) = p.2) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear G (y, F z) := by
  let I := {p : ((Fin n → ℂ) × (Fin b → ℂ)) × (Fin k → ℂ) |
    (p.1.1, p.2) ∈ A ∧ F p.2 = p.1.2}
  have hI : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear I ((y, F z), z) :=
    s2e_analytic_incidence_evaluation_graph A y z hA F hF (F z)
  have hfin : Set.Finite {w : Fin k → ℂ | ((y, F z), w) ∈ I} := by
    apply Set.Subsingleton.finite
    intro u hu v hv
    exact hinj hu.1 hv.1 (hu.2.trans hv.2.symm)
  apply s2e_analytic_projection_of_local_section (ContinuousLinearEquiv.refl ℂ (Fin k → ℂ))
    I G (y, F z) z hI ⟨hz, rfl⟩ hfin (fun p => r p.2)
    (hr.comp_of_eq (f := fun p : (Fin n → ℂ) × (Fin b → ℂ) => p.2)
      continuous_snd.continuousAt rfl) hrz
  · intro p w hw
    change (p.1, w) ∈ A ∧ F w = p.2 at hw
    change (p.1, p.2) ∈ G
    rw [← hw.2]
    exact himage p.1 w hw.1
  · exact hsection


/-- Adding a locally analytic scalar level equation preserves local analyticity. -/
theorem s2e_analyticNear_inter_level {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : Set V) (x : V) (f : V → ℂ) (c : ℂ)
    (hA : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A x) (hf : AnalyticAt ℂ f x) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear {y | y ∈ A ∧ f y = c} x := by
  obtain ⟨U, hU, hxU, κ, hκ, g, hg, he⟩ := hA
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.mp hf.eventually_analyticAt
  letI : Finite κ := hκ
  refine ⟨U ∩ W, hU.inter hWo, ⟨hxU, hxW⟩, κ ⊕ Unit, inferInstance,
    Sum.elim g (fun _ y => f y - c), ?_, ?_⟩
  · intro j y hy
    cases j with
    | inl j => exact hg j y hy.1
    | inr j => exact (hW y hy.2).sub analyticAt_const
  · intro y hy
    constructor
    · rintro ⟨ha, hf⟩ j
      cases j with
      | inl j => exact (he y hy.1).mp ha j
      | inr j => exact sub_eq_zero.mpr hf
    · intro hh
      exact ⟨(he y hy.1).mpr (fun j => hh (Sum.inl j)), sub_eq_zero.mp (hh (Sum.inr ()))⟩


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint in
/-- Normalized affine graph incidence is analytic in the native affine scheme chart. -/
theorem s2e_affine_normalized_graph_chart_analytic (k d b : ℕ) (i : Fin k)
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)).hom]
    (z : ComplexPoint (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)))
    (y : Fin b → ℂ) (S : Set ((Fin b → ℂ) × (Fin k → ℂ)))
    (hS : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear S (y, affineSpaceEquiv (Fin k) z)) :
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : (Fin b → ℂ) × (Fin d → ℂ) |
        (p.1, affineSpaceEquiv (Fin k)
          ((localChart (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z).symm p.2)) ∈ S ∧
        affineSpaceEquiv (Fin k)
          ((localChart (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z).symm p.2) i = 1}
      (y, localChart (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z z) := by
  let C := localChart (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z
  let φ := fun p : (Fin b → ℂ) × (Fin d → ℂ) =>
    (p.1, affineSpaceEquiv (Fin k) (C.symm p.2))
  have hzC := mem_localChart_source (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z
  have hc := s2e_affine_coordinates_chart_analytic k d z (C z) (C.map_source hzC)
  have hφ : AnalyticAt ℂ φ (y, C z) :=
    analyticAt_fst.prod (hc.comp_of_eq analyticAt_snd rfl)
  have hφbase : φ (y, C z) = (y, affineSpaceEquiv (Fin k) z) := by
    dsimp [φ]
    rw [C.left_inv hzC]
  have hS' : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear S (φ (y, C z)) := by
    rw [hφbase]
    exact hS
  have hp := s2e_analyticNear_preimage_at φ (y, C z) S hφ hS'
  have hi : AnalyticAt ℂ (fun p : (Fin b → ℂ) × (Fin d → ℂ) =>
      affineSpaceEquiv (Fin k) (C.symm p.2) i) (y, C z) :=
    (analyticAt_pi_iff.mp hc i).comp_of_eq analyticAt_snd rfl
  exact s2e_analyticNear_inter_level (φ ⁻¹' S) (y, C z) _ 1 hp hi


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- Native projective chart coordinates are injective on the valid normalized affine chart domain. -/
theorem s2e_projective_chart_normalized_native_injective (n d e : ℕ) (i : Fin (n + 1))
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom]
    (z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ))) :
    let C := localChart (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) d z
    let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e
      (chartAffineComplexPointMap i z)
    Set.InjOn (fun v => D (chartAffineComplexPointMap i (C.symm v)))
      {v | v ∈ C.target ∧ chartAffineComplexPointMap i (C.symm v) ∈ D.source ∧
        affineSpaceEquiv (Fin (n + 1)) (C.symm v) i = 1} := by
  dsimp only
  intro u hu v hv h
  apply (localChart (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) d z).symm.injOn hu.1 hv.1
  apply s2e_projective_affineChart_normalized_injective i hu.2.2 hv.2.2
  exact (localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e
    (chartAffineComplexPointMap i z)).injOn hu.2.1 hv.2.1 h


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- The polynomial projective chart map is analytic in its retained native scheme charts. -/
theorem s2e_projective_chart_native_analytic (n d e : ℕ) (i : Fin (n + 1))
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom]
    (z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ))) :
    let C := localChart (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) d z
    let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e
      (chartAffineComplexPointMap i z)
    AnalyticAt ℂ (fun v => D (chartAffineComplexPointMap i (C.symm v))) (C z) := by
  let A := Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)
  let P := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))
  let f : A ⟶ P := Over.homMk (chartAffineToProjectiveSpace i) (chartAffineToProjectiveSpace_over i)
  let C := localChart A d z
  have hz := mem_localChart_source A d z
  apply analyticAt_localChart_symm_map A P f d e z (C.map_source hz)
  rw [C.left_inv hz]
  exact mem_localChart_source P e (Point.map f z)


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- Normalized graph incidence remains analytic after restricting to valid native chart domains. -/
theorem s2e_projective_normalized_graph_incidence_analytic (n d e b : ℕ) (i : Fin (n + 1))
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom]
    (z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)))
    (y : Fin b → ℂ) (S : Set ((Fin b → ℂ) × (Fin (n + 1) → ℂ)))
    (hS : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear S
      (y, affineSpaceEquiv (Fin (n + 1)) z)) :
    let C := localChart (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) d z
    let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e
      (chartAffineComplexPointMap i z)
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : (Fin b → ℂ) × (Fin d → ℂ) |
        ((p.1, affineSpaceEquiv (Fin (n + 1)) (C.symm p.2)) ∈ S ∧
          affineSpaceEquiv (Fin (n + 1)) (C.symm p.2) i = 1) ∧
        p.2 ∈ C.target ∧ chartAffineComplexPointMap i (C.symm p.2) ∈ D.source} (y, C z) := by
  let A := Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)
  let P := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))
  let C := localChart A d z
  let D := localChart P e (chartAffineComplexPointMap i z)
  have hz := mem_localChart_source A d z
  have hc : ContinuousAt (fun v => chartAffineComplexPointMap i (C.symm v)) (C z) :=
    (continuous_chartAffineComplexPointMap i).continuousAt.comp (C.continuousAt_symm (C.map_source hz))
  have hm : ∀ᶠ v in nhds (C z), chartAffineComplexPointMap i (C.symm v) ∈ D.source := by
    apply hc.eventually
    change D.source ∈ nhds (chartAffineComplexPointMap i (C.symm (C z)))
    rw [C.left_inv hz]
    exact D.open_source.mem_nhds (mem_localChart_source P e _)
  have hv0 : ∀ᶠ v in nhds (C z), v ∈ C.target := C.open_target.mem_nhds (C.map_source hz)
  have hv := hv0.and hm
  have hv' := (continuous_snd.tendsto (y, C z)).eventually hv
  apply (s2e_affine_normalized_graph_chart_analytic (n + 1) d b i z y S hS).congr
  filter_upwards [hv'] with p hp
  exact ⟨fun h => ⟨h, hp⟩, fun h => h.1⟩


/-- A continuous local section transports to valid native chart coordinates with its image constraint. -/
theorem s2e_native_chart_local_section {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {d e : ℕ} (C : OpenPartialHomeomorph X (Fin d → ℂ))
    (D : OpenPartialHomeomorph Y (Fin e → ℂ)) (f : X → Y) (s : Y → X) (p : Y)
    (hp : p ∈ D.source) (hs : ContinuousAt s p) (hC : s p ∈ C.source)
    (T : Set X) (hsection : ∀ᶠ q in nhds p, f (s q) = q ∧ s q ∈ T) :
    ∃ r : (Fin e → ℂ) → (Fin d → ℂ),
      ContinuousAt r (D p) ∧ r (D p) = C (s p) ∧
      ∀ᶠ w in nhds (D p), r w ∈ C.target ∧ f (C.symm (r w)) ∈ D.source ∧
        C.symm (r w) ∈ T ∧ D (f (C.symm (r w))) = w := by
  let r := fun w => C (s (D.symm w))
  have hd := D.continuousAt_symm (D.map_source hp)
  have hsd : ContinuousAt (fun w => s (D.symm w)) (D p) :=
    hs.comp_of_eq hd (D.left_inv hp)
  have hr : ContinuousAt r (D p) :=
    (C.continuousAt hC).comp_of_eq hsd (congrArg s (D.left_inv hp))
  have ht : Tendsto D.symm (nhds (D p)) (nhds p) := by
    simpa only [D.left_inv hp] using hd.tendsto
  have hc : ∀ᶠ w in nhds (D p), s (D.symm w) ∈ C.source := by
    apply hsd.eventually
    change C.source ∈ nhds (s (D.symm (D p)))
    rw [D.left_inv hp]
    exact C.open_source.mem_nhds hC
  have hw : ∀ᶠ w in nhds (D p), w ∈ D.target := D.open_target.mem_nhds (D.map_source hp)
  refine ⟨r, hr, by dsimp [r]; rw [D.left_inv hp], ?_⟩
  filter_upwards [hc, hw, ht.eventually hsection] with w hc hw hs
  refine ⟨C.map_source hc, ?_⟩
  change f (C.symm (C (s (D.symm w)))) ∈ D.source ∧
    C.symm (C (s (D.symm w))) ∈ T ∧ D (f (C.symm (C (s (D.symm w))))) = w
  rw [C.left_inv hc, hs.1]
  exact ⟨D.map_target hw, hs.2, D.right_inv hw⟩


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- Actual projective points have continuous normalized sections in valid native chart coordinates. -/
theorem s2e_projective_normalized_native_section (n d e : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom]
    (P : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    ∃ (i : Fin (n + 1))
      (z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ))),
      affineSpaceEquiv (Fin (n + 1)) z i = 1 ∧ chartAffineComplexPointMap i z = P ∧
      let C := localChart (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) d z
      let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e P
      ∃ r : (Fin e → ℂ) → (Fin d → ℂ),
        ContinuousAt r (D P) ∧ r (D P) = C z ∧
        ∀ᶠ w in nhds (D P), r w ∈ C.target ∧
          chartAffineComplexPointMap i (C.symm (r w)) ∈ D.source ∧
          affineSpaceEquiv (Fin (n + 1)) (C.symm (r w)) i = 1 ∧
          D (chartAffineComplexPointMap i (C.symm (r w))) = w := by
  obtain ⟨i, U, s, hU, hP, hs, he⟩ := s2e_projective_affineChart_local_section n P
  refine ⟨i, s P, (he P hP).1, (he P hP).2, ?_⟩
  apply s2e_native_chart_local_section _ _ (chartAffineComplexPointMap i) s P
    (mem_localChart_source _ e P) (hs.continuousAt (hU.mem_nhds hP))
    (mem_localChart_source _ d (s P)) {z | affineSpaceEquiv (Fin (n + 1)) z i = 1}
  filter_upwards [hU.mem_nhds hP] with Q hQ
  exact ⟨(he Q hQ).2, (he Q hQ).1⟩


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- Analytic affine pullback graphs descend to native projective source charts. -/
theorem s2e_projective_graph_descent (n d e b : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom]
    (f : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) → (Fin b → ℂ))
    (P : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))))
    (hgraph : ∀ (i : Fin (n + 1))
      (z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ))),
      affineSpaceEquiv (Fin (n + 1)) z i = 1 → chartAffineComplexPointMap i z = P →
      HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
        {p : (Fin b → ℂ) × (Fin (n + 1) → ℂ) |
          f (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (n + 1))).symm p.2)) = p.1}
        (f (chartAffineComplexPointMap i z), affineSpaceEquiv (Fin (n + 1)) z))
    :
    let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e P
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : (Fin b → ℂ) × (Fin e → ℂ) | f (D.symm p.2) = p.1} (f P, D P) := by
  obtain ⟨i, z, hzi, hzP, r, hr, hrz, hsec⟩ := s2e_projective_normalized_native_section n d e P
  let C := localChart (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) d z
  let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e P
  let S := {p : (Fin b → ℂ) × (Fin (n + 1) → ℂ) |
    f (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (n + 1))).symm p.2)) = p.1}
  let A := {p : (Fin b → ℂ) × (Fin d → ℂ) |
    ((p.1, affineSpaceEquiv (Fin (n + 1)) (C.symm p.2)) ∈ S ∧
      affineSpaceEquiv (Fin (n + 1)) (C.symm p.2) i = 1) ∧
    p.2 ∈ C.target ∧ chartAffineComplexPointMap i (C.symm p.2) ∈ D.source}
  let F := fun v => D (chartAffineComplexPointMap i (C.symm v))
  have hzC := mem_localChart_source (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) d z
  have hDP := mem_localChart_source (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e P
  have hS : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear S
      (f P, affineSpaceEquiv (Fin (n + 1)) z) := by
    simpa only [hzP] using hgraph i z hzi hzP
  have hA : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear A (f P, C z) := by
    simpa only [hzP] using s2e_projective_normalized_graph_incidence_analytic n d e b i z (f P) S hS
  have hAz : (f P, C z) ∈ A := by
    change (_ ∧ _) ∧ _ ∧ _
    simpa only [S, Set.mem_ofPred_eq, C.left_inv hzC, Equiv.symm_apply_apply, hzP] using
      (show (f P = f P ∧ affineSpaceEquiv (Fin (n + 1)) z i = 1) ∧
        C z ∈ C.target ∧ P ∈ D.source from ⟨⟨rfl, hzi⟩, C.map_source hzC, hDP⟩)
  have hF : AnalyticAt ℂ F (C z) := by
    simpa only [hzP] using s2e_projective_chart_native_analytic n d e i z
  have hFz : F (C z) = D P := by dsimp [F]; rw [C.left_inv hzC, hzP]
  have hinj : Set.InjOn F {w | (f P, w) ∈ A} := by
    have hh : Set.InjOn F {v | v ∈ C.target ∧
        chartAffineComplexPointMap i (C.symm v) ∈ D.source ∧
        affineSpaceEquiv (Fin (n + 1)) (C.symm v) i = 1} := by
      simpa only [hzP] using s2e_projective_chart_normalized_native_injective n d e i z
    intro u hu v hv h
    exact hh ⟨hu.2.1, hu.2.2, hu.1.2⟩ ⟨hv.2.1, hv.2.2, hv.1.2⟩ h
  have hr' : ContinuousAt r (F (C z)) := by rw [hFz]; exact hr
  have hrz' : r (F (C z)) = C z := by rw [hFz]; exact hrz
  change HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
    {p : (Fin b → ℂ) × (Fin e → ℂ) | f (D.symm p.2) = p.1} (f P, D P)
  rw [← hFz]
  apply s2e_analytic_graph_descent A (f P) (C z) hA hAz F hF hinj _ r hr' hrz'
  · intro y w hw
    change f (D.symm (F w)) = y
    dsimp only [F]
    rw [D.left_inv hw.2.2]
    have hh := hw.1.1
    simpa only [S, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using hh
  · have hs := (continuous_snd.tendsto (f P, D P)).eventually hsec
    rw [hFz]
    filter_upwards [hs] with p hp hG
    have heq : chartAffineComplexPointMap i (C.symm (r p.2)) = D.symm p.2 := by
      exact (D.left_inv hp.2.1).symm.trans (congrArg D.symm hp.2.2.2)
    refine ⟨⟨⟨?_, hp.2.2.1⟩, hp.1, hp.2.1⟩, hp.2.2.2⟩
    change f (chartAffineComplexPointMap i
      ((affineSpaceEquiv (Fin (n + 1))).symm
        (affineSpaceEquiv (Fin (n + 1)) (C.symm (r p.2))))) = p.1
    rw [Equiv.symm_apply_apply, heq]
    exact hG


open scoped BigOperators in
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint in
/-- Normalizing one affine coefficient preserves the analytic graph of the actual canonical family. -/
theorem s2e_canonicalFamily_updated_chart_graph_analytic
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N q : ℕ) [SmoothOfRelativeDimension q B.hom]
    (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    {m : ℕ} (b : Fin m → b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))
    (a : Fin m → ℂ) (hne : (∑ j, a j • b j) ≠ 0) (i : Fin m) (hai : a i = 1) :
    let Q := s2e_canonicalQuotientPoint Z B N γ hg (Projectivization.mk ℂ (∑ j, a j • b j) hne)
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : (Fin q → ℂ) × (Fin m → ℂ) |
        ∃ hn : (∑ j, (Function.update p.2 i 1) j • b j) ≠ 0,
          localChart B q Q (s2e_canonicalQuotientPoint Z B N γ hg
            (Projectivization.mk ℂ (∑ j, (Function.update p.2 i 1) j • b j) hn)) = p.1}
      (localChart B q Q Q, a) := by
  classical
  let Q := s2e_canonicalQuotientPoint Z B N γ hg (Projectivization.mk ℂ (∑ j, a j • b j) hne)
  let φ := fun p : (Fin q → ℂ) × (Fin m → ℂ) => (Function.update p.2 i 1 - a, p.1)
  have hu : Function.update a i 1 = a := by
    funext j
    by_cases h : j = i
    · subst j; simp [hai]
    · simp [h]
  have hupdate : AnalyticAt ℂ (fun p : (Fin q → ℂ) × (Fin m → ℂ) => Function.update p.2 i 1)
      (localChart B q Q Q, a) := by
    apply AnalyticAt.pi
    intro j
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : (Fin q → ℂ) × (Fin m → ℂ) => (1 : ℂ)) _)
    · simp only [Function.update_of_ne h]
      exact ((ContinuousLinearMap.proj j : (Fin m → ℂ) →L[ℂ] ℂ).analyticAt a).comp_of_eq
        analyticAt_snd rfl
  have hφ : AnalyticAt ℂ φ (localChart B q Q Q, a) :=
    (hupdate.sub analyticAt_const).prod analyticAt_fst
  have hφ0 : φ (localChart B q Q Q, a) = (0, localChart B q Q Q) := by simp [φ, hu]
  have hfam := s2e_canonicalFamily_chart_graph_analytic Z B N q γ hγ hg b a hne
  have hp := s2e_analyticNear_preimage_at φ (localChart B q Q Q, a) _ hφ
    (by rw [hφ0]; exact hfam)
  apply hp.congr
  apply Filter.Eventually.of_forall
  intro p
  have he : a + (Function.update p.2 i 1 - a) = Function.update p.2 i 1 := by abel
  change (∃ hn : (∑ j, (a + (Function.update p.2 i 1 - a)) j • b j) ≠ 0,
    localChart B q Q (s2e_canonicalQuotientPoint Z B N γ hg
      (Projectivization.mk ℂ (∑ j, (a + (Function.update p.2 i 1 - a)) j • b j) hn)) = p.1) ↔ _
  simp only [he, Set.mem_ofPred_eq, Q]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped BigOperators in
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- The actual canonical quotient map has a locally analytic graph in native projective source charts. -/
theorem s2e_canonicalProjective_chart_graph_analytic
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N n d e q : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom]
    [SmoothOfRelativeDimension q B.hom]
    (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = n + 1)
    (P : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
    let g := fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R)
    let Q := g P
    let D := localChart (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) e P
    HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {p : (Fin q → ℂ) × (Fin e → ℂ) | localChart B q Q (g (D.symm p.2)) = p.1}
      (localChart B q Q Q, D P) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) n hd
  let β := Module.finBasisOfFinrankEq ℂ V hd
  let g := fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R)
  let Q := g P
  let f := fun R => localChart B q Q (g R)
  apply s2e_projective_graph_descent n d e q f P
  intro i z hzi hzP
  let v := affineSpaceEquiv (Fin (n + 1)) z
  have hu : Function.update v i 1 = v := by
    funext j
    by_cases h : j = i
    · subst j; simpa only [Function.update_self] using hzi.symm
    · simp [h]
  obtain ⟨h0, he0⟩ := s2e_finiteDimensionalProjectivePointEquiv_symm_affineChart (V := V) n hd i v
  simp only [hu] at h0 he0
  have hzv : (affineSpaceEquiv (Fin (n + 1))).symm v = z :=
    (affineSpaceEquiv (Fin (n + 1))).symm_apply_apply z
  rw [hzv, hzP] at he0
  have hQ : s2e_canonicalQuotientPoint Z B N γ hg
      (Projectivization.mk ℂ (∑ j, v j • β j) h0) = Q := by
    change _ = s2e_canonicalQuotientPoint Z B N γ hg (ep.symm P)
    rw [he0]
  have hfam := s2e_canonicalFamily_updated_chart_graph_analytic Z B N q γ hγ hg
    (fun j => β j) v h0 i hzi
  dsimp only at hfam
  rw [hQ] at hfam
  rw [hzP]
  apply hfam.congr
  apply Filter.Eventually.of_forall
  intro p
  obtain ⟨hp, hep⟩ := s2e_finiteDimensionalProjectivePointEquiv_symm_affineChart (V := V) n hd i p.2
  constructor
  · rintro ⟨hn, hy⟩
    change localChart B q Q
      (s2e_canonicalQuotientPoint Z B N γ hg
        (ep.symm (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (n + 1))).symm p.2)))) = p.1
    rw [hep]
    exact hy
  · intro hy
    refine ⟨hp, ?_⟩
    change localChart B q Q
      (s2e_canonicalQuotientPoint Z B N γ hg
        (ep.symm (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (n + 1))).symm p.2)))) = p.1 at hy
    rw [hep] at hy
    exact hy


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped BigOperators in
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- The actual canonical quotient evaluation is continuous on its native projective source. -/
theorem s2e_canonicalProjective_continuous
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N n : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = n + 1) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
    Continuous (fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R)) := by
  classical
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) n hd
  let β := Module.finBasisOfFinrankEq ℂ V hd
  let g := fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R)
  apply continuous_iff_continuousAt.mpr
  intro P
  obtain ⟨i, U, r, hU, hP, hr, he⟩ := s2e_projectivePoint_local_normalized_section n P
  have hrep (Q) (hQ : Q ∈ U) : ∃ hn : (∑ j, r Q j • β j : V) ≠ 0,
      ep.symm Q = Projectivization.mk ℂ (∑ j, r Q j • β j : V) hn := by
    obtain ⟨hv, hvQ⟩ := (he Q hQ).2
    have hh := s2e_finiteDimensionalProjectivePointEquiv_symm_vector (V := V) n hd (r Q) hv
    rw [hvQ] at hh
    have hn : (∑ j, r Q j • β j : V) ≠ 0 := by
      simpa only [Module.Basis.equivFun_symm_apply] using β.equivFun.symm.map_ne_zero_iff.mpr hv
    exact ⟨hn, by simpa only [Module.Basis.equivFun_symm_apply] using hh⟩
  obtain ⟨hnP, hlineP⟩ := hrep P hP
  let f : (Fin (n + 1) → ℂ) → ComplexPoint B := fun v =>
    if hv : (∑ j, v j • β j : V) ≠ 0 then
      s2e_canonicalQuotientPoint Z B N γ hg (Projectivization.mk ℂ (∑ j, v j • β j : V) hv)
    else g P
  have hf : ContinuousAt f (r P) := by
    apply s2e_canonicalFamily_evaluation_continuousAt Z B N γ hγ hg (fun j => β j) (r P) hnP f
    filter_upwards [s2e_holomorphicFamily_eventually_ne_zero (fun j => β j) (r P) hnP] with v hv
    exact ⟨hv, dif_pos hv⟩
  apply (hf.comp (hr.continuousAt (hU.mem_nhds hP))).congr
  filter_upwards [hU.mem_nhds hP] with Q hQ
  obtain ⟨hn, hline⟩ := hrep Q hQ
  change f (r Q) = g Q
  dsimp only [f, g]
  rw [dif_pos hn, hline]


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace in
/-- The canonical quotient graph is closed in the actual product topology. -/
theorem s2e_canonicalProjective_graph_isClosed
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsProjective B.hom]
    (N n : ℕ) (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = n + 1) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
    IsClosed {p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) ×
      ComplexPoint B | s2e_canonicalQuotientPoint Z B N γ hg (ep.symm p.1) = p.2} := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  exact (s2e_canonicalProjective_continuous Z B N n γ hγ hg hd).isClosed_graph


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace in
/-- Canonical quotient incidence along scheme morphisms is a closed analytic subset. -/
theorem s2e_canonicalProjective_incidence_isClosedAnalytic
    (Z B T : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsProjective B.hom]
    (N n d e q t : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)).hom]
    [SmoothOfRelativeDimension e (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))).hom]
    [SmoothOfRelativeDimension q B.hom] [SmoothOfRelativeDimension t T.hom]
    (γ : HodgeLean.Adapters.g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = n + 1)
    (u : T ⟶ Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) (v : T ⟶ B) :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
    IsClosedAnalytic (Fin t → ℂ) {x : ComplexPoint T |
      s2e_canonicalQuotientPoint Z B N γ hg (ep.symm (Point.map u x)) = Point.map v x} := by
  classical
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) n hd
  let g := fun R => s2e_canonicalQuotientPoint Z B N γ hg (ep.symm R)
  have hgcont : Continuous g := s2e_canonicalProjective_continuous Z B N n γ hγ hg hd
  apply isClosedAnalytic_iff_finite.mpr
  refine ⟨isClosed_eq (hgcont.comp (Point.continuous_map u)) (Point.continuous_map v), ?_⟩
  intro x hx
  change g (Point.map u x) = Point.map v x at hx
  let C := localChart T t x
  let D := localChart PP e (Point.map u x)
  let E := localChart B q (g (Point.map u x))
  have hxC : x ∈ C.source := mem_localChart_source T t x
  have hxD : Point.map u x ∈ D.source := mem_localChart_source PP e _
  have hxE : g (Point.map u x) ∈ E.source := mem_localChart_source B q _
  have hu : AnalyticAt ℂ (fun w => D (Point.map u (C.symm w))) (C x) := by
    apply analyticAt_localChart_symm_map T PP u t e x (C.map_source hxC)
    rw [C.left_inv hxC]
    exact hxD
  have hv : AnalyticAt ℂ (fun w => E (Point.map v (C.symm w))) (C x) := by
    have hh := analyticAt_localChart_symm_map T B v t q x (C.map_source hxC)
      (by rw [C.left_inv hxC]; exact mem_localChart_source B q _)
    simpa only [E, hx] using hh
  let φ := fun w => (E (Point.map v (C.symm w)), D (Point.map u (C.symm w)))
  have hφ : AnalyticAt ℂ φ (C x) := hv.prod hu
  have hφx : φ (C x) = (E (g (Point.map u x)), D (Point.map u x)) := by
    simp only [φ, C.left_inv hxC, hx]
  have hgraph := s2e_canonicalProjective_chart_graph_analytic Z B N n d e q γ hγ hg hd (Point.map u x)
  have hp := s2e_analyticNear_preimage_at φ (C x) _ hφ (by rw [hφx]; exact hgraph)
  have hcu : ContinuousAt (fun w => Point.map u (C.symm w)) (C x) :=
    (Point.continuous_map u).continuousAt.comp (C.continuousAt_symm (C.map_source hxC))
  have hcv : ContinuousAt (fun w => Point.map v (C.symm w)) (C x) :=
    (Point.continuous_map v).continuousAt.comp (C.continuousAt_symm (C.map_source hxC))
  have hcg := hgcont.continuousAt.comp hcu
  have hDu : ∀ᶠ w in nhds (C x), Point.map u (C.symm w) ∈ D.source :=
    hcu.eventually (D.open_source.mem_nhds (by simpa only [C.left_inv hxC] using hxD))
  have hEg : ∀ᶠ w in nhds (C x), g (Point.map u (C.symm w)) ∈ E.source :=
    hcg.eventually (E.open_source.mem_nhds (by simpa only [Function.comp_apply, C.left_inv hxC] using hxE))
  have hEv : ∀ᶠ w in nhds (C x), Point.map v (C.symm w) ∈ E.source :=
    hcv.eventually (E.open_source.mem_nhds (by simpa only [C.left_inv hxC, hx] using hxE))
  have hlocal : HodgeLean.Foundations.Analytic.anf_IsAnalyticNear
      {w | g (Point.map u (C.symm w)) = Point.map v (C.symm w)} (C x) := by
    apply hp.congr
    filter_upwards [hDu, hEg, hEv] with w hdu heg hev
    change E (g (D.symm (D (Point.map u (C.symm w))))) = E (Point.map v (C.symm w)) ↔ _
    rw [D.left_inv hdu]
    exact ⟨fun h => E.injOn heg hev h, fun h => congrArg E h⟩
  obtain ⟨U, hU, hxU, κ, hκ, f, hf, heq⟩ := hlocal
  refine ⟨U ∩ C.target, hU.inter C.open_target, ⟨hxU, C.map_source hxC⟩,
    Set.inter_subset_right, κ, hκ, f, fun j => (hf j).mono Set.inter_subset_left, ?_⟩
  intro w hw
  exact heq w hw.1

end HodgeLean.Foundations.Program
