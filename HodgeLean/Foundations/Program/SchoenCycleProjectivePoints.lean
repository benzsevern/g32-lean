import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap

/-! # Projective coordinate recovery
Standard chart functions recover normalized homogeneous coordinates.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of a standard chart coordinate gives the homogeneous coordinate ratio. -/
theorem s2e_projective_chartCoordinate_eval {n : ℕ} (v : CoordinateSpace n)
    (i j : Fin (n + 1)) (hi : v i ≠ 0) :
    awayCoordinateEvaluation v i hi (chartCoordinate i j) = v j / v i := by
  unfold chartCoordinate
  rw [awayCoordinateEvaluation_mk]
  · simp [div_eq_mul_inv]
  · exact MvPolynomial.isHomogeneous_X _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal points in a common standard chart have equal coordinate ratios. -/
theorem s2e_projective_chart_eq_ratios {n : ℕ} (v w : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) (hj : w i ≠ 0)
    (h : chartIntegralProjAt v i hi = chartIntegralProjAt w i hj) :
    ∀ j, v j / v i = w j / w i := by
  unfold chartIntegralProjAt at h
  have he := (cancel_mono (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)).mp h
  have hh := Spec.map_injective he
  intro j
  have hx := congrArg (fun f => f.hom (chartCoordinate i j)) hh
  exact (s2e_projective_chartCoordinate_eval v i j hi).symm.trans
    (hx.trans (s2e_projective_chartCoordinate_eval w i j hj))

/-- Equality in a common projective chart recovers a nonzero scalar between vectors. -/
theorem s2e_projective_chart_eq_proportional {n : ℕ} (v w : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) (hj : w i ≠ 0)
    (h : chartIntegralProjAt v i hi = chartIntegralProjAt w i hj) :
    ∃ c : ℂ, c ≠ 0 ∧ v = c • w := by
  refine ⟨v i / w i, div_ne_zero hi hj, ?_⟩
  funext j
  have hr := s2e_projective_chart_eq_ratios v w i hi hj h j
  have hm := (div_eq_div_iff hi hj).mp hr
  change v j = (v i / w i) * w j
  apply (mul_right_cancel₀ hj)
  calc
    v j * w i = w j * v i := hm
    _ = ((v i / w i) * w j) * w i := by field_simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coordinate nonvanishing is detected by the actual projective basic open. -/
theorem s2e_projective_chart_mem_basicOpen {n : ℕ} (v : CoordinateSpace n)
    (i j : Fin (n + 1)) (hi : v i ≠ 0) :
    chartIntegralProjAt v i hi (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X j) ↔ v j ≠ 0 := by
  change (Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hi)))
    (IsLocalRing.closedPoint ℂ) ∈
    (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ _) zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X j) ↔ _
  rw [Proj.awayι_preimage_basicOpen (𝒜 := UniversalGrading n)
    (MvPolynomial.isHomogeneous_X _ i) zero_lt_one
    (MvPolynomial.isHomogeneous_X _ j) zero_lt_one]
  change awayCoordinateEvaluation v i hi
    (HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) j)) ∉
        (IsLocalRing.closedPoint ℂ).asIdeal ↔ _
  have he : HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) j) = chartCoordinate i j := by
    simp [HomogeneousLocalization.Away.isLocalizationElem, chartCoordinate]
  rw [he, s2e_projective_chartCoordinate_eval]
  simp [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, hi]

/-- Equality of integral projective points recovers nonzero scalar proportionality. -/
theorem s2e_projective_integral_eq_proportional {n : ℕ} (v w : CoordinateSpace n)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (h : chartIntegralProj v hv = chartIntegralProj w hw) :
    ∃ c : ℂ, c ≠ 0 ∧ v = c • w := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  obtain ⟨j, hj⟩ := exists_coordinate_ne_zero w hw
  have hh := h
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
    chartIntegralProj_eq_chartIntegralProjAt w hw j hj] at hh
  have hm : chartIntegralProjAt w j hj (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) := by
    rw [← hh]
    exact (s2e_projective_chart_mem_basicOpen v i i hi).mpr hi
  have hwi := (s2e_projective_chart_mem_basicOpen w j i hj).mp hm
  rw [chartIntegralProjAt_independent w j i hj hwi] at hh
  exact s2e_projective_chart_eq_proportional v w i hi hwi hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual projective scheme point determines its line of homogeneous coordinates. -/
theorem s2e_projectivizationToComplexPoint_injective {n : ℕ} :
    Function.Injective (projectivizationToComplexPoint (n := n)) := by
  intro x y h
  induction x using Projectivization.ind with
  | h v hv =>
    induction y using Projectivization.ind with
    | h w hw =>
      have he : vectorToProjectiveSpace v hv = vectorToProjectiveSpace w hw :=
        congrArg (fun z => z.left) h
      have hh := congrArg (fun f => f ≫ Limits.pullback.snd
        (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (UniversalGrading n)))) he
      rw [vectorToProjectiveSpace_toProj, vectorToProjectiveSpace_toProj] at hh
      obtain ⟨c, hc, heq⟩ := s2e_projective_integral_eq_proportional v w hv hw hh
      exact (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr ⟨c, heq.symm⟩

/-- Homogeneous coordinate lines and actual projective complex points are homeomorphic. -/
noncomputable def s2e_projectivePointHomeomorph (n : ℕ) :
    Projectivization ℂ (CoordinateSpace n) ≃ₜ
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  (Equiv.ofBijective projectivizationToComplexPoint
    ⟨s2e_projectivizationToComplexPoint_injective,
      surjective_projectivizationToComplexPoint⟩).toHomeomorphOfContinuousClosed
    continuous_projectivizationToComplexPoint
    continuous_projectivizationToComplexPoint.isClosedMap

/-- A linear coordinate equivalence induces an equivalence of actual projective lines. -/
noncomputable def s2e_projectiveLinearEquiv {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) : Projectivization ℂ V ≃ Projectivization ℂ W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv x := by
    induction x using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk]; congr 1; exact e.symm_apply_apply v
  right_inv x := by
    induction x using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk]; congr 1; exact e.apply_symm_apply v

/-- Finite-dimensional projective parameters have actual projective scheme points. -/
noncomputable def s2e_finiteDimensionalProjectivePointEquiv {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (hd : Module.finrank ℂ V = n + 1) :
    Projectivization ℂ V ≃
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  (s2e_projectiveLinearEquiv (Module.finBasisOfFinrankEq ℂ V hd).equivFun).trans
    (s2e_projectivePointHomeomorph n).toEquiv


/-- Coordinate normalization is invariant under nonzero scalar multiplication. -/
theorem s2e_coordinate_normalization_smul {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (t : ℂ) (ht : t ≠ 0) :
    ((t • v) i)⁻¹ • (t • v) = (v i)⁻¹ • v := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev]
  calc
    (v i)⁻¹ * t⁻¹ * (t * v j) = (v i)⁻¹ * ((t⁻¹ * t) * v j) := by ring
    _ = (v i)⁻¹ * v j := by rw [inv_mul_cancel₀ ht, one_mul]


/-- Normalize homogeneous coordinates by a specified coordinate, with zero value off that chart. -/
noncomputable def s2e_projectiveNormalizedVector {n : ℕ} (i : Fin (n + 1)) :
    Projectivization ℂ (CoordinateSpace n) → CoordinateSpace n :=
  Projectivization.lift (fun v => (v.val i)⁻¹ • v.val) (by
    intro v w t h
    have ht : t ≠ 0 := by
      intro ht
      apply v.property
      simpa only [ht, zero_smul] using h
    change (v.val i)⁻¹ • v.val = (w.val i)⁻¹ • w.val
    rw [h]
    exact s2e_coordinate_normalization_smul w.val i t ht)


/-- Normalization on a homogeneous representative is its coordinate ratio vector. -/
theorem s2e_projectiveNormalizedVector_mk {n : ℕ} (i : Fin (n + 1))
    (v : CoordinateSpace n) (hv : v ≠ 0) :
    s2e_projectiveNormalizedVector i (Projectivization.mk ℂ v hv) = (v i)⁻¹ • v := rfl


/-- The nonvanishing coordinate domain of normalized projective vectors is open. -/
theorem s2e_projectiveNormalizedVector_chart_open {n : ℕ} (i : Fin (n + 1)) :
    IsOpen {z : Projectivization ℂ (CoordinateSpace n) |
      s2e_projectiveNormalizedVector i z i ≠ 0} := by
  let q := Projectivization.mk' ℂ (V := CoordinateSpace n)
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  apply hq.isOpen_preimage.mp
  have he : q ⁻¹' {z | s2e_projectiveNormalizedVector i z i ≠ 0} =
      {v : {v : CoordinateSpace n // v ≠ 0} | v.val i ≠ 0} := by
    ext v
    change ((v.val i)⁻¹ • v.val) i ≠ 0 ↔ v.val i ≠ 0
    simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, inv_eq_zero, or_self]
  rw [he]
  exact isOpen_ne.preimage ((continuous_apply i).comp continuous_subtype_val)


/-- Normalized representatives vary continuously on their nonvanishing coordinate chart. -/
theorem s2e_projectiveNormalizedVector_continuousOn {n : ℕ} (i : Fin (n + 1)) :
    ContinuousOn (s2e_projectiveNormalizedVector i)
      {z : Projectivization ℂ (CoordinateSpace n) | s2e_projectiveNormalizedVector i z i ≠ 0} := by
  let S := {z : Projectivization ℂ (CoordinateSpace n) | s2e_projectiveNormalizedVector i z i ≠ 0}
  let q := Projectivization.mk' ℂ (V := CoordinateSpace n)
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  rw [continuousOn_iff_continuous_restrict]
  apply (hq.restrictPreimage_isOpen (s2e_projectiveNormalizedVector_chart_open i)).continuous_iff.mpr
  change Continuous (fun v : {v : {v : CoordinateSpace n // v ≠ 0} // q v ∈ S} =>
    (v.val.val i)⁻¹ • v.val.val)
  have hv : ∀ v : {v : {v : CoordinateSpace n // v ≠ 0} // q v ∈ S}, v.val.val i ≠ 0 := by
    intro v
    have hh := v.property
    change ((v.val.val i)⁻¹ • v.val.val) i ≠ 0 at hh
    simpa only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, inv_eq_zero, or_self] using hh
  exact (((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)).inv₀ hv).smul
    (continuous_subtype_val.comp continuous_subtype_val)


/-- A normalized vector in its coordinate chart recovers its projective line. -/
theorem s2e_projectiveNormalizedVector_reconstruct {n : ℕ} (i : Fin (n + 1))
    (z : Projectivization ℂ (CoordinateSpace n))
    (hz : s2e_projectiveNormalizedVector i z i ≠ 0) :
    s2e_projectiveNormalizedVector i z i = 1 ∧
      ∃ hv : s2e_projectiveNormalizedVector i z ≠ 0,
        Projectivization.mk ℂ (s2e_projectiveNormalizedVector i z) hv = z := by
  induction z using Projectivization.ind with
  | h v hv =>
    rw [s2e_projectiveNormalizedVector_mk] at hz ⊢
    have hi : v i ≠ 0 := by
      simpa only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, inv_eq_zero, or_self] using hz
    refine ⟨by simp [Pi.smul_apply, smul_eq_mul, hi], smul_ne_zero (inv_ne_zero hi) hv, ?_⟩
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ hv).mpr ⟨(v i)⁻¹, rfl⟩


/-- Actual projective complex points have continuous local normalized homogeneous representatives. -/
theorem s2e_projectivePoint_local_normalized_section (n : ℕ)
    (P : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    ∃ (i : Fin (n + 1)) (U : Set (ComplexPoint
        (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))))
      (r : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) → CoordinateSpace n),
      IsOpen U ∧ P ∈ U ∧ ContinuousOn r U ∧
      ∀ Q ∈ U, r Q i = 1 ∧ ∃ h : r Q ≠ 0, vectorToComplexPoint (r Q) h = Q := by
  let e := s2e_projectivePointHomeomorph n
  let z := e.symm P
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero z.rep z.rep_nonzero
  have hz : s2e_projectiveNormalizedVector i z i ≠ 0 := by
    rw [← Projectivization.mk_rep z, s2e_projectiveNormalizedVector_mk]
    simpa only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, inv_eq_zero, or_self] using hi
  let S := {z : Projectivization ℂ (CoordinateSpace n) | s2e_projectiveNormalizedVector i z i ≠ 0}
  let U := e.symm ⁻¹' S
  let r := s2e_projectiveNormalizedVector i ∘ e.symm
  refine ⟨i, U, r, (s2e_projectiveNormalizedVector_chart_open i).preimage e.symm.continuous,
    hz, ?_, ?_⟩
  · exact (s2e_projectiveNormalizedVector_continuousOn i).comp e.symm.continuous.continuousOn
      (fun _ h => h)
  · intro Q hQ
    obtain ⟨hqi, hv, hrec⟩ := s2e_projectiveNormalizedVector_reconstruct i (e.symm Q) hQ
    refine ⟨hqi, hv, ?_⟩
    change e (Projectivization.mk ℂ (s2e_projectiveNormalizedVector i (e.symm Q)) hv) = Q
    rw [hrec]
    exact e.apply_symm_apply Q


open AlgebraicGeometry.ComplexPoint in
/-- Actual affine coordinate functions are analytic in every native scheme chart. -/
theorem s2e_affine_coordinates_chart_analytic (k d : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)).hom]
    (z : ComplexPoint (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)))
    (w : Fin d → ℂ)
    (hw : w ∈ (localChart (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z).target) :
    AnalyticAt ℂ (fun v => affineSpaceEquiv (Fin k)
      ((localChart (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z).symm v)) w := by
  apply AnalyticAt.pi
  intro i
  have hh := analyticAt_localChart_symm_evaluate
    (Over.mk (complexAffineSpace (Fin k) ↘ Spec ↧ℂ)) d z hw ⊤
    (AffineSpace.coord (Spec ↧ℂ) i) (by exact trivial)
  simpa only [evaluate_top_eq_appTop, affineSpaceEquiv_apply] using hh


/-- A projective scheme point determines its normalized homogeneous representative uniquely. -/
theorem s2e_normalized_projective_coordinates_unique {n : ℕ} (i : Fin (n + 1))
    (v w : CoordinateSpace n) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvi : v i = 1) (hwi : w i = 1)
    (h : vectorToComplexPoint v hv = vectorToComplexPoint w hw) : v = w := by
  have hl := s2e_projectivizationToComplexPoint_injective
    (show projectivizationToComplexPoint (Projectivization.mk ℂ v hv) =
      projectivizationToComplexPoint (Projectivization.mk ℂ w hw) from h)
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mp hl
  have ht1 : t = 1 := by
    have hh := congrFun ht i
    simpa only [hvi, Pi.smul_apply, smul_eq_mul, hwi, mul_one] using hh
  simpa only [ht1, one_smul] using ht.symm


open AlgebraicGeometry.ComplexPoint in
/-- The polynomial projective chart map evaluates normalized affine coordinates as homogeneous coordinates. -/
theorem s2e_projective_affineChart_normalized_map {n : ℕ} (i : Fin (n + 1))
    (z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)))
    (hi : affineSpaceEquiv (Fin (n + 1)) z i = 1) :
    chartAffineComplexPointMap i z =
      vectorToComplexPoint (affineSpaceEquiv (Fin (n + 1)) z)
        (vector_ne_zero_of_coordinate _ i (hi.trans_ne one_ne_zero)) := by
  have hh := chartVectorToComplexPoint_eq i
    ⟨affineSpaceEquiv (Fin (n + 1)) z, hi.trans_ne one_ne_zero⟩
  simpa [vectorChartToAffinePoint, vectorChartRatios, hi] using hh


open AlgebraicGeometry.ComplexPoint in
/-- The polynomial projective chart map is injective on its normalized affine slice. -/
theorem s2e_projective_affineChart_normalized_injective {n : ℕ} (i : Fin (n + 1)) :
    Set.InjOn (chartAffineComplexPointMap i)
      {z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ)) |
        affineSpaceEquiv (Fin (n + 1)) z i = 1} := by
  intro z hz w hw h
  apply (affineSpaceEquiv (Fin (n + 1))).injective
  apply s2e_normalized_projective_coordinates_unique i _ _
    (vector_ne_zero_of_coordinate _ i (hz.trans_ne one_ne_zero))
    (vector_ne_zero_of_coordinate _ i (hw.trans_ne one_ne_zero)) hz hw
  rw [← s2e_projective_affineChart_normalized_map i z hz,
    ← s2e_projective_affineChart_normalized_map i w hw]
  exact h


open AlgebraicGeometry.ComplexPoint in
/-- The polynomial projective chart map has a continuous normalized local section on actual scheme points. -/
theorem s2e_projective_affineChart_local_section (n : ℕ)
    (P : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    ∃ (i : Fin (n + 1)) (U : Set (ComplexPoint
        (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))))
      (s : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) →
        ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ))),
      IsOpen U ∧ P ∈ U ∧ ContinuousOn s U ∧
      ∀ Q ∈ U, affineSpaceEquiv (Fin (n + 1)) (s Q) i = 1 ∧
        chartAffineComplexPointMap i (s Q) = Q := by
  obtain ⟨i, U, r, hU, hP, hr, he⟩ := s2e_projectivePoint_local_normalized_section n P
  let s := (affineSpaceEquiv (Fin (n + 1))).symm ∘ r
  refine ⟨i, U, s, hU, hP, ?_, ?_⟩
  · exact (affineSpaceHomeomorph (Fin (n + 1))).symm.continuous.comp_continuousOn hr
  · intro Q hQ
    obtain ⟨hi, hv, hp⟩ := he Q hQ
    have hsi : affineSpaceEquiv (Fin (n + 1)) (s Q) i = 1 := by
      simpa only [s, Function.comp_apply, Equiv.apply_symm_apply] using hi
    refine ⟨hsi, ?_⟩
    rw [s2e_projective_affineChart_normalized_map i (s Q) hsi]
    simpa only [s, Function.comp_apply, Equiv.apply_symm_apply] using hp


set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual affine point induces polynomial evaluation at its affine coordinates. -/
theorem s2e_affinePoint_comp_SpecIso (k : ℕ)
    (z : ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin k) ↘ Spec ↧ℂ))) :
    z.left ≫ (AffineSpace.SpecIso (Fin k) ↧ℂ).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (ComplexPoint.affineSpaceEquiv (Fin k) z))) := by
  rw [← Spec.map_preimage (z.left ≫ (AffineSpace.SpecIso (Fin k) ↧ℂ).hom)]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [specPreimage_apply]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [ComplexPoint.SpecIso_hom_appTop_C]
    change (Scheme.ΓSpecIso ↧ℂ).hom
      ((((ComplexPoint.complexAffineSpace (Fin k) ↘ Spec ↧ℂ).appTop ≫ z.left.appTop))
        ((Scheme.ΓSpecIso ↧ℂ).inv c)) = _
    rw [← Scheme.Hom.comp_appTop, show z.left ≫
      (ComplexPoint.complexAffineSpace (Fin k) ↘ Spec ↧ℂ) = 𝟙 _ from Over.w z]
    simp
  · intro j
    rw [specPreimage_apply]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [ComplexPoint.SpecIso_hom_appTop_X]
    simp [ComplexPoint.affineSpaceEquiv]


/-- The polynomial projective chart forgets the affine coordinate that it normalizes to one. -/
theorem s2e_chartAway_evaluation_update {n : ℕ} (i : Fin (n + 1)) (v : CoordinateSpace n) :
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) v).comp (chartAwayPolynomialHom i) =
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) (Function.update v i 1)).comp
        (chartAwayPolynomialHom i) := by
  apply awayRingHom_ext i
  · intro a
    exact DFunLike.congr_fun (degreeZero_ringHom_unique
      (((MvPolynomial.eval₂Hom (RingHom.id ℂ) v).comp (chartAwayPolynomialHom i)).comp
        (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
          (Submonoid.powers (MvPolynomial.X i))))
      (((MvPolynomial.eval₂Hom (RingHom.id ℂ) (Function.update v i 1)).comp
        (chartAwayPolynomialHom i)).comp
        (HomogeneousLocalization.fromZeroRingHom (UniversalGrading n)
          (Submonoid.powers (MvPolynomial.X i))))) a
  · intro j
    simp only [RingHom.comp_apply, chartAwayPolynomialHom_chartCoordinate]
    by_cases h : j = i
    · simp [h]
    · simp [h]


set_option backward.isDefEq.respectTransparency.types false in
open AlgebraicGeometry.ComplexPoint in
/-- Updating the normalized coordinate does not change the actual polynomial projective chart map. -/
theorem s2e_projective_affineChart_update {n : ℕ} (i : Fin (n + 1))
    (z : ComplexPoint (Over.mk (complexAffineSpace (Fin (n + 1)) ↘ Spec ↧ℂ))) :
    chartAffineComplexPointMap i z = chartAffineComplexPointMap i
      ((affineSpaceEquiv (Fin (n + 1))).symm
        (Function.update (affineSpaceEquiv (Fin (n + 1)) z) i 1)) := by
  let z' := (affineSpaceEquiv (Fin (n + 1))).symm
    (Function.update (affineSpaceEquiv (Fin (n + 1)) z) i 1)
  apply Over.OverMorphism.ext
  change z.left ≫ chartAffineToProjectiveSpace i = z'.left ≫ chartAffineToProjectiveSpace i
  apply Limits.pullback.hom_ext
  · change (z.left ≫ chartAffineToProjectiveSpace i) ≫
      ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ) =
      (z'.left ≫ chartAffineToProjectiveSpace i) ≫
        ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)
    simp only [Category.assoc, chartAffineToProjectiveSpace_over]
    exact (Over.w z).trans (Over.w z').symm
  · change (z.left ≫ chartAffineToProjectiveSpace i) ≫
      Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (UniversalGrading n))) =
      (z'.left ≫ chartAffineToProjectiveSpace i) ≫
        Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
          (Limits.terminal.from (Proj (UniversalGrading n)))
    simp only [Category.assoc, chartAffineToProjectiveSpace_toProj]
    unfold chartAffineToProj
    simp only [← Category.assoc, s2e_affinePoint_comp_SpecIso, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    change (MvPolynomial.eval₂Hom (RingHom.id ℂ) (affineSpaceEquiv (Fin (n + 1)) z)).comp
      (chartAwayPolynomialHom i) =
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) (affineSpaceEquiv (Fin (n + 1)) z')).comp
        (chartAwayPolynomialHom i)
    simpa only [z', Equiv.apply_symm_apply] using
      s2e_chartAway_evaluation_update i (affineSpaceEquiv (Fin (n + 1)) z)


/-- The inverse projective-point equivalence recovers the line of the actual basis-coordinate vector. -/
theorem s2e_finiteDimensionalProjectivePointEquiv_symm_vector {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (hd : Module.finrank ℂ V = n + 1) (v : CoordinateSpace n) (hv : v ≠ 0) :
    (s2e_finiteDimensionalProjectivePointEquiv (V := V) n hd).symm (vectorToComplexPoint v hv) =
      Projectivization.mk ℂ ((Module.finBasisOfFinrankEq ℂ V hd).equivFun.symm v)
        ((Module.finBasisOfFinrankEq ℂ V hd).equivFun.symm.map_ne_zero_iff.mpr hv) := by
  apply (s2e_finiteDimensionalProjectivePointEquiv (V := V) n hd).injective
  rw [Equiv.apply_symm_apply]
  change vectorToComplexPoint v hv =
    vectorToComplexPoint
      ((Module.finBasisOfFinrankEq ℂ V hd).equivFun
        ((Module.finBasisOfFinrankEq ℂ V hd).equivFun.symm v)) _
  simp only [LinearEquiv.apply_symm_apply]


open AlgebraicGeometry.ComplexPoint in
/-- The polynomial projective chart sends an affine vector to its coordinate-updated homogeneous vector. -/
theorem s2e_projective_affineChart_vector {n : ℕ} (i : Fin (n + 1)) (v : CoordinateSpace n) :
    chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (n + 1))).symm v) =
      vectorToComplexPoint (Function.update v i 1)
        (vector_ne_zero_of_coordinate _ i (by simp)) := by
  rw [s2e_projective_affineChart_update]
  simpa only [Equiv.apply_symm_apply] using s2e_projective_affineChart_normalized_map i
    ((affineSpaceEquiv (Fin (n + 1))).symm (Function.update v i 1))
      (by rw [Equiv.apply_symm_apply]; simp)


open scoped BigOperators in
open AlgebraicGeometry.ComplexPoint in
/-- The inverse projective parameter map on an affine chart is the line of the normalized basis combination. -/
theorem s2e_finiteDimensionalProjectivePointEquiv_symm_affineChart {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (hd : Module.finrank ℂ V = n + 1) (i : Fin (n + 1)) (v : CoordinateSpace n) :
    let B := Module.finBasisOfFinrankEq ℂ V hd
    ∃ h : (∑ j, (Function.update v i 1) j • B j) ≠ 0,
      (s2e_finiteDimensionalProjectivePointEquiv (V := V) n hd).symm
        (chartAffineComplexPointMap i ((affineSpaceEquiv (Fin (n + 1))).symm v)) =
      Projectivization.mk ℂ (∑ j, (Function.update v i 1) j • B j) h := by
  let B := Module.finBasisOfFinrankEq ℂ V hd
  have hw : Function.update v i 1 ≠ 0 := vector_ne_zero_of_coordinate _ i (by simp)
  have hb := B.equivFun.symm.map_ne_zero_iff.mpr hw
  rw [B.equivFun_symm_apply] at hb
  refine ⟨hb, ?_⟩
  rw [s2e_projective_affineChart_vector]
  simpa only [Module.Basis.equivFun_symm_apply] using
    s2e_finiteDimensionalProjectivePointEquiv_symm_vector (V := V) n hd (Function.update v i 1) hw

end HodgeLean.Foundations.Program
