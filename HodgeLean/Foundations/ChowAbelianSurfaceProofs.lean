import HodgeLean.Foundations.ChowAbelianSurfaceDefs
import HodgeLean.Adapters.CycleClassDivisorPowers3
import Mathlib.AlgebraicGeometry.Pullbacks
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

/-! # Proof obligations for the E² Chow primitives -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set
open HodgeLean.Adapters HodgeLean.Foundations.Curves
namespace HodgeLean.Foundations

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev ChowEEGrading (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)

private abbrev ChowEEChartRing (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (ChowEEGrading n) (MvPolynomial.X i)

private abbrev ChowEEChartVars {n : ℕ} (i : Fin (n + 1)) :=
  {j : Fin (n + 1) // j ≠ i}

private abbrev ChowEEChartPoly (n : ℕ) (i : Fin (n + 1)) :=
  MvPolynomial (ChowEEChartVars i) (ULift.{0} ℤ)

private theorem chowEE_away_ext {R : Type} [CommRing R] (n : ℕ) (i : Fin (n + 1))
    (φ ψ : ChowEEChartRing n i →+* R)
    (hc : ∀ j, φ (ComplexProjectiveSpace.chartCoordinate i j) =
      ψ (ComplexProjectiveSpace.chartCoordinate i j)) : φ = ψ := by
  open HomogeneousLocalization MvPolynomial in
  have hb : φ.comp (fromZeroRingHom (ChowEEGrading n) (.powers (X i))) =
      ψ.comp (fromZeroRingHom (ChowEEGrading n) (.powers (X i))) := by
    let e : ChowEEGrading n 0 ≃+* ℤ :=
      (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift.{0} ℤ)).trans ULift.ringEquiv
    apply (RingHom.cancel_right (f := e.symm.toRingHom) e.symm.surjective).mp
    exact Subsingleton.elim _ _
  let : Algebra (ChowEEGrading n 0) R :=
    (φ.comp (HomogeneousLocalization.fromZeroRingHom
      (ChowEEGrading n) (.powers (MvPolynomial.X i)))).toAlgebra
  let φa : ChowEEChartRing n i →ₐ[ChowEEGrading n 0] R :=
    { φ with commutes' := fun _ ↦ rfl }
  let ψa : ChowEEChartRing n i →ₐ[ChowEEGrading n 0] R :=
    { ψ with commutes' := fun r ↦ (DFunLike.congr_fun hb r).symm }
  change φa.toRingHom = ψa.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AlgHom.ext_of_adjoin_eq_top
    (HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X (ULift.{0} ℤ) i)
      (Fin (n + 1)) (fun j ↦ MvPolynomial.X j)
      (ComplexProjectiveSpace.adjoin_coordinates_eq_top n)
      (fun _ ↦ (1 : ℕ)) (fun j ↦ MvPolynomial.isHomogeneous_X (ULift.{0} ℤ) j))
  rintro z ⟨a, ai, hai, _, rfl⟩
  have hai' : ∑ j, ai j = a := by simpa using hai
  rw [ComplexProjectiveSpace.chartGenerator_eq_prod i ai hai']
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change φ (ComplexProjectiveSpace.chartCoordinate i j ^ ai j) =
    ψ (ComplexProjectiveSpace.chartCoordinate i j ^ ai j)
  rw [map_pow, map_pow, hc]

private def chowEE_normalizedVar {n : ℕ} (i j : Fin (n + 1)) :
    ChowEEChartPoly n i :=
  if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

private def chowEE_normalizeIntegral (n : ℕ) (i : Fin (n + 1)) :
    ComplexProjectiveSpace.UniversalRing n →+* ChowEEChartPoly n i :=
  MvPolynomial.eval₂Hom MvPolynomial.C (chowEE_normalizedVar i)

private def chowEE_chartToPoly (n : ℕ) (i : Fin (n + 1)) :
    ChowEEChartRing n i →+* ChowEEChartPoly n i :=
  (Localization.awayLift (chowEE_normalizeIntegral n i) (MvPolynomial.X i)
    (by
      rw [show chowEE_normalizeIntegral n i (MvPolynomial.X i) = 1 by
        simp [chowEE_normalizeIntegral, chowEE_normalizedVar]]
      exact isUnit_one)).comp
      (algebraMap _ (Localization.Away (MvPolynomial.X i)))

private theorem chowEE_chartToPoly_coord (n : ℕ) (i j : Fin (n + 1)) :
    chowEE_chartToPoly n i (ComplexProjectiveSpace.chartCoordinate i j) =
      chowEE_normalizedVar i j := by
  have hu : IsUnit (chowEE_normalizeIntegral n i (MvPolynomial.X i)) := by
    rw [show chowEE_normalizeIntegral n i (MvPolynomial.X i) = 1 by
      simp [chowEE_normalizeIntegral, chowEE_normalizedVar]]
    exact isUnit_one
  change (Localization.awayLift (chowEE_normalizeIntegral n i) (MvPolynomial.X i) hu)
    (Localization.mk (MvPolynomial.X j) ⟨MvPolynomial.X i ^ 1, ⟨1, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (chowEE_normalizeIntegral n i) (MvPolynomial.X i)
    (MvPolynomial.X j) 1]
  · simp [chowEE_normalizeIntegral]
  · simp [chowEE_normalizeIntegral, chowEE_normalizedVar]

private def chowEE_polyToChart (n : ℕ) (i : Fin (n + 1)) :
    ChowEEChartPoly n i →+* ChowEEChartRing n i :=
  MvPolynomial.eval₂Hom
    ((HomogeneousLocalization.fromZeroRingHom (ChowEEGrading n) (.powers (MvPolynomial.X i))).comp
      (ProjectiveSpace.degreeZeroEquiv (Fin (n + 1)) (ULift.{0} ℤ)).symm.toRingHom)
    (fun j ↦ ComplexProjectiveSpace.chartCoordinate i j.1)

private theorem chowEE_polyToChart_normalized (n : ℕ) (i j : Fin (n + 1)) :
    chowEE_polyToChart n i (chowEE_normalizedVar i j) =
      ComplexProjectiveSpace.chartCoordinate i j := by
  by_cases h : j = i
  · subst j
    simp [chowEE_normalizedVar]
  · simp [chowEE_normalizedVar, h, chowEE_polyToChart]

private theorem chowEE_chart_roundtrip (n : ℕ) (i : Fin (n + 1)) :
    (chowEE_polyToChart n i).comp (chowEE_chartToPoly n i) = RingHom.id _ := by
  apply chowEE_away_ext n i
  intro j
  simp only [RingHom.comp_apply, RingHom.id_apply, chowEE_chartToPoly_coord,
    chowEE_polyToChart_normalized]

private theorem chowEE_poly_roundtrip (n : ℕ) (i : Fin (n + 1)) :
    (chowEE_chartToPoly n i).comp (chowEE_polyToChart n i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro ⟨a⟩
    change ((chowEE_chartToPoly n i).comp (chowEE_polyToChart n i))
      (MvPolynomial.C (a : ULift.{0} ℤ)) =
        (RingHom.id (ChowEEChartPoly n i)) (MvPolynomial.C (a : ULift.{0} ℤ))
    simp only [map_intCast]
  · intro j
    simp [chowEE_polyToChart, chowEE_chartToPoly_coord, chowEE_normalizedVar, j.2]

private def chowEE_chartEquiv (n : ℕ) (i : Fin (n + 1)) :
    ChowEEChartRing n i ≃+* ChowEEChartPoly n i where
  __ := chowEE_chartToPoly n i
  invFun := chowEE_polyToChart n i
  left_inv a := DFunLike.congr_fun (chowEE_chart_roundtrip n i) a
  right_inv a := DFunLike.congr_fun (chowEE_poly_roundtrip n i) a

private def chowEE_integralChart (n : ℕ) (i : Fin (n + 1)) :
    Spec (.of (ChowEEChartPoly n i)) ⟶ Proj (ChowEEGrading n) :=
  (Scheme.Spec.mapIso (chowEE_chartEquiv n i).toCommRingCatIso.op).hom ≫
    Proj.awayι (ChowEEGrading n) (MvPolynomial.X i)
      (by simpa using MvPolynomial.isHomogeneous_X (ULift.{0} ℤ) i) zero_lt_one

private instance chowEE_integralChart_open (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (chowEE_integralChart n i) := by
  unfold chowEE_integralChart
  infer_instance

private theorem chowEE_integralChart_range (n : ℕ) (i : Fin (n + 1)) :
    (chowEE_integralChart n i).opensRange =
      Proj.basicOpen (ChowEEGrading n) (MvPolynomial.X i) := by
  unfold chowEE_integralChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

private def chowEE_standardChart (n : ℕ) (i : Fin (n + 1)) :
    𝔸(ChowEEChartVars i; Spec ↧ℂ) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) :=
  Limits.pullback.map _ _ _ _ (𝟙 _) (chowEE_integralChart n i) (𝟙 _)
    (by simp) (by simp)

private instance chowEE_standardChart_open (n : ℕ) (i : Fin (n + 1)) :
    IsOpenImmersion (chowEE_standardChart n i) := by
  unfold chowEE_standardChart
  infer_instance

private theorem chowEE_standardChart_base (n : ℕ) (i : Fin (n + 1)) :
    chowEE_standardChart n i ≫ ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ) =
      (𝔸(ChowEEChartVars i; Spec ↧ℂ) ↘ Spec ↧ℂ) := by
  change chowEE_standardChart n i ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _
  simp [chowEE_standardChart]

private theorem chowEE_standardChart_integral (n : ℕ) (i : Fin (n + 1)) :
    chowEE_standardChart n i ≫ Limits.pullback.snd _ _ =
      AffineSpace.toSpecMvPoly (ChowEEChartVars i) (Spec ↧ℂ) ≫
        chowEE_integralChart n i := by
  simp [chowEE_standardChart, AffineSpace.toSpecMvPoly]

private theorem chowEE_standardChart_pullback (n : ℕ) (i : Fin (n + 1)) :
    IsPullback (chowEE_standardChart n i)
      (AffineSpace.toSpecMvPoly (ChowEEChartVars i) (Spec ↧ℂ))
      (Limits.pullback.snd _ _) (chowEE_integralChart n i) := by
  refine (IsPullback.paste_horiz_iff (.of_hasPullback _ _)
    (chowEE_standardChart_integral n i)).mp ?_
  simp only [Limits.terminal.comp_from]
  convert! (IsPullback.of_hasPullback _ _)
  exact chowEE_standardChart_base n i

private theorem chowEE_standardChart_range (n : ℕ) (i : Fin (n + 1)) :
    (chowEE_standardChart n i).opensRange =
      (Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj (ChowEEGrading n)))) ⁻¹ᵁ
          Proj.basicOpen (ChowEEGrading n) (MvPolynomial.X i) := by
  rw [← chowEE_integralChart_range n i]
  apply TopologicalSpace.Opens.ext
  change Set.range (chowEE_standardChart n i) = _
  rw [← (chowEE_standardChart_pullback n i).isoPullback_hom_fst]
  have hs : Set.range (chowEE_standardChart_pullback n i).isoPullback.hom = Set.univ :=
    Set.range_eq_univ.mpr
      (chowEE_standardChart_pullback n i).isoPullback.hom.homeomorph.surjective
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs, Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst _ _

private def chowEE_dehomogenize {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (ChowEEChartVars i) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j ↦
    if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩)

private def chowEE_chartVector {n : ℕ} (i : Fin (n + 1))
    (w : ChowEEChartVars i → ℂ) : Fin (n + 1) → ℂ :=
  fun j ↦ if h : j = i then 1 else w ⟨j, h⟩

private theorem chowEE_eval_dehomogenize {n : ℕ} (i : Fin (n + 1))
    (w : ChowEEChartVars i → ℂ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval w (chowEE_dehomogenize i P) =
      MvPolynomial.eval (chowEE_chartVector i w) P := by
  change ((MvPolynomial.eval₂Hom (RingHom.id ℂ) w).comp (chowEE_dehomogenize i)) P = _
  apply DFunLike.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chowEE_dehomogenize]
  · intro j
    by_cases h : j = i
    · subst j
      simp [chowEE_dehomogenize, chowEE_chartVector]
    · simp [chowEE_dehomogenize, chowEE_chartVector, h]

private lemma chowEE_eval_smul_of_isHomogeneous {n d : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℂ) (hP : P.IsHomogeneous d)
    (c : ℂ) (z : Fin (n + 1) → ℂ) :
    MvPolynomial.eval (c • z) P = c ^ d * MvPolynomial.eval z P := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hd : ∑ i, e i = d := by
    rw [← hP (MvPolynomial.mem_support_iff.mp he)]
    simp only [Finsupp.weight_apply, smul_eq_mul, Pi.one_apply, mul_one]
    exact (Finsupp.sum_fintype e (fun _ x ↦ x) (fun _ ↦ rfl)).symm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [show (∏ x, c ^ e x) = c ^ ∑ x, e x by
    simpa using Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin (n + 1))) e c]
  rw [hd]
  ring

private lemma chowEE_eval_smul_eq_zero_iff {n d : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℂ) (hP : P.IsHomogeneous d)
    (c : ℂ) (hc : c ≠ 0) (z : Fin (n + 1) → ℂ) :
    MvPolynomial.eval (c • z) P = 0 ↔ MvPolynomial.eval z P = 0 := by
  rw [chowEE_eval_smul_of_isHomogeneous P hP]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero d hc))

private theorem chowEE_affinePoint_integral {ι : Type} (w : ι → ℂ) :
    ((affineSpaceEquiv ι).symm w).left ≫ AffineSpace.toSpecMvPoly ι (Spec ↧ℂ) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
        ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom) w)) := by
  apply (AffineSpace.toSpecMvPolyIntEquiv ι).injective
  funext j
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso ↧ℂ).hom).injective
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
  change (Scheme.ΓSpecIso ↧ℂ).hom
    (((affineSpaceEquiv ι).symm w).left.appTop (AffineSpace.coord (Spec ↧ℂ) j)) = _
  rw [← affineSpaceEquiv_apply, Equiv.apply_symm_apply]
  dsimp only [AffineSpace.toSpecMvPolyIntEquiv, Equiv.coe_fn_mk]
  symm
  calc
    _ = (Spec.preimage (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
        ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom) w)))).hom (MvPolynomial.X j) :=
      (ComplexProjectiveSpace.specPreimage_apply _ _).symm
    _ = w j := by rw [Spec.preimage_map]; simp

private theorem chowEE_chartPoint {n : ℕ} (i : Fin (n + 1))
    (w : ChowEEChartVars i → ℂ) :
    ((affineSpaceEquiv (ChowEEChartVars i)).symm w).left ≫ chowEE_standardChart n i =
      ComplexProjectiveSpace.vectorToProjectiveSpace (chowEE_chartVector i w)
        (by intro h; have := congrFun h i; simp [chowEE_chartVector] at this) := by
  have hi : chowEE_chartVector i w i ≠ 0 := by simp [chowEE_chartVector]
  apply Limits.pullback.hom_ext
  · change (_ ≫ chowEE_standardChart n i) ≫ ProjectiveSpace.toBase _ _ =
      _ ≫ ProjectiveSpace.toBase _ _
    rw [Category.assoc, chowEE_standardChart_base,
      ComplexProjectiveSpace.vectorToProjectiveSpace_toBase]
    exact Over.w _
  · rw [Category.assoc, chowEE_standardChart_integral,
      ← Category.assoc, chowEE_affinePoint_integral,
      ComplexProjectiveSpace.vectorToProjectiveSpace_toProj,
      ComplexProjectiveSpace.chartIntegralProj_eq_chartIntegralProjAt _ _ i hi]
    unfold chowEE_integralChart ComplexProjectiveSpace.chartIntegralProjAt
    rw [← Category.assoc]
    congr 1
    change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply chowEE_away_ext n i
    intro j
    change (MvPolynomial.eval₂Hom _ w)
      (chowEE_chartToPoly n i (ComplexProjectiveSpace.chartCoordinate i j)) = _
    rw [chowEE_chartToPoly_coord]
    simp only [CommRingCat.hom_ofHom]
    unfold ComplexProjectiveSpace.chartCoordinate
    rw [ComplexProjectiveSpace.awayCoordinateEvaluation_mk
      (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j)]
    simp only [ComplexProjectiveSpace.coordinateEvaluationHom_X, pow_one]
    by_cases h : j = i
    · subst j; simp [chowEE_normalizedVar, chowEE_chartVector]
    · simp [chowEE_normalizedVar, chowEE_chartVector, h]

private theorem chowEE_chartPoint_ratios {n : ℕ} (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) (hz : z ≠ 0) (hi : z i ≠ 0) :
    ((affineSpaceEquiv (ChowEEChartVars i)).symm
      (fun j ↦ (z i)⁻¹ * z j)).left ≫ chowEE_standardChart n i =
        ComplexProjectiveSpace.vectorToProjectiveSpace z hz := by
  have hv : chowEE_chartVector i (fun j ↦ (z i)⁻¹ * z j) = (z i)⁻¹ • z := by
    funext j
    by_cases h : j = i
    · subst j; simp [chowEE_chartVector, hi]
    · simp [chowEE_chartVector, h]
  rw [chowEE_chartPoint]
  simpa only [hv] using
    ComplexProjectiveSpace.vectorToProjectiveSpace_smul z hz (z i)⁻¹ (inv_ne_zero hi)

private theorem chowEE_chartRange_coordinate {n : ℕ} (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ) (hz : z ≠ 0)
    (h : (ComplexProjectiveSpace.vectorToComplexPoint z hz).underlying ∈
      (chowEE_standardChart n i).opensRange) : z i ≠ 0 := by
  rw [chowEE_standardChart_range] at h
  change IsLocalRing.closedPoint ℂ ∈
    (ComplexProjectiveSpace.vectorToProjectiveSpace z hz ≫ Limits.pullback.snd _ _) ⁻¹ᵁ
      Proj.basicOpen (ChowEEGrading n) (MvPolynomial.X i) at h
  rw [ComplexProjectiveSpace.vectorToProjectiveSpace_toProj,
    ComplexProjectiveSpace.chartIntegralProj_preimage_basicOpen z hz _ zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i)] at h
  simp only [ComplexProjectiveSpace.coordinateEvaluationHom_X] at h
  intro hi
  rw [if_pos hi] at h
  exact h

private def chowEE_polynomialSection {ι : Type} (Q : MvPolynomial ι ℂ) :
    Γ(complexAffineSpace ι, ⊤) :=
  (AffineSpace.SpecIso ι ↧ℂ).hom.appTop
    ((Scheme.ΓSpecIso ↧(MvPolynomial ι ℂ)).inv Q)

private theorem chowEE_polynomialSection_eval {ι : Type} (Q : MvPolynomial ι ℂ)
    (w : ι → ℂ) :
    Point.evaluate ⊤ (chowEE_polynomialSection Q) ((affineSpaceEquiv ι).symm w) =
      MvPolynomial.eval w Q := by
  rw [evaluate_affineSpaceEquiv_symm_top]
  congr 1
  unfold affineGlobalPolynomial chowEE_polynomialSection
  change (Scheme.ΓSpecIso ↧(MvPolynomial ι ℂ)).hom
    (((AffineSpace.SpecIso ι ↧ℂ).hom.appTop ≫
      (AffineSpace.SpecIso ι ↧ℂ).inv.appTop)
        ((Scheme.ΓSpecIso ↧(MvPolynomial ι ℂ)).inv Q)) = Q
  rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
  simp

private theorem chowEE_chart_basicOpen {n : ℕ} (i : Fin (n + 1))
    (Q : MvPolynomial (ChowEEChartVars i) ℂ)
    (z : Fin (n + 1) → ℂ) (hz : z ≠ 0) (hi : z i ≠ 0) :
    (ComplexProjectiveSpace.vectorToComplexPoint z hz).underlying ∈
      (chowEE_standardChart n i) ''
        (complexAffineSpace (ChowEEChartVars i)).basicOpen (chowEE_polynomialSection Q) ↔
      MvPolynomial.eval (fun j : ChowEEChartVars i ↦ (z i)⁻¹ * z j) Q ≠ 0 := by
  let w : ChowEEChartVars i → ℂ := fun j ↦ (z i)⁻¹ * z j
  let a := (affineSpaceEquiv (ChowEEChartVars i)).symm w
  have ha : chowEE_standardChart n i a.underlying =
      (ComplexProjectiveSpace.vectorToComplexPoint z hz).underlying :=
    congrArg (fun f : Spec ↧ℂ ⟶ ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) ↦
      f (IsLocalRing.closedPoint ℂ)) (chowEE_chartPoint_ratios i z hz hi)
  have he : a.underlying ∈
      (complexAffineSpace (ChowEEChartVars i)).basicOpen (chowEE_polynomialSection Q) ↔
        MvPolynomial.eval w Q ≠ 0 := by
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (U := ⊤)
      (chowEE_polynomialSection Q) a (by trivial)).trans
        (by rw [chowEE_polynomialSection_eval])
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hxa : x = a.underlying :=
      (chowEE_standardChart n i).isOpenEmbedding.injective (hxe.trans ha.symm)
    exact he.mp (hxa ▸ hx)
  · intro h
    exact ⟨a.underlying, he.mpr h, ha⟩

private theorem chowEE_dehomogenize_ratios_zero {n d : ℕ} (i : Fin (n + 1))
    (P : MvPolynomial (Fin (n + 1)) ℂ) (hP : P.IsHomogeneous d)
    (z : Fin (n + 1) → ℂ) (hi : z i ≠ 0) :
    MvPolynomial.eval (fun j : ChowEEChartVars i ↦ (z i)⁻¹ * z j)
      (chowEE_dehomogenize i P) = 0 ↔ MvPolynomial.eval z P = 0 := by
  rw [chowEE_eval_dehomogenize]
  have hv : chowEE_chartVector i (fun j ↦ (z i)⁻¹ * z j) = (z i)⁻¹ • z := by
    funext j
    by_cases h : j = i
    · subst j; simp [chowEE_chartVector, hi]
    · simp [chowEE_chartVector, h]
  rw [hv]
  exact chowEE_eval_smul_eq_zero_iff P hP (z i)⁻¹ (inv_ne_zero hi) z

/-- Source: closed complex points over an algebraically closed field;
Mathlib `pointEquivClosedPoint` and `ext_of_apply_closedPoint_eq`. -/
theorem chowEE_finite_algebraic_aux (Z : Set (ComplexPoint (g3_power E 2)))
    (hZ : Z.Finite) :
    IsClosed ((Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) '' Z) ∧
      Z = (Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) ⁻¹'
        ((Point.underlying : ComplexPoint (g3_power E 2) → (g3_power E 2).left) '' Z) := by
  constructor
  · rw [show Point.underlying '' Z =
        ⋃ z : Z, ({z.1.underlying} : Set (g3_power E 2).left) by
      ext y
      simp]
    letI : Finite Z := hZ
    apply isClosed_iUnion_of_finite
    intro z
    exact ((pointEquivClosedPoint (g3_power E 2).hom) ⟨z.1.left, Over.w z.1⟩).2
  · apply Set.Subset.antisymm
    · intro z hz
      exact ⟨z, hz, rfl⟩
    · rintro z ⟨w, hw, hzw⟩
      have : z = w := by
        apply Over.OverMorphism.ext
        exact ext_of_apply_closedPoint_eq (g3_power E 2).hom (Over.w z) (Over.w w) hzw.symm
      simpa [this] using hw

/-- Source: Hartshorne, Algebraic Geometry, Chapter I §2, homogeneous zero loci
in projective space and their affine chart equations. -/
theorem chowEE_projectiveCarrier_mem_aux (n m : ℕ) (d : Fin m → ℕ)
    (P : Fin m → MvPolynomial (Fin (n + 1)) ℂ)
    (hP : ∀ j, (P j).IsHomogeneous (d j))
    (z : Fin (n + 1) → ℂ) (hz : z ≠ 0) :
    (ComplexProjectiveSpace.vectorToComplexPoint z hz).underlying ∈
        chowEE_projectiveCarrier n m P ↔ ∀ j, MvPolynomial.eval z (P j) = 0 := by
  constructor
  · intro hclosure j
    by_contra hj
    let i := ComplexProjectiveSpace.coordinateIndex z hz
    have hi : z i ≠ 0 := ComplexProjectiveSpace.coordinateIndex_ne_zero z hz
    let Q := chowEE_dehomogenize i (P j)
    let V := (complexAffineSpace (ChowEEChartVars i)).basicOpen
      (chowEE_polynomialSection Q)
    let U : Set (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)) :=
      (chowEE_standardChart n i) '' V
    have hU : IsOpen U := (chowEE_standardChart n i).isOpenEmbedding.isOpenMap V V.isOpen
    have hzU : (ComplexProjectiveSpace.vectorToComplexPoint z hz).underlying ∈ U := by
      apply (chowEE_chart_basicOpen i Q z hz hi).mpr
      exact fun h ↦ hj ((chowEE_dehomogenize_ratios_zero i (P j) (hP j) z hi).mp h)
    obtain ⟨x, hxU, w, hw, hwP, hwx⟩ := mem_closure_iff.mp hclosure U hU hzU
    have hwU : (ComplexProjectiveSpace.vectorToComplexPoint w hw).underlying ∈ U := by
      rw [hwx]
      exact hxU
    have hwi : w i ≠ 0 := by
      apply chowEE_chartRange_coordinate i w hw
      obtain ⟨a, _, ha⟩ := hwU
      exact ⟨a, ha⟩
    exact ((chowEE_chart_basicOpen i Q w hw hwi).mp hwU)
      ((chowEE_dehomogenize_ratios_zero i (P j) (hP j) w hwi).mpr (hwP j))
  · intro hzero
    apply subset_closure
    exact ⟨z, hz, hzero, rfl⟩

end HodgeLean.Foundations
