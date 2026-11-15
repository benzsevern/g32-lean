import HodgeLean.Foundations.Program.CompensationCubic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

set_option maxHeartbeats 400000

/-! # Integrality and smoothness of the CM cubic

Source: Hartshorne, I.5 and III.10, the Jacobian criterion; Silverman, III.1.
-/

namespace HodgeLean.Foundations.Program.CompensationCubic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem zCoordinateRing_isDomain : IsDomain W.toAffine.CoordinateRing := by
  infer_instance

example : IsDomain W.toAffine.CoordinateRing := zCoordinateRing_isDomain

theorem zChart_isIntegral : IsIntegral zChart.toScheme := by
  exact IsIntegral.of_isIso zChartIso.inv

example : IsIntegral zChart.toScheme := zChart_isIntegral

theorem E_nonempty : Nonempty E.left := by
  exact Nonempty.map infinity inferInstance

example : Nonempty E.left := E_nonempty

noncomputable section

open Polynomial

private theorem y_root_regular :
    AdjoinRoot.root yAffinePolynomial ∈ nonZeroDivisors YCoordinateRing := by
  rw [mem_nonZeroDivisors_iff_left]
  intro a ha
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  have hp : yAffinePolynomial ∣ X * p := by
    apply AdjoinRoot.mk_eq_zero.mp
    simpa only [map_mul, AdjoinRoot.mk_X] using ha
  obtain ⟨q, hq⟩ := hp
  have hq0 : q.coeff 0 = 0 := by
    have h := congrArg (fun p : (ℂ[X])[X] ↦ p.coeff 0) hq
    have hn : (-(X : ℂ[X]) ^ 3) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ X_ne_zero)
    simp only [mul_coeff_zero, yAffinePolynomial, coeff_sub,
      coeff_X_zero, coeff_C_zero, coeff_X_pow, OfNat.zero_ne_ofNat,
      ↓reduceIte, mul_zero, sub_zero, zero_sub] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hn
  obtain ⟨r, hr⟩ := (X_dvd_iff.mpr hq0)
  apply AdjoinRoot.mk_eq_zero.mpr
  refine ⟨r, ?_⟩
  apply mul_left_cancel₀ (X_ne_zero : (X : (ℂ[X])[X]) ≠ 0)
  rw [hq, hr]
  ring

private theorem z_root_ne_zero : AdjoinRoot.root W.toAffine.polynomial ≠ 0 := by
  simpa only [WeierstrassCurve.Affine.CoordinateRing.basis_one,
    WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.mk_X] using
    (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine).ne_zero 1

theorem yCoordinateRing_isDomain : IsDomain YCoordinateRing := by
  let A := Localization.Away (AdjoinRoot.root W.toAffine.polynomial)
  let B := Localization.Away (AdjoinRoot.root yAffinePolynomial)
  have hA : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A
    (powers_le_nonZeroDivisors_of_noZeroDivisors z_root_ne_zero)
  have hB : IsDomain B := Function.Injective.isDomain overlapEquiv.symm.toRingHom overlapEquiv.symm.injective
  have hi : Function.Injective (algebraMap YCoordinateRing B) :=
    IsLocalization.injective B (Submonoid.powers_le.mpr y_root_regular)
  exact Function.Injective.isDomain (algebraMap YCoordinateRing B) hi

example : IsDomain YCoordinateRing := yCoordinateRing_isDomain

theorem yChart_isIntegral : IsIntegral yChart.toScheme := by
  let := yCoordinateRing_isDomain
  exact IsIntegral.of_isIso yChartIso.inv

example : IsIntegral yChart.toScheme := yChart_isIntegral

theorem charts_overlap_nonempty :
    ((zChart : Set E.left) ∩ (yChart : Set E.left)).Nonempty := by
  let p : PrimeSpectrum W.toAffine.CoordinateRing := ⟨⊥, inferInstance⟩
  refine ⟨zChartMap p, ?_, ?_⟩
  · change zChart.ι (zChartIso.inv p) ∈ zChart
    exact (zChartIso.inv p).property
  · have hp : p ∈ zChartMap ⁻¹ᵁ yChart := by
      rw [zChartMap_preimage_y]
      exact z_root_ne_zero
    exact hp

example : ((zChart : Set E.left) ∩ (yChart : Set E.left)).Nonempty :=
  charts_overlap_nonempty

theorem yAffinePolynomial_irreducible : Irreducible yAffinePolynomial := by
  have hn : yAffinePolynomial ≠ 0 := by
    intro h
    have hc := congrArg (fun p : (ℂ[X])[X] ↦ p.coeff 0) h
    simp only [yAffinePolynomial, coeff_sub, coeff_X_zero, coeff_C_zero,
      mul_coeff_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte,
      mul_zero, sub_zero, zero_sub, coeff_zero] at hc
    exact (neg_ne_zero.mpr (pow_ne_zero 3 (X_ne_zero : (X : ℂ[X]) ≠ 0))) hc
  apply Prime.irreducible
  apply (Ideal.span_singleton_prime hn).mp
  exact (Ideal.Quotient.isDomain_iff_prime _).mp yCoordinateRing_isDomain

example : Irreducible yAffinePolynomial := yAffinePolynomial_irreducible

theorem yChart_nonsingular (u v : ℂ) (h : v = u ^ 3 + v ^ 3) :
    -3 * u ^ 2 ≠ 0 ∨ 1 - 3 * v ^ 2 ≠ 0 := by
  have hc : (-3 * u * v) * (-3 * u ^ 2) + (2 - 3 * v ^ 2) * (1 - 3 * v ^ 2) = 2 := by
    linear_combination -9 * v * h
  by_contra! hn
  rw [hn.1, hn.2] at hc
  norm_num at hc

example (u v : ℂ) (h : v = u ^ 3 + v ^ 3) :
    -3 * u ^ 2 ≠ 0 ∨ 1 - 3 * v ^ 2 ≠ 0 := yChart_nonsingular u v h

example : NoZeroDivisors YCoordinateRing := by
  let := yCoordinateRing_isDomain
  infer_instance

#print axioms yAffinePolynomial_irreducible
#print axioms yChart_nonsingular

theorem exists_overlap_complexPoint : ∃ p : Spec ↧ℂ ⟶ E.left,
    p ≫ E.hom = 𝟙 (Spec ↧ℂ) ∧ p ⁻¹ᵁ zChart = ⊤ ∧ p ⁻¹ᵁ yChart = ⊤ := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) (by decide : 0 < 2)
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  let φ : W.toAffine.CoordinateRing →+* ℂ :=
    AdjoinRoot.lift (Polynomial.evalRingHom 1) y (by
      rw [Polynomial.eval₂_evalRingHom]
      rw [WeierstrassCurve.Affine.evalEval_polynomial]
      norm_num [W, HodgeLean.Foundations.Program.cp_W, hy])
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ zChartMap, ?_, ?_, ?_⟩
  · rw [Category.assoc, zChartMap_over, ← Spec.map_comp]
    have hφ : φ.comp (algebraMap ℂ W.toAffine.CoordinateRing) = RingHom.id ℂ := by
      ext c
      change φ (AdjoinRoot.of W.toAffine.polynomial (C c)) = c
      simp [φ]
    change Spec.map (CommRingCat.ofHom (φ.comp (algebraMap ℂ W.toAffine.CoordinateRing))) = _
    rw [hφ]
    exact Spec.map_id _
  · simp [zChartMap]
  · rw [Scheme.Hom.comp_preimage, zChartMap_preimage_y, SpecMap_preimage_basicOpen]
    change PrimeSpectrum.basicOpen (φ (AdjoinRoot.root W.toAffine.polynomial)) = ⊤
    simp only [φ, AdjoinRoot.lift_root]
    apply top_unique
    intro p _
    exact p.asIdeal.notMem_of_isUnit (isUnit_iff_ne_zero.mpr hy0)

example : ∃ p : Spec ↧ℂ ⟶ E.left,
    p ≫ E.hom = 𝟙 (Spec ↧ℂ) ∧ p ⁻¹ᵁ zChart = ⊤ ∧ p ⁻¹ᵁ yChart = ⊤ :=
  exists_overlap_complexPoint

#print axioms exists_overlap_complexPoint

private def cubicOpenCover : E.left.OpenCover :=
  E.left.openCoverOfIsOpenCover (fun b : Bool ↦ if b then zChart else yChart)
    (TopologicalSpace.IsOpenCover.mk (by simpa [iSup_bool_eq, sup_comm] using charts_cover))

theorem E_irreducibleSpace : IrreducibleSpace E.left := by
  let := zChart_isIntegral
  let := yChart_isIntegral
  have : IrreducibleSpace zChart.toScheme := inferInstance
  have : IrreducibleSpace yChart.toScheme := inferInstance
  have hz : IsIrreducible (zChart : Set E.left) := by
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using
      (IrreducibleSpace.isIrreducible_univ zChart.toScheme).image zChart.ι
        zChart.ι.continuous.continuousOn
  have hy : IsIrreducible (yChart : Set E.left) := by
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using
      (IrreducibleSpace.isIrreducible_univ yChart.toScheme).image yChart.ι
        yChart.ι.continuous.continuousOn
  have hd : closure (zChart : Set E.left) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ zChart ⊔ yChart := by rw [charts_cover]; trivial
    rcases hx with hx | hx
    · exact subset_closure hx
    · apply closure_mono Set.inter_subset_right
      apply subset_closure_inter_of_isPreirreducible_of_isOpen hy.2 zChart.isOpen
        (by simpa [Set.inter_comm] using charts_overlap_nonempty) hx
  rw [irreducibleSpace_def]
  simpa only [hd, Set.top_eq_univ] using hz.closure

example : IrreducibleSpace E.left := E_irreducibleSpace

instance E_isIntegral : IsIntegral E.left := by
  let := zChart_isIntegral
  let := yChart_isIntegral
  let := E_irreducibleSpace
  have hr (b : Bool) : IsReduced (cubicOpenCover.X b) := by
    cases b <;> dsimp [cubicOpenCover, Scheme.openCoverOfIsOpenCover] <;> infer_instance
  let : ∀ i : cubicOpenCover.I₀, IsReduced (cubicOpenCover.X i) := hr
  let : IsReduced E.left := IsReduced.of_openCover E.left cubicOpenCover
  exact isIntegral_of_irreducibleSpace_of_isReduced E.left

example : IsIntegral E.left := E_isIntegral

private def bivarMap (f : (ℂ[X])[X]) : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] AdjoinRoot f :=
  ((AdjoinRoot.mkₐ f).restrictScalars ℂ).comp (Polynomial.Bivariate.equivMvPolynomial ℂ).symm.toAlgHom

private def bivarPresentation (f : (ℂ[X])[X]) :
    Algebra.Presentation ℂ (AdjoinRoot f) (Fin 2) Unit where
  __ := Algebra.Generators.ofAlgHom (bivarMap f)
    (AdjoinRoot.mk_surjective.comp (Polynomial.Bivariate.equivMvPolynomial ℂ).symm.surjective)
  relation _ := Polynomial.Bivariate.equivMvPolynomial ℂ f
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_ofAlgHom]
    ext p
    simp only [Set.range_const, Ideal.mem_span_singleton, RingHom.mem_ker]
    change _ ↔ AdjoinRoot.mk f ((Polynomial.Bivariate.equivMvPolynomial ℂ).symm p) = 0
    rw [AdjoinRoot.mk_eq_zero]
    simpa only [AlgEquiv.symm_apply_apply] using
      (map_dvd_iff (Polynomial.Bivariate.equivMvPolynomial ℂ).symm
        (a := Polynomial.Bivariate.equivMvPolynomial ℂ f) (b := p)).symm

private def bivarPre (f : (ℂ[X])[X]) (i : Fin 2) :
    Algebra.PreSubmersivePresentation ℂ (AdjoinRoot f) (Fin 2) Unit where
  __ := bivarPresentation f
  map _ := i
  map_inj := Function.injective_of_subsingleton _

private theorem bivarJac (f : (ℂ[X])[X]) (i : Fin 2) :
    (bivarPre f i).jacobian =
      bivarMap f (MvPolynomial.pderiv i (Polynomial.Bivariate.equivMvPolynomial ℂ f)) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  rw [Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    Algebra.Generators.algebraMap_apply]
  change MvPolynomial.aeval ((bivarMap f) ∘ MvPolynomial.X) _ = _
  rw [← MvPolynomial.aeval_unique (bivarMap f)]
  rfl

private theorem localStandard (f : (ℂ[X])[X]) (i : Fin 2) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ
      (Localization.Away (bivarPre f i).jacobian) := by
  let P := bivarPre f i
  let S := Localization.Away P.jacobian
  let Q := (Algebra.PreSubmersivePresentation.localizationAway S P.jacobian).comp P
  have hu : IsUnit Q.jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
      (IsLocalization.Away.algebraMap_isUnit P.jacobian)
  let T : Algebra.SubmersivePresentation ℂ S (Unit ⊕ Fin 2) (Unit ⊕ Unit) :=
    { Q with jacobian_isUnit := hu }
  exact T.isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

private theorem bivarMap_X0 (f : (ℂ[X])[X]) :
    bivarMap f (MvPolynomial.X 0) = AdjoinRoot.of f X := by
  simp [bivarMap, AdjoinRoot.mk_C]

private theorem bivarMap_X1 (f : (ℂ[X])[X]) :
    bivarMap f (MvPolynomial.X 1) = AdjoinRoot.root f := by
  simp [bivarMap]

private theorem y_mv : Polynomial.Bivariate.equivMvPolynomial ℂ yAffinePolynomial =
    MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 3 := by
  simp [yAffinePolynomial, map_pow]

private theorem z_mv : Polynomial.Bivariate.equivMvPolynomial ℂ W.toAffine.polynomial =
    MvPolynomial.X 1 ^ 2 - (MvPolynomial.X 0 ^ 3 + 1) := by
  simp [WeierstrassCurve.Affine.polynomial, W, HodgeLean.Foundations.Program.cp_W, map_pow]

private theorem y_jac_zero :
    (bivarPre yAffinePolynomial 0).jacobian =
      -3 * (AdjoinRoot.of yAffinePolynomial X)^2 := by
  rw [bivarJac, y_mv]
  simp [map_sub, map_mul, map_pow, map_neg, map_ofNat, bivarMap_X0, bivarMap_X1]

private theorem y_jac_one :
    (bivarPre yAffinePolynomial 1).jacobian =
      1 - 3 * (AdjoinRoot.root yAffinePolynomial)^2 := by
  rw [bivarJac, y_mv]
  simp [map_sub, map_mul, map_ofNat, bivarMap_X0, bivarMap_X1]

private theorem z_jac_zero :
    (bivarPre W.toAffine.polynomial 0).jacobian =
      -3 * (AdjoinRoot.of W.toAffine.polynomial X)^2 := by
  rw [bivarJac, z_mv]
  simp [map_sub, map_mul, map_pow, map_neg, map_ofNat, bivarMap_X0]

private theorem z_jac_one :
    (bivarPre W.toAffine.polynomial 1).jacobian =
      2 * AdjoinRoot.root W.toAffine.polynomial := by
  rw [bivarJac, z_mv]
  simp [map_sub, map_mul, map_ofNat, bivarMap_X1]

private theorem z_relation :
    (AdjoinRoot.root W.toAffine.polynomial)^2 =
      (AdjoinRoot.of W.toAffine.polynomial X)^3 + 1 := by
  have h := (bivarPresentation W.toAffine.polynomial).aeval_val_relation ()
  change MvPolynomial.aeval ((bivarMap W.toAffine.polynomial) ∘ MvPolynomial.X) _ = 0 at h
  rw [← MvPolynomial.aeval_unique (bivarMap W.toAffine.polynomial)] at h
  change bivarMap W.toAffine.polynomial
    (Polynomial.Bivariate.equivMvPolynomial ℂ W.toAffine.polynomial) = 0 at h
  rw [z_mv] at h
  simpa [map_sub, map_add, map_pow, bivarMap_X0, bivarMap_X1, sub_eq_zero] using h

private theorem y_jac_span :
    Ideal.span (Set.range fun i ↦ (bivarPre yAffinePolynomial i).jacobian) = ⊤ := by
  let I := Ideal.span (Set.range fun i ↦ (bivarPre yAffinePolynomial i).jacobian)
  have h0 : (bivarPre yAffinePolynomial 0).jacobian ∈ I := Ideal.subset_span ⟨0, rfl⟩
  have h1 : (bivarPre yAffinePolynomial 1).jacobian ∈ I := Ideal.subset_span ⟨1, rfl⟩
  have h := I.add_mem
    (I.mul_mem_left (-3 * AdjoinRoot.of yAffinePolynomial X * AdjoinRoot.root yAffinePolynomial) h0)
    (I.mul_mem_left (2 - 3 * (AdjoinRoot.root yAffinePolynomial)^2) h1)
  have h2 : (2 : YCoordinateRing) ∈ I := by
    convert h using 1
    rw [y_jac_zero, y_jac_one]
    linear_combination 9 * AdjoinRoot.root yAffinePolynomial * yChart_equation
  have hu : IsUnit (2 : YCoordinateRing) := by
    simpa only [map_ofNat] using
      (show IsUnit (2 : ℂ) by norm_num).map (algebraMap ℂ YCoordinateRing)
  exact I.eq_top_of_isUnit_mem h2 hu

private theorem z_jac_span :
    Ideal.span (Set.range fun i ↦ (bivarPre W.toAffine.polynomial i).jacobian) = ⊤ := by
  let I := Ideal.span (Set.range fun i ↦ (bivarPre W.toAffine.polynomial i).jacobian)
  have h0 : (bivarPre W.toAffine.polynomial 0).jacobian ∈ I := Ideal.subset_span ⟨0, rfl⟩
  have h1 : (bivarPre W.toAffine.polynomial 1).jacobian ∈ I := Ideal.subset_span ⟨1, rfl⟩
  have h := I.add_mem (I.mul_mem_left (2 * AdjoinRoot.of W.toAffine.polynomial X) h0)
    (I.mul_mem_left (3 * AdjoinRoot.root W.toAffine.polynomial) h1)
  have h6 : (6 : AdjoinRoot W.toAffine.polynomial) ∈ I := by
    convert h using 1
    rw [z_jac_zero, z_jac_one]
    linear_combination -6 * z_relation
  have hu : IsUnit (6 : AdjoinRoot W.toAffine.polynomial) := by
    simpa only [map_ofNat] using
      (show IsUnit (6 : ℂ) by norm_num).map (algebraMap ℂ (AdjoinRoot W.toAffine.polynomial))
  exact I.eq_top_of_isUnit_mem h6 hu

private theorem bivar_smooth (f : (ℂ[X])[X])
    (h : Ideal.span (Set.range fun i ↦ (bivarPre f i).jacobian) = ⊤) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjoinRoot f)))) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension 1)]
  refine ⟨_, h, ?_⟩
  rintro _ ⟨i, rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap (AdjoinRoot f) (Localization.Away (bivarPre f i).jacobian)).comp
      (algebraMap ℂ (AdjoinRoot f)))
  rw [← IsScalarTower.algebraMap_eq,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact localStandard f i

instance E_smoothOfRelativeDimension : SmoothOfRelativeDimension 1 E.hom := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1) cubicOpenCover
  intro b
  cases b
  · change SmoothOfRelativeDimension 1 (yChart.ι ≫ E.hom)
    have hs : SmoothOfRelativeDimension 1 (yChartMap ≫ E.hom) := by
      rw [yChartMap_over]
      exact bivar_smooth yAffinePolynomial y_jac_span
    have ht : SmoothOfRelativeDimension (0 + 1)
        (yChartIso.hom ≫ (yChartMap ≫ E.hom)) := inferInstance
    simpa [yChartMap] using ht
  · change SmoothOfRelativeDimension 1 (zChart.ι ≫ E.hom)
    have hs : SmoothOfRelativeDimension 1 (zChartMap ≫ E.hom) := by
      rw [zChartMap_over]
      exact bivar_smooth W.toAffine.polynomial z_jac_span
    have ht : SmoothOfRelativeDimension (0 + 1)
        (zChartIso.hom ≫ (zChartMap ≫ E.hom)) := inferInstance
    simpa [zChartMap] using ht

example : SmoothOfRelativeDimension 1 E.hom := E_smoothOfRelativeDimension

instance E_smooth : Smooth E.hom := by
  let := E_smoothOfRelativeDimension
  exact SmoothOfRelativeDimension.smooth 1 E.hom

example : Smooth E.hom := E_smooth

theorem E_dim : TopologicalSpace.dim E.left = 1 := by
  let := E_isIntegral
  let := E_smooth
  let := E_smoothOfRelativeDimension
  exact SmoothOfRelativeDimension.dim_eq E.hom 1

example : TopologicalSpace.dim E.left = 1 := E_dim

end

end HodgeLean.Foundations.Program.CompensationCubic
