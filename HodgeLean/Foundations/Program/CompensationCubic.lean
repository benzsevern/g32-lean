import HodgeLean.Foundations.Program.CompensationProductDefs
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.Basic.Complex.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective

set_option maxHeartbeats 400000

/-! # The projective cubic with equation `y²z = x³ + z³`

The two equation charts, their projective image, projectivity, overlap comparison, and
coordinate-open cover are constructed explicitly.
Source: Silverman, *The Arithmetic of Elliptic Curves*, III.1; Hartshorne, II.2 and II.7.
-/

namespace HodgeLean.Foundations.Program.CompensationCubic

noncomputable def W : WeierstrassCurve ℂ := HodgeLean.Foundations.Program.cp_W

theorem W_discriminant : W.Δ = -432 := HodgeLean.Foundations.Program.cp_W_discriminant

instance : W.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, W_discriminant]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

section StandardChartCoordinates

open MvPolynomial HomogeneousLocalization AlgebraicGeometry.ComplexProjectiveSpace

noncomputable section

private abbrev GG := homogeneousSubmodule (Fin 3) (ULift.{0} ℤ)
private abbrev ChartR (i : Fin 3) := Away GG (X i)
private abbrev Vars (i : Fin 3) := {j : Fin 3 // j ≠ i}
private abbrev PolyR (i : Fin 3) := MvPolynomial (Vars i) (ULift.{0} ℤ)

private theorem away_ext {R : Type} [CommRing R] (i : Fin 3)
    (φ ψ : ChartR i →+* R)
    (hc : ∀ j, φ (chartCoordinate i j) = ψ (chartCoordinate i j)) : φ = ψ := by
  have hb : φ.comp (fromZeroRingHom GG (.powers (X i))) =
      ψ.comp (fromZeroRingHom GG (.powers (X i))) := by
    let e : GG 0 ≃+* ℤ :=
      (ProjectiveSpace.degreeZeroEquiv (Fin 3) (ULift.{0} ℤ)).trans ULift.ringEquiv
    apply (RingHom.cancel_right (f := e.symm.toRingHom) e.symm.surjective).mp
    exact Subsingleton.elim _ _
  let : Algebra (GG 0) R :=
    (φ.comp (fromZeroRingHom GG (.powers (X i)))).toAlgebra
  let φa : ChartR i →ₐ[GG 0] R := { φ with commutes' := fun _ ↦ rfl }
  let ψa : ChartR i →ₐ[GG 0] R :=
    { ψ with commutes' := fun r ↦ (DFunLike.congr_fun hb r).symm }
  change φa.toRingHom = ψa.toRingHom
  apply congrArg AlgHom.toRingHom
  apply AlgHom.ext_of_adjoin_eq_top
    (Away.adjoin_mk_prod_pow_eq_top (isHomogeneous_X (ULift.{0} ℤ) i)
      (Fin 3) (fun j ↦ X j) (adjoin_coordinates_eq_top 2)
      (fun _ ↦ (1 : ℕ)) (fun j ↦ isHomogeneous_X (ULift.{0} ℤ) j))
  rintro z ⟨a, ai, hai, _, rfl⟩
  have hai' : ∑ j, ai j = a := by simpa using hai
  rw [chartGenerator_eq_prod i ai hai']
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change φ (chartCoordinate i j ^ ai j) = ψ (chartCoordinate i j ^ ai j)
  rw [map_pow, map_pow, hc]

private def normalizedVars (i j : Fin 3) : PolyR i :=
  if h : j = i then 1 else X ⟨j, h⟩

private def normalize (i : Fin 3) : UniversalRing 2 →+* PolyR i :=
  eval₂Hom C (normalizedVars i)

private def chartToPoly (i : Fin 3) : ChartR i →+* PolyR i :=
  (Localization.awayLift (normalize i) (X i)
    (by simp [normalize, normalizedVars])).comp (algebraMap _ (Localization.Away (X i)))

private theorem chartToPoly_coord (i j : Fin 3) :
    chartToPoly i (chartCoordinate i j) = normalizedVars i j := by
  change (Localization.awayLift (normalize i) (X i)
    (by simp [normalize, normalizedVars]))
    (Localization.mk (X j) ⟨X i ^ 1, ⟨1, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (normalize i) (X i) (X j) 1]
  · simp [normalize]
  · simp [normalize, normalizedVars]

private def polyToChart (i : Fin 3) : PolyR i →+* ChartR i :=
  eval₂Hom ((fromZeroRingHom GG (.powers (X i))).comp
    (ProjectiveSpace.degreeZeroEquiv (Fin 3) (ULift.{0} ℤ)).symm.toRingHom)
    (fun j ↦ chartCoordinate i j.1)

private theorem polyToChart_normalized (i j : Fin 3) :
    polyToChart i (normalizedVars i j) = chartCoordinate i j := by
  by_cases h : j = i
  · subst j; simp [normalizedVars]
  · simp [normalizedVars, h, polyToChart]

private theorem chart_roundtrip (i : Fin 3) :
    (polyToChart i).comp (chartToPoly i) = RingHom.id _ := by
  apply away_ext i _ _
  intro j
  simp only [RingHom.comp_apply, RingHom.id_apply, chartToPoly_coord, polyToChart_normalized]

private theorem poly_roundtrip (i : Fin 3) :
    (chartToPoly i).comp (polyToChart i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro ⟨a⟩
    change ((chartToPoly i).comp (polyToChart i)) (C (a : ULift.{0} ℤ)) =
      (RingHom.id (PolyR i)) (C (a : ULift.{0} ℤ))
    simp only [map_intCast]
  · intro j
    simp [polyToChart, chartToPoly_coord, normalizedVars, j.2]

private def chartEquiv (i : Fin 3) : ChartR i ≃+* PolyR i where
  __ := chartToPoly i
  invFun := polyToChart i
  left_inv a := DFunLike.congr_fun (chart_roundtrip i) a
  right_inv a := DFunLike.congr_fun (poly_roundtrip i) a

private def integralChart (i : Fin 3) : Spec ↧(PolyR i) ⟶ Proj GG :=
  (Scheme.Spec.mapIso (chartEquiv i).toCommRingCatIso.op).hom ≫
    Proj.awayι GG (X i) (isHomogeneous_X _ i) zero_lt_one

private instance integralChart_open (i : Fin 3) : IsOpenImmersion (integralChart i) := by
  change IsOpenImmersion ((Scheme.Spec.mapIso (chartEquiv i).toCommRingCatIso.op).hom ≫ _)
  infer_instance

private theorem integralChart_range (i : Fin 3) :
    (integralChart i).opensRange = Proj.basicOpen GG (X i) := by
  unfold integralChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

private def standardChart (i : Fin 3) : 𝔸(Vars i; Spec ↧ℂ) ⟶ ℙ(Fin 3; Spec ↧ℂ) :=
  Limits.pullback.map _ _ _ _ (𝟙 _) (integralChart i) (𝟙 _)
    (by simp) (by simp)

private instance standardChart_open (i : Fin 3) : IsOpenImmersion (standardChart i) := by
  unfold standardChart
  infer_instance

private theorem standardChart_base (i : Fin 3) :
    standardChart i ≫ ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ) =
      (𝔸(Vars i; Spec ↧ℂ) ↘ Spec ↧ℂ) := by
  change standardChart i ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _
  simp [standardChart]

private theorem standardChart_integral (i : Fin 3) :
    standardChart i ≫ Limits.pullback.snd _ _ =
      AffineSpace.toSpecMvPoly (Vars i) (Spec ↧ℂ) ≫ integralChart i := by
  simp [standardChart, AffineSpace.toSpecMvPoly]

private theorem standardChart_pullback (i : Fin 3) :
    IsPullback (standardChart i) (AffineSpace.toSpecMvPoly (Vars i) (Spec ↧ℂ))
      (Limits.pullback.snd _ _) (integralChart i) := by
  refine (IsPullback.paste_horiz_iff (.of_hasPullback _ _)
    (standardChart_integral i)).mp ?_
  simp only [Limits.terminal.comp_from]
  convert! (IsPullback.of_hasPullback _ _)
  exact standardChart_base i

private theorem standardChart_range (i : Fin 3) :
    (standardChart i).opensRange =
      (Limits.pullback.snd (Limits.terminal.from (Spec ↧ℂ))
        (Limits.terminal.from (Proj GG))) ⁻¹ᵁ Proj.basicOpen GG (X i) := by
  rw [← integralChart_range i]
  apply TopologicalSpace.Opens.ext
  change Set.range (standardChart i) = _
  rw [← (standardChart_pullback i).isoPullback_hom_fst]
  have hs : Set.range (standardChart_pullback i).isoPullback.hom = Set.univ :=
    Set.range_eq_univ.mpr (by exact (standardChart_pullback i).isoPullback.hom.homeomorph.surjective)
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs, Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst _ _

private def complexPoly (i : Fin 3) := MvPolynomial (Vars i) ℂ
private def intPolyMap (i : Fin 3) : PolyR i →+* MvPolynomial (Vars i) ℂ :=
  MvPolynomial.map ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom)

private theorem affineSpec_integral (i : Fin 3) :
    (AffineSpace.SpecIso (Vars i) (CommRingCat.of ℂ)).inv ≫
      AffineSpace.toSpecMvPoly (Vars i) (Spec ↧ℂ) =
      Spec.map (CommRingCat.ofHom (intPolyMap i)) := by
  apply (AffineSpace.toSpecMvPolyIntEquiv (Vars i)).injective
  ext j
  change (AffineSpace.SpecIso (Vars i) (CommRingCat.of ℂ)).inv.appTop
      (AffineSpace.coord (Spec ↧ℂ) j) = _
  rw [AffineSpace.SpecIso_inv_appTop_coord]
  change (Scheme.ΓSpecIso _).inv (X j) =
    (Spec.map (CommRingCat.ofHom (intPolyMap i))).appTop ((Scheme.ΓSpecIso _).inv (X j))
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  change (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Vars i) ℂ))).inv.hom (X j) =
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Vars i) ℂ))).inv.hom (intPolyMap i (X j))
  rw [show intPolyMap i (X j) = X j by simp [intPolyMap]]

private def standardChartSpec (i : Fin 3) :
    Spec ↧(MvPolynomial (Vars i) ℂ) ⟶ ℙ(Fin 3; Spec ↧ℂ) :=
  (AffineSpace.SpecIso (Vars i) (CommRingCat.of ℂ)).inv ≫ standardChart i

private instance standardChartSpec_open (i : Fin 3) :
    IsOpenImmersion (standardChartSpec i) := by
  unfold standardChartSpec
  infer_instance

private theorem standardChartSpec_integral (i : Fin 3) :
    standardChartSpec i ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((intPolyMap i).comp (chartEquiv i).toRingHom)) ≫
      Proj.awayι GG (X i) (isHomogeneous_X _ i) zero_lt_one := by
  rw [standardChartSpec, Category.assoc, standardChart_integral,
    ← Category.assoc, affineSpec_integral]
  change Spec.map (CommRingCat.ofHom (intPolyMap i)) ≫
    Spec.map (CommRingCat.ofHom (chartEquiv i).toRingHom) ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

private theorem chartToPoly_mk (i : Fin 3) (n : ℕ) (p : UniversalRing 2)
    (hp : p ∈ GG (n • 1)) :
    chartToPoly i (Away.mk GG (isHomogeneous_X _ i) n p hp) = normalize i p := by
  change (Localization.awayLift (normalize i) (X i)
    (by simp [normalize, normalizedVars]))
    (Localization.mk p ⟨X i ^ n, ⟨n, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (normalize i) (X i) p 1]
  · simp
  · simp [normalize, normalizedVars]

private theorem standardChartSpec_preimage (i : Fin 3) (d : ℕ) (hd : 0 < d)
    (p : UniversalRing 2) (hp : p ∈ GG d) :
    (standardChartSpec i ≫ Limits.pullback.snd _ _) ⁻¹ᵁ Proj.basicOpen GG p =
      PrimeSpectrum.basicOpen (intPolyMap i (normalize i p)) := by
  rw [standardChartSpec_integral, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := GG) (isHomogeneous_X _ i) zero_lt_one hp hd, SpecMap_preimage_basicOpen]
  congr 1
  change intPolyMap i (chartToPoly i (Away.isLocalizationElem _ hp)) = _
  congr 1
  simpa [Away.isLocalizationElem] using
    chartToPoly_mk i d p (by simpa using hp)

private def chartEval {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) : MvPolynomial (Vars i) ℂ →+* R :=
  eval₂Hom (algebraMap ℂ R) (fun j ↦ c j.1)

private def embedFromChart {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) : Spec ↧R ⟶ ℙ(Fin 3; Spec ↧ℂ) :=
  Spec.map (CommRingCat.ofHom (chartEval i c)) ≫ standardChartSpec i

private theorem embedFromChart_base {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) :
    embedFromChart i c ≫ ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) := by
  simp only [embedFromChart, standardChartSpec, Category.assoc, standardChart_base,
    AffineSpace.SpecIso_inv_over]
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp [chartEval]

private theorem normalized_eval {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) (hc : c i = 1) :
    ((chartEval i c).comp (intPolyMap i)).comp (normalize i) =
      eval₂Hom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom) c := by
  apply MvPolynomial.ringHom_ext
  · intro ⟨r⟩
    simp [chartEval, intPolyMap, normalize]
    exact map_intCast (eval₂Hom (algebraMap ℂ R) (fun j : Vars i ↦ c j.1)) r
  · intro j
    by_cases h : j = i
    · subst j
      simp [chartEval, intPolyMap, normalize, normalizedVars, hc]
    · simp [chartEval, intPolyMap, normalize, normalizedVars, h]

private theorem embedFromChart_preimage {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) (hc : c i = 1)
    (d : ℕ) (hd : 0 < d) (p : UniversalRing 2) (hp : p ∈ GG d) :
    (embedFromChart i c ≫ Limits.pullback.snd _ _) ⁻¹ᵁ Proj.basicOpen GG p =
      PrimeSpectrum.basicOpen (eval₂Hom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom) c p) := by
  rw [embedFromChart, Category.assoc, Scheme.Hom.comp_preimage,
    standardChartSpec_preimage i d hd p hp, SpecMap_preimage_basicOpen]
  congr 1
  exact DFunLike.congr_fun (normalized_eval i c hc) p

private theorem polynomialQuotient_surjective
    {σ : Type} (p : Polynomial (Polynomial ℂ))
    (φ : MvPolynomial σ ℂ →+* AdjoinRoot p)
    (hC : ∀ r, φ (C r) = algebraMap ℂ (AdjoinRoot p) r)
    (j k : σ) (hj : φ (X j) = AdjoinRoot.of p Polynomial.X)
    (hk : φ (X k) = AdjoinRoot.root p) : Function.Surjective φ := by
  rw [← RingHom.range_eq_top]
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  have hx : AdjoinRoot.of p Polynomial.X ∈ φ.range := hj ▸ φ.mem_range_self (X j)
  have hy : AdjoinRoot.root p ∈ φ.range := hk ▸ φ.mem_range_self (X k)
  have hcoeff (r : Polynomial ℂ) : AdjoinRoot.of p r ∈ φ.range := by
    induction r using Polynomial.induction_on' with
    | add r s hr hs => simpa only [map_add] using φ.range.add_mem hr hs
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply φ.range.mul_mem _ (φ.range.pow_mem hx n)
      exact (hC c) ▸ φ.mem_range_self (C c)
  induction q using Polynomial.induction_on' with
  | add r s hr hs => simpa only [map_add] using φ.range.add_mem hr hs
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
      AdjoinRoot.mk_C]
    exact φ.range.mul_mem (hcoeff c) (φ.range.pow_mem hy n)

end

private theorem coprod_ker {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    [QuasiCompact (coprod.desc f g)] : (coprod.desc f g).ker = f.ker ⊓ g.ker := by
  have h := (coprod.desc f g).iInf_ker_openCover_map_comp (coprodOpenCover.{0,0} X Y)
  simpa [coprodOpenCover, iInf_sum] using h.symm

private theorem comp_mono_pullback {A U P : Scheme} (i : A ⟶ U) (u : U ⟶ P) [Mono u] :
    IsPullback i (𝟙 A) u (i ≫ u) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk i (𝟙 A) (by simp))
  refine PullbackCone.IsLimit.mk (by simp) (fun s ↦ s.snd) ?_ (by simp) ?_
  · intro s
    apply (cancel_mono u).mp
    simpa only [Category.assoc] using s.condition.symm
  · intro s m _ hm
    simpa using hm

private theorem image_chart_ker {A B U P : Scheme} (i : A ⟶ U) (u : U ⟶ P) (g : B ⟶ P)
    [IsClosedImmersion i] [IsOpenImmersion u] [QuasiCompact (i ≫ u)] [QuasiCompact g]
    [QuasiCompact (coprod.desc (i ≫ u) g)]
    (h : pullback g u ⟶ A) (hh : h ≫ i = pullback.snd g u) :
    (pullback.snd (coprod.desc (i ≫ u) g).imageι u).ker = i.ker := by
  ext V : 2
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (coprod.desc (i ≫ u) g).imageι _ _ u
    (IsPullback.of_hasPullback _ _).flip]
  simp only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι, coprod_ker,
    Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, Ideal.comap_inf]
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (i ≫ u) i (𝟙 A) u
      (comp_mono_pullback i u),
    ← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g (pullback.snd g u)
      (pullback.fst g u) u (IsPullback.of_hasPullback _ _).flip]
  have hle : i.ker ≤ (pullback.snd g u).ker := by
    rw [← hh]
    exact Scheme.Hom.le_ker_comp h i
  exact inf_eq_left.mpr (hle V)

private noncomputable def imageChartIso {A B U P : Scheme} (i : A ⟶ U) (u : U ⟶ P) (g : B ⟶ P)
    [IsClosedImmersion i] [IsOpenImmersion u] [QuasiCompact (i ≫ u)] [QuasiCompact g]
    [QuasiCompact (coprod.desc (i ≫ u) g)]
    (h : pullback g u ⟶ A) (hh : h ≫ i = pullback.snd g u) :
    pullback (coprod.desc (i ≫ u) g).imageι u ≅ A := by
  let f := IsClosedImmersion.lift i (pullback.snd (coprod.desc (i ≫ u) g).imageι u)
    (image_chart_ker i u g h hh).symm.le
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ (image_chart_ker i u g h hh).symm
  exact asIso f

private theorem image_chart_ker_right {A B U P : Scheme} (i : A ⟶ U) (u : U ⟶ P) (g : B ⟶ P)
    [IsClosedImmersion i] [IsOpenImmersion u] [QuasiCompact (i ≫ u)] [QuasiCompact g]
    [QuasiCompact (coprod.desc g (i ≫ u))]
    (h : pullback g u ⟶ A) (hh : h ≫ i = pullback.snd g u) :
    (pullback.snd (coprod.desc g (i ≫ u)).imageι u).ker = i.ker := by
  ext V : 2
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (coprod.desc g (i ≫ u)).imageι _ _ u
    (IsPullback.of_hasPullback _ _).flip]
  simp only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι, coprod_ker,
    Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, Ideal.comap_inf]
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (i ≫ u) i (𝟙 A) u
      (comp_mono_pullback i u),
    ← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g (pullback.snd g u)
      (pullback.fst g u) u (IsPullback.of_hasPullback _ _).flip]
  have hle : i.ker ≤ (pullback.snd g u).ker := by
    rw [← hh]
    exact Scheme.Hom.le_ker_comp h i
  exact inf_eq_right.mpr (hle V)

private noncomputable def imageChartIsoRight {A B U P : Scheme} (i : A ⟶ U) (u : U ⟶ P) (g : B ⟶ P)
    [IsClosedImmersion i] [IsOpenImmersion u] [QuasiCompact (i ≫ u)] [QuasiCompact g]
    [QuasiCompact (coprod.desc g (i ≫ u))]
    (h : pullback g u ⟶ A) (hh : h ≫ i = pullback.snd g u) :
    pullback (coprod.desc g (i ≫ u)).imageι u ≅ A := by
  let f := IsClosedImmersion.lift i (pullback.snd (coprod.desc g (i ≫ u)).imageι u)
    (image_chart_ker_right i u g h hh).symm.le
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ (image_chart_ker_right i u g h hh).symm
  exact asIso f

noncomputable section
private def chartFraction {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) : ChartR i →+* R :=
  (chartEval i c).comp ((intPolyMap i).comp (chartEquiv i).toRingHom)

private theorem chartFraction_coord {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) (hc : c i = 1) (k : Fin 3) :
    chartFraction i c (chartCoordinate i k) = c k := by
  change chartEval i c (intPolyMap i (chartToPoly i (chartCoordinate i k))) = _
  rw [chartToPoly_coord]
  by_cases h : k = i
  · subst k; simp [normalizedVars, hc]
  · simp [normalizedVars, h, intPolyMap, chartEval]

private def pairFraction {R : Type} [CommRing R] (i j : Fin 3)
    (c : Fin 3 → R) (t : R) (hc : c i = 1) (ht : c j * t = 1) :
    Away GG (X i * X j) →+* R :=
  (Localization.awayLift
    (eval₂Hom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom) c) (X i * X j)
    (by simpa [hc] using (isUnit_iff_exists_inv.mpr ⟨t, ht⟩))).comp
    (algebraMap _ (Localization.Away (X i * X j)))

private theorem pairFraction_coord {R : Type} [CommRing R] (i j k : Fin 3)
    (c : Fin 3 → R) (t : R) (hc : c i = 1) (ht : c j * t = 1) :
    pairFraction i j c t hc ht
      (awayMap GG (isHomogeneous_X _ j) rfl (chartCoordinate i k)) = c k := by
  unfold pairFraction chartCoordinate
  simp only [RingHom.comp_apply]
  change (Localization.awayLift _ _ _) ((awayMap GG (isHomogeneous_X _ j) rfl
    (Away.mk GG (isHomogeneous_X _ i) 1 (X k) _)).val) = _
  rw [awayMap_mk, Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ t]
  · simp only [map_mul, eval₂Hom_X', pow_one]
    rw [mul_assoc, ht, mul_one]
  · simp [hc, ht]

private theorem pairFraction_coord_other {R : Type} [CommRing R] (i j k : Fin 3)
    (c : Fin 3 → R) (t : R) (hc : c i = 1) (ht : c j * t = 1) :
    pairFraction i j c t hc ht
      (awayMap GG (isHomogeneous_X _ i) (mul_comm (X i) (X j))
        (chartCoordinate j k)) = c k * t := by
  unfold pairFraction chartCoordinate
  simp only [RingHom.comp_apply]
  change (Localization.awayLift _ _ _) ((awayMap GG (isHomogeneous_X _ i) _
    (Away.mk GG (isHomogeneous_X _ j) 1 (X k) _)).val) = _
  rw [awayMap_mk, Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ t]
  · simp [hc]
  · simp [hc, ht]
private theorem embedFromChart_integral {R : Type} [CommRing R] [Algebra ℂ R]
    (i : Fin 3) (c : Fin 3 → R) :
    embedFromChart i c ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (chartFraction i c)) ≫
        Proj.awayι GG (X i) (isHomogeneous_X _ i) zero_lt_one := by
  simp only [embedFromChart, Category.assoc, standardChartSpec_integral]
  rw [← Spec.map_comp_assoc]
  rfl

private theorem embedFromChart_transition {R : Type} [CommRing R] [Algebra ℂ R]
    (i j : Fin 3) (c d : Fin 3 → R) (t : R)
    (hc : c i = 1) (hd : d j = 1) (ht : c j * t = 1)
    (hcd : ∀ k, c k * t = d k) : embedFromChart i c = embedFromChart j d := by
  have hi : (pairFraction i j c t hc ht).comp
      (awayMap GG (isHomogeneous_X _ j) rfl) = chartFraction i c := by
    apply away_ext i
    intro k
    rw [RingHom.comp_apply, pairFraction_coord, chartFraction_coord i c hc]
  have hj : (pairFraction i j c t hc ht).comp
      (awayMap GG (isHomogeneous_X _ i) (mul_comm (X i) (X j))) = chartFraction j d := by
    apply away_ext j
    intro k
    rw [RingHom.comp_apply, pairFraction_coord_other, chartFraction_coord j d hd, hcd]
  apply Limits.pullback.hom_ext
  · exact (embedFromChart_base i c).trans (embedFromChart_base j d).symm
  · rw [embedFromChart_integral, embedFromChart_integral, ← hi, ← hj]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      Proj.SpecMap_awayMap_awayι]

private theorem embedFromChart_map {R S : Type} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (φ : R →+* S)
    (hφ : ∀ z, φ (algebraMap ℂ R z) = algebraMap ℂ S z)
    (i : Fin 3) (c : Fin 3 → R) :
    Spec.map (CommRingCat.ofHom φ) ≫ embedFromChart i c =
      embedFromChart i (fun k ↦ φ (c k)) := by
  unfold embedFromChart
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro z; simpa [chartEval] using hφ z
  · intro k; simp [chartEval]

end

end StandardChartCoordinates

private abbrev A := W.toAffine.CoordinateRing
private abbrev G := MvPolynomial.homogeneousSubmodule (Fin 3) (ULift ℤ)

private noncomputable def affineCoordinates : Fin 3 → A :=
  ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X,
    AdjoinRoot.root W.toAffine.polynomial, 1]

private noncomputable def affineEvaluation : MvPolynomial (Fin 3) (ULift ℤ) →+* A :=
  MvPolynomial.eval₂Hom ((algebraMap ℤ A).comp ULift.ringEquiv.toRingHom)
    affineCoordinates

private noncomputable def affineToPlane : Spec ↧A ⟶ ℙ(Fin 3; Spec ↧ℂ) :=
  embedFromChart 2 affineCoordinates

noncomputable def yAffinePolynomial : Polynomial (Polynomial ℂ) :=
  Polynomial.X - Polynomial.C (Polynomial.X ^ 3) -
    Polynomial.X ^ 3

abbrev YCoordinateRing := AdjoinRoot yAffinePolynomial

private noncomputable def yCoordinates : Fin 3 → YCoordinateRing :=
  ![AdjoinRoot.of yAffinePolynomial Polynomial.X, 1,
    AdjoinRoot.root yAffinePolynomial]

private noncomputable def yEvaluation :
    MvPolynomial (Fin 3) (ULift ℤ) →+* YCoordinateRing :=
  MvPolynomial.eval₂Hom ((algebraMap ℤ YCoordinateRing).comp ULift.ringEquiv.toRingHom)
    yCoordinates

private noncomputable def yToPlane : Spec ↧YCoordinateRing ⟶ ℙ(Fin 3; Spec ↧ℂ) :=
  embedFromChart 1 yCoordinates

private theorem affineChartEval_surjective :
    Function.Surjective (chartEval 2 affineCoordinates) := by
  apply polynomialQuotient_surjective W.toAffine.polynomial (chartEval 2 affineCoordinates)
    (fun r ↦ by simp [chartEval]) ⟨0, by decide⟩ ⟨1, by decide⟩
  · simp [chartEval, affineCoordinates]
  · simp [chartEval, affineCoordinates]

private theorem yChartEval_surjective :
    Function.Surjective (chartEval 1 yCoordinates) := by
  apply polynomialQuotient_surjective yAffinePolynomial (chartEval 1 yCoordinates)
    (fun r ↦ by simp [chartEval]) ⟨0, by decide⟩ ⟨2, by decide⟩
  · simp [chartEval, yCoordinates]
  · simp [chartEval, yCoordinates]

private instance affineChart_closed :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (chartEval 2 affineCoordinates))) :=
  IsClosedImmersion.spec_of_surjective _ affineChartEval_surjective

private instance yChart_closed :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (chartEval 1 yCoordinates))) :=
  IsClosedImmersion.spec_of_surjective _ yChartEval_surjective

private noncomputable def chartsToPlane :
    (Spec ↧A) ⨿ (Spec ↧YCoordinateRing) ⟶ ℙ(Fin 3; Spec ↧ℂ) :=
  coprod.desc affineToPlane yToPlane

noncomputable def E : Over (Spec ↧ℂ) :=
  Over.mk (chartsToPlane.imageι ≫ ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))

noncomputable def cubicImmersion : E.left ⟶ ℙ(Fin 3; Spec ↧ℂ) := chartsToPlane.imageι

instance : IsClosedImmersion cubicImmersion := by
  change IsClosedImmersion chartsToPlane.ker.subschemeι
  infer_instance

theorem cubicImmersion_toBase :
    cubicImmersion ≫ ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ) = E.hom := rfl

noncomputable def cubicPresentation : ProjectiveSpace.Presentation E.hom where
  ambientDimension := 2
  immersion := cubicImmersion
  immersion_toBase := cubicImmersion_toBase

instance : IsProjective E.hom := ⟨⟨cubicPresentation⟩⟩

private noncomputable def planeToIntegral : ℙ(Fin 3; Spec ↧ℂ) ⟶ Proj G :=
  pullback.snd _ _

noncomputable def zChart : E.left.Opens :=
  (cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ Proj.basicOpen G (MvPolynomial.X 2)

noncomputable def yChart : E.left.Opens :=
  (cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ Proj.basicOpen G (MvPolynomial.X 1)

private noncomputable def zOrigin : A →+* ℂ :=
  AdjoinRoot.lift (Polynomial.evalRingHom 0) 1 (by
    simp [WeierstrassCurve.Affine.polynomial, W, HodgeLean.Foundations.Program.cp_W])

private noncomputable def yOrigin : YCoordinateRing →+* ℂ :=
  AdjoinRoot.lift (Polynomial.evalRingHom 0) 0 (by
    simp [yAffinePolynomial]
    rw [← Polynomial.C_pow, Polynomial.coeff_C_zero, Polynomial.eval_pow,
      Polynomial.eval_X]
    norm_num)

noncomputable def infinity : Spec ↧ℂ ⟶ E.left :=
  Spec.map (CommRingCat.ofHom yOrigin) ≫ coprod.inr ≫ chartsToPlane.toImage

noncomputable def finitePoint : Spec ↧ℂ ⟶ E.left :=
  Spec.map (CommRingCat.ofHom zOrigin) ≫ coprod.inl ≫ chartsToPlane.toImage

private theorem infinity_immersion :
    infinity ≫ cubicImmersion = Spec.map (CommRingCat.ofHom yOrigin) ≫ yToPlane := by
  simp [infinity, cubicImmersion, chartsToPlane, Category.assoc]

private theorem finitePoint_immersion :
    finitePoint ≫ cubicImmersion = Spec.map (CommRingCat.ofHom zOrigin) ≫ affineToPlane := by
  simp [finitePoint, cubicImmersion, chartsToPlane, Category.assoc]

theorem infinity_over : infinity ≫ E.hom = 𝟙 (Spec ↧ℂ) := by
  rw [← cubicImmersion_toBase, ← Category.assoc, infinity_immersion]
  simp only [Category.assoc, yToPlane, embedFromChart_base]
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ YCoordinateRing) ≫
      CommRingCat.ofHom yOrigin = 𝟙 (CommRingCat.of ℂ) := by
    ext c
    simp [yOrigin, AdjoinRoot.algebraMap_eq']
  rw [h, Spec.map_id]

theorem finitePoint_over : finitePoint ≫ E.hom = 𝟙 (Spec ↧ℂ) := by
  rw [← cubicImmersion_toBase, ← Category.assoc, finitePoint_immersion]
  simp only [Category.assoc, affineToPlane, embedFromChart_base]
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ A) ≫
      CommRingCat.ofHom zOrigin = 𝟙 (CommRingCat.of ℂ) := by
    ext c
    simp [zOrigin, AdjoinRoot.algebraMap_eq']
  rw [h, Spec.map_id]

private theorem infinity_coordinateOpen (i : Fin 3) :
    infinity ⁻¹ᵁ ((cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ
      Proj.basicOpen G (MvPolynomial.X i)) =
      PrimeSpectrum.basicOpen (![0, 1, 0] i : ℂ) := by
  rw [← Scheme.Hom.comp_preimage, ← Category.assoc, infinity_immersion,
    Category.assoc]
  rw [Scheme.Hom.comp_preimage]
  change Spec.map (CommRingCat.ofHom yOrigin) ⁻¹ᵁ
    ((embedFromChart 1 yCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
      Proj.basicOpen GG (MvPolynomial.X i)) = _
  rw [embedFromChart_preimage 1 yCoordinates (by simp [yCoordinates]) 1 zero_lt_one
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i), SpecMap_preimage_basicOpen]
  fin_cases i <;> simp [yCoordinates, yOrigin, AdjoinRoot.lift_of, AdjoinRoot.lift_root]

private theorem finitePoint_coordinateOpen (i : Fin 3) :
    finitePoint ⁻¹ᵁ ((cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ
      Proj.basicOpen G (MvPolynomial.X i)) =
      PrimeSpectrum.basicOpen (![0, 1, 1] i : ℂ) := by
  rw [← Scheme.Hom.comp_preimage, ← Category.assoc, finitePoint_immersion,
    Category.assoc]
  rw [Scheme.Hom.comp_preimage]
  change Spec.map (CommRingCat.ofHom zOrigin) ⁻¹ᵁ
    ((embedFromChart 2 affineCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
      Proj.basicOpen GG (MvPolynomial.X i)) = _
  rw [embedFromChart_preimage 2 affineCoordinates (by simp [affineCoordinates]) 1 zero_lt_one
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i), SpecMap_preimage_basicOpen]
  fin_cases i <;> simp [affineCoordinates, zOrigin, AdjoinRoot.lift_of, AdjoinRoot.lift_root]

theorem infinity_yChart : infinity ⁻¹ᵁ yChart = ⊤ := by
  simpa [yChart] using infinity_coordinateOpen 1

theorem infinity_zChart : infinity ⁻¹ᵁ zChart = ⊥ := by
  simpa [zChart] using infinity_coordinateOpen 2

theorem finitePoint_zChart : finitePoint ⁻¹ᵁ zChart = ⊤ := by
  simpa [zChart] using finitePoint_coordinateOpen 2

theorem finitePoint_yChart : finitePoint ⁻¹ᵁ yChart = ⊤ := by
  simpa [yChart] using finitePoint_coordinateOpen 1

theorem infinity_ne_finitePoint : infinity ≠ finitePoint := by
  intro h
  have heq : (⊥ : (Spec ↧ℂ).Opens) = ⊤ := by
    rw [← infinity_zChart, h, finitePoint_zChart]
  exact bot_ne_top heq

noncomputable def cubicPolynomial : MvPolynomial (Fin 3) (ULift ℤ) :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 - MvPolynomial.X 0 ^ 3 -
    MvPolynomial.X 2 ^ 3

private theorem cubicPolynomial_homogeneous : cubicPolynomial ∈ G 3 := by
  apply Submodule.sub_mem
  · apply Submodule.sub_mem
    · exact (MvPolynomial.isHomogeneous_X _ (1 : Fin 3)).pow 2 |>.mul
        (MvPolynomial.isHomogeneous_X _ (2 : Fin 3))
    · exact (MvPolynomial.isHomogeneous_X _ (0 : Fin 3)).pow 3
  · exact (MvPolynomial.isHomogeneous_X _ (2 : Fin 3)).pow 3

private theorem affineEvaluation_cubic : affineEvaluation cubicPolynomial = 0 := by
  have h := AdjoinRoot.eval₂_root W.toAffine.polynomial
  simp only [WeierstrassCurve.Affine.polynomial, W, HodgeLean.Foundations.Program.cp_W,
    Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    map_add, map_pow, map_zero, map_one, zero_mul, add_zero, one_mul] at h
  simpa [affineEvaluation, cubicPolynomial, affineCoordinates, sub_sub, A, W,
    WeierstrassCurve.toAffine, WeierstrassCurve.Affine.polynomial,
    HodgeLean.Foundations.Program.cp_W] using h

private theorem yEvaluation_cubic : yEvaluation cubicPolynomial = 0 := by
  have h := AdjoinRoot.eval₂_root yAffinePolynomial
  simp only [yAffinePolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_pow] at h
  simpa [yEvaluation, cubicPolynomial, yCoordinates, YCoordinateRing, yAffinePolynomial] using h

private theorem affineToPlane_cubicOpen :
    (affineToPlane ≫ planeToIntegral) ⁻¹ᵁ Proj.basicOpen G cubicPolynomial = ⊥ := by
  change (embedFromChart 2 affineCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
    Proj.basicOpen GG cubicPolynomial = ⊥
  rw [embedFromChart_preimage 2 affineCoordinates (by simp [affineCoordinates]) 3 (by decide)
    cubicPolynomial cubicPolynomial_homogeneous]
  change PrimeSpectrum.basicOpen (affineEvaluation cubicPolynomial) = ⊥
  rw [affineEvaluation_cubic, PrimeSpectrum.basicOpen_zero]

private theorem yToPlane_cubicOpen :
    (yToPlane ≫ planeToIntegral) ⁻¹ᵁ Proj.basicOpen G cubicPolynomial = ⊥ := by
  change (embedFromChart 1 yCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
    Proj.basicOpen GG cubicPolynomial = ⊥
  rw [embedFromChart_preimage 1 yCoordinates (by simp [yCoordinates]) 3 (by decide)
    cubicPolynomial cubicPolynomial_homogeneous]
  change PrimeSpectrum.basicOpen (yEvaluation cubicPolynomial) = ⊥
  rw [yEvaluation_cubic, PrimeSpectrum.basicOpen_zero]

private theorem image_cubicOpen :
    (cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ Proj.basicOpen G cubicPolynomial = ⊥ := by
  let U := planeToIntegral ⁻¹ᵁ Proj.basicOpen G cubicPolynomial
  have hrange : Set.range chartsToPlane ⊆ (U : Set _)ᶜ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨q | q, rfl⟩ := (coprodMk (Spec ↧A) (Spec ↧YCoordinateRing)).surjective q
    · have hq : q ∉ ((affineToPlane ≫ planeToIntegral) ⁻¹ᵁ
          Proj.basicOpen G cubicPolynomial) := by rw [affineToPlane_cubicOpen]; simp
      change planeToIntegral (chartsToPlane (coprodMk _ _ (Sum.inl q))) ∉ Proj.basicOpen G cubicPolynomial
      rw [coprodMk_inl, ← Scheme.Hom.comp_apply (f := coprod.inl) (g := chartsToPlane),
        chartsToPlane, coprod.inl_desc]
      exact hq
    · have hq : q ∉ ((yToPlane ≫ planeToIntegral) ⁻¹ᵁ
          Proj.basicOpen G cubicPolynomial) := by rw [yToPlane_cubicOpen]; simp
      change planeToIntegral (chartsToPlane (coprodMk _ _ (Sum.inr q))) ∉ Proj.basicOpen G cubicPolynomial
      rw [coprodMk_inr, ← Scheme.Hom.comp_apply (f := coprod.inr) (g := chartsToPlane),
        chartsToPlane, coprod.inr_desc]
      exact hq
  have hclosure : closure (Set.range chartsToPlane) ⊆ (U : Set _)ᶜ :=
    closure_minimal hrange U.isOpen.isClosed_compl
  have : CompactSpace ((Spec ↧A) ⨿ (Spec ↧YCoordinateRing) : Scheme) :=
    (coprodMk (Spec ↧A) (Spec ↧YCoordinateRing)).compactSpace
  have : QuasiSeparatedSpace ℙ(Fin 3; Spec ↧ℂ) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))
  have : QuasiCompact chartsToPlane := by infer_instance
  rw [← Scheme.Hom.support_ker] at hclosure
  apply le_bot_iff.mp
  intro x hx
  exact (hclosure x.2) hx

theorem charts_cover : zChart ⊔ yChart = ⊤ := by
  apply top_unique
  intro x _
  change (cubicImmersion ≫ planeToIntegral) x ∈ Proj.basicOpen G (MvPolynomial.X 2) ∨
    (cubicImmersion ≫ planeToIntegral) x ∈ Proj.basicOpen G (MvPolynomial.X 1)
  let p := (cubicImmersion ≫ planeToIntegral) x
  by_contra h
  have hz : MvPolynomial.X 2 ∈ p.asHomogeneousIdeal := by simpa [p] using (not_or.mp h).1
  have hy : MvPolynomial.X 1 ∈ p.asHomogeneousIdeal := by simpa [p] using (not_or.mp h).2
  have hp : cubicPolynomial ∈ p.asHomogeneousIdeal := by
    by_contra hp
    have hx : x ∈ (cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ
        Proj.basicOpen G cubicPolynomial := hp
    rw [image_cubicOpen] at hx
    exact hx
  have hx3 : MvPolynomial.X 0 ^ 3 ∈ p.asHomogeneousIdeal.toIdeal := by
    have heq : MvPolynomial.X 0 ^ 3 =
        MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 - cubicPolynomial -
          MvPolynomial.X 2 ^ 3 := by
      unfold cubicPolynomial
      ring
    rw [heq]
    exact p.asHomogeneousIdeal.toIdeal.sub_mem
      (p.asHomogeneousIdeal.toIdeal.sub_mem
        (p.asHomogeneousIdeal.toIdeal.mul_mem_left _ hz) hp)
      (p.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hz 3 (by decide))
  have hx0 : MvPolynomial.X 0 ∈ p.asHomogeneousIdeal := p.isPrime.mem_of_pow_mem 3 hx3
  have hc : p ∈ ⨆ i : Fin 3, Proj.basicOpen G (MvPolynomial.X i) := by
    rw [show (⨆ i : Fin 3, Proj.basicOpen G (MvPolynomial.X i)) = ⊤ from
      ComplexProjectiveSpace.iSup_coordinateBasicOpen_eq_top 2]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  fin_cases i
  · exact hi hx0
  · exact hi hy
  · exact hi hz

section Overlap

open Polynomial

noncomputable section

private abbrev AA := W.toAffine.CoordinateRing
private abbrev BB := YCoordinateRing
private def ax : AA := AdjoinRoot.of W.toAffine.polynomial X
private def ay : AA := AdjoinRoot.root W.toAffine.polynomial
private def bu : BB := AdjoinRoot.of yAffinePolynomial X
private def bv : BB := AdjoinRoot.root yAffinePolynomial
private abbrev LA := Localization.Away ay
private abbrev LB := Localization.Away bv
private def ainv : LA := IsLocalization.Away.invSelf ay
private def binv : LB := IsLocalization.Away.invSelf bv

private theorem arel : ay ^ 2 - ax ^ 3 - 1 = 0 := by
  have h := AdjoinRoot.eval₂_root W.toAffine.polynomial
  simp only [WeierstrassCurve.Affine.polynomial, W, HodgeLean.Foundations.Program.cp_W,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C,
    map_add, map_pow, map_zero, map_one, zero_mul, add_zero, one_mul] at h
  simpa [ax, ay, AA, W, WeierstrassCurve.toAffine, WeierstrassCurve.Affine.polynomial,
    HodgeLean.Foundations.Program.cp_W, sub_sub] using h

private theorem brel : bv - bu ^ 3 - bv ^ 3 = 0 := by
  have h := AdjoinRoot.eval₂_root yAffinePolynomial
  simp only [yAffinePolynomial, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_pow] at h
  simpa [bu, bv, BB, YCoordinateRing, yAffinePolynomial] using h

private theorem toA_relation {R : Type*} [CommRing R] (u v t : R)
    (h : v - u ^ 3 - v ^ 3 = 0) (ht : v * t = 1) :
    t ^ 2 - (u * t) ^ 3 - 1 = 0 := by
  calc
    _ = (v - u ^ 3 - v ^ 3) * t ^ 3 +
      (1 - v * t) * (t ^ 2 - ((v * t) ^ 2 + v * t + 1)) := by ring
    _ = 0 := by rw [h, ht]; ring

private theorem toB_relation {R : Type*} [CommRing R] (x y t : R)
    (h : y ^ 2 - x ^ 3 - 1 = 0) (ht : y * t = 1) :
    t - (x * t) ^ 3 - t ^ 3 = 0 := by
  calc
    _ = (y ^ 2 - x ^ 3 - 1) * t ^ 3 + t * (1 - (y * t) ^ 2) := by ring
    _ = 0 := by rw [h, ht]; ring

private def aToLB : AA →+* LB :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap ℂ LB) (algebraMap BB LB bu * binv)) binv (by
    have h := congrArg (algebraMap BB LB) brel
    simp only [map_sub, map_pow, map_mul, map_zero] at h
    have ht : algebraMap BB LB bv * binv = 1 := IsLocalization.Away.mul_invSelf bv
    have hh := toA_relation (algebraMap BB LB bu) (algebraMap BB LB bv) binv h ht
    simp only [WeierstrassCurve.Affine.polynomial, W, HodgeLean.Foundations.Program.cp_W,
      eval₂_sub, eval₂_add, eval₂_pow, eval₂_C, eval₂_X,
      map_add, map_pow, map_zero, map_one, zero_mul, add_zero, one_mul]
    simpa only [coe_eval₂RingHom, eval₂_X, eval₂_C, eval₂_one, sub_sub] using hh)

private def bToLA : BB →+* LA :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap ℂ LA) (algebraMap AA LA ax * ainv)) ainv (by
    have h := congrArg (algebraMap AA LA) arel
    simp only [map_sub, map_pow, map_zero, map_one] at h
    have ht : algebraMap AA LA ay * ainv = 1 := IsLocalization.Away.mul_invSelf ay
    have hh := toB_relation (algebraMap AA LA ax) (algebraMap AA LA ay) ainv h ht
    simp only [yAffinePolynomial, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, map_pow]
    simpa only [coe_eval₂RingHom, eval₂_X, eval₂_C] using hh)

private theorem aToLB_x : aToLB ax = algebraMap BB LB bu * binv := by
  simp [aToLB, ax, AdjoinRoot.lift_of]
private theorem aToLB_y : aToLB ay = binv := by simp [aToLB, ay]
private theorem bToLA_u : bToLA bu = algebraMap AA LA ax * ainv := by
  simp [bToLA, bu, AdjoinRoot.lift_of]
private theorem bToLA_v : bToLA bv = ainv := by simp [bToLA, bv]

private def aOverlapToB : LA →+* LB := Localization.awayLift aToLB ay (by
  rw [aToLB_y]
  exact isUnit_iff_exists_inv.mpr ⟨algebraMap BB LB bv, by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf bv⟩)

private def bOverlapToA : LB →+* LA := Localization.awayLift bToLA bv (by
  rw [bToLA_v]
  exact isUnit_iff_exists_inv.mpr ⟨algebraMap AA LA ay, by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf ay⟩)

private theorem aToLB_C (c : ℂ) :
    aToLB (algebraMap ℂ AA c) = algebraMap ℂ LB c := by
  simp [aToLB, AdjoinRoot.algebraMap_eq']
private theorem bToLA_C (c : ℂ) :
    bToLA (algebraMap ℂ BB c) = algebraMap ℂ LA c := by
  simp [bToLA, AdjoinRoot.algebraMap_eq']

private theorem aOverlap_base (a : AA) : aOverlapToB (algebraMap AA LA a) = aToLB a := by
  simp only [aOverlapToB, Localization.awayLift, IsLocalization.Away.lift_eq]
private theorem bOverlap_base (b : BB) : bOverlapToA (algebraMap BB LB b) = bToLA b := by
  simp only [bOverlapToA, Localization.awayLift, IsLocalization.Away.lift_eq]

private theorem aOverlap_C (c : ℂ) : aOverlapToB (algebraMap ℂ LA c) = algebraMap ℂ LB c := by
  rw [IsScalarTower.algebraMap_apply ℂ AA LA, aOverlap_base, aToLB_C]
private theorem bOverlap_C (c : ℂ) : bOverlapToA (algebraMap ℂ LB c) = algebraMap ℂ LA c := by
  rw [IsScalarTower.algebraMap_apply ℂ BB LB, bOverlap_base, bToLA_C]

private theorem aOverlap_inv : aOverlapToB ainv = algebraMap BB LB bv := by
  have h := congrArg aOverlapToB (IsLocalization.Away.mul_invSelf ay (S := LA))
  change aOverlapToB (algebraMap AA LA ay * ainv) = aOverlapToB 1 at h
  rw [map_mul, aOverlap_base, aToLB_y, map_one] at h
  calc
    _ = (algebraMap BB LB bv * binv) * aOverlapToB ainv := by
      rw [show algebraMap BB LB bv * binv = 1 from IsLocalization.Away.mul_invSelf bv, one_mul]
    _ = algebraMap BB LB bv := by rw [mul_assoc, h, mul_one]

private theorem bOverlap_inv : bOverlapToA binv = algebraMap AA LA ay := by
  have h := congrArg bOverlapToA (IsLocalization.Away.mul_invSelf bv (S := LB))
  change bOverlapToA (algebraMap BB LB bv * binv) = bOverlapToA 1 at h
  rw [map_mul, bOverlap_base, bToLA_v, map_one] at h
  calc
    _ = (algebraMap AA LA ay * ainv) * bOverlapToA binv := by
      rw [show algebraMap AA LA ay * ainv = 1 from IsLocalization.Away.mul_invSelf ay, one_mul]
    _ = algebraMap AA LA ay := by rw [mul_assoc, h, mul_one]

private theorem overlapA_base : bOverlapToA.comp aToLB = algebraMap AA LA := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      change bOverlapToA (aToLB (algebraMap ℂ AA c)) = algebraMap ℂ LA c
      rw [aToLB_C, bOverlap_C]
    · change bOverlapToA (aToLB ax) = algebraMap AA LA ax
      rw [aToLB_x, map_mul, bOverlap_base, bToLA_u, bOverlap_inv, mul_assoc]
      rw [mul_comm ainv, show algebraMap AA LA ay * ainv = 1 from IsLocalization.Away.mul_invSelf ay,
        mul_one]
  · change bOverlapToA (aToLB ay) = algebraMap AA LA ay
    rw [aToLB_y, bOverlap_inv]

private theorem overlapB_base : aOverlapToB.comp bToLA = algebraMap BB LB := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      change aOverlapToB (bToLA (algebraMap ℂ BB c)) = algebraMap ℂ LB c
      rw [bToLA_C, aOverlap_C]
    · change aOverlapToB (bToLA bu) = algebraMap BB LB bu
      rw [bToLA_u, map_mul, aOverlap_base, aToLB_x, aOverlap_inv, mul_assoc]
      rw [mul_comm binv, show algebraMap BB LB bv * binv = 1 from IsLocalization.Away.mul_invSelf bv,
        mul_one]
  · change aOverlapToB (bToLA bv) = algebraMap BB LB bv
    rw [bToLA_v, aOverlap_inv]

private theorem overlapA : bOverlapToA.comp aOverlapToB = RingHom.id LA := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ay)
  apply RingHom.ext
  intro a
  change bOverlapToA (aOverlapToB (algebraMap AA LA a)) = algebraMap AA LA a
  rw [aOverlap_base]
  exact DFunLike.congr_fun overlapA_base a

private theorem overlapB : aOverlapToB.comp bOverlapToA = RingHom.id LB := by
  apply IsLocalization.ringHom_ext (Submonoid.powers bv)
  apply RingHom.ext
  intro b
  change aOverlapToB (bOverlapToA (algebraMap BB LB b)) = algebraMap BB LB b
  rw [bOverlap_base]
  exact DFunLike.congr_fun overlapB_base b

def overlapEquiv :
    Localization.Away (AdjoinRoot.root W.toAffine.polynomial) ≃+*
      Localization.Away (AdjoinRoot.root yAffinePolynomial) :=
  RingEquiv.ofRingHom aOverlapToB bOverlapToA overlapB overlapA

private theorem overlapPlane :
    Spec.map (CommRingCat.ofHom aToLB) ≫ affineToPlane =
      Spec.map (CommRingCat.ofHom (algebraMap BB LB)) ≫ yToPlane := by
  change Spec.map (CommRingCat.ofHom aToLB) ≫ embedFromChart 2 affineCoordinates =
    Spec.map (CommRingCat.ofHom (algebraMap BB LB)) ≫ embedFromChart 1 yCoordinates
  rw [embedFromChart_map aToLB aToLB_C,
    embedFromChart_map (algebraMap BB LB) (fun z ↦ IsScalarTower.algebraMap_apply ℂ BB LB z)]
  apply (embedFromChart_transition 1 2 _ _ binv _ _ _ _).symm
  · simp [yCoordinates]
  · simp [affineCoordinates]
  · exact IsLocalization.Away.mul_invSelf bv
  · intro k
    fin_cases k
    · exact aToLB_x.symm
    · simpa [yCoordinates, affineCoordinates, ay] using aToLB_y.symm
    · simp [yCoordinates, affineCoordinates, bv, binv]

private theorem standardChartSpec_range (i : Fin 3) :
    (standardChartSpec i).opensRange = planeToIntegral ⁻¹ᵁ Proj.basicOpen G (MvPolynomial.X i) := by
  change ((AffineSpace.SpecIso (Vars i) (CommRingCat.of ℂ)).inv ≫ standardChart i).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, standardChart_range]
  rfl

private def yZPullIso : Spec ↧LB ≅ pullback yToPlane (standardChartSpec 2) :=
  IsOpenImmersion.isoOfRangeEq (Spec.map (CommRingCat.ofHom (algebraMap BB LB)))
    (pullback.fst yToPlane (standardChartSpec 2)) (by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
      congr 1
      rw [Scheme.Hom.opensRange_pullbackFst, standardChartSpec_range,
        ← Scheme.Hom.comp_preimage]
      change _ = (embedFromChart 1 yCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
        Proj.basicOpen GG (MvPolynomial.X 2)
      rw [embedFromChart_preimage 1 yCoordinates (by simp [yCoordinates]) 1 zero_lt_one
        (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X _ _)]
      simp only [MvPolynomial.eval₂Hom_X']
      apply TopologicalSpace.Opens.ext
      exact PrimeSpectrum.localization_away_comap_range LB bv)

private def yZToA : pullback yToPlane (standardChartSpec 2) ⟶ Spec ↧AA :=
  yZPullIso.inv ≫ Spec.map (CommRingCat.ofHom aToLB)

private theorem yZToA_fac : yZToA ≫ Spec.map (CommRingCat.ofHom (chartEval 2 affineCoordinates)) =
    pullback.snd yToPlane (standardChartSpec 2) := by
  apply (cancel_mono (standardChartSpec 2)).mp
  rw [Category.assoc, ← pullback.condition]
  change (yZPullIso.inv ≫ Spec.map (CommRingCat.ofHom aToLB)) ≫ affineToPlane = _
  rw [Category.assoc, overlapPlane, ← Category.assoc]
  congr 1
  exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

private instance planeQS : QuasiSeparatedSpace ℙ(Fin 3; Spec ↧ℂ) :=
  quasiSeparatedSpace_of_quasiSeparated (ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ))

private instance chartSourceCompact : CompactSpace ((Spec ↧A) ⨿ (Spec ↧YCoordinateRing) : Scheme) :=
  (coprodMk (Spec ↧A) (Spec ↧YCoordinateRing)).compactSpace

private def zPullIso : pullback cubicImmersion (standardChartSpec 2) ≅ Spec ↧AA :=
  imageChartIso (Spec.map (CommRingCat.ofHom (chartEval 2 affineCoordinates)))
    (standardChartSpec 2) yToPlane yZToA yZToA_fac

private def zRestrictPullIso : zChart.toScheme ≅
    pullback cubicImmersion (standardChartSpec 2) :=
  IsOpenImmersion.isoOfRangeEq zChart.ι (pullback.fst cubicImmersion (standardChartSpec 2)) (by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
    congr 1
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.opensRange_pullbackFst,
      standardChartSpec_range, ← Scheme.Hom.comp_preimage]
    rfl)

def zChartIso : zChart.toScheme ≅ Spec ↧(W.toAffine.CoordinateRing) :=
  zRestrictPullIso ≪≫ zPullIso

private theorem overlapPlaneReverse :
    Spec.map (CommRingCat.ofHom bToLA) ≫ yToPlane =
      Spec.map (CommRingCat.ofHom (algebraMap AA LA)) ≫ affineToPlane := by
  change Spec.map (CommRingCat.ofHom bToLA) ≫ embedFromChart 1 yCoordinates =
    Spec.map (CommRingCat.ofHom (algebraMap AA LA)) ≫ embedFromChart 2 affineCoordinates
  rw [embedFromChart_map bToLA bToLA_C,
    embedFromChart_map (algebraMap AA LA) (fun z ↦ IsScalarTower.algebraMap_apply ℂ AA LA z)]
  apply (embedFromChart_transition 2 1 _ _ ainv _ _ _ _).symm
  · simp [affineCoordinates]
  · simp [yCoordinates]
  · exact IsLocalization.Away.mul_invSelf ay
  · intro k
    fin_cases k
    · exact bToLA_u.symm
    · simp [yCoordinates, affineCoordinates, ay, ainv]
    · simpa [yCoordinates, affineCoordinates, bv] using bToLA_v.symm

private def zYPullIso : Spec ↧LA ≅ pullback affineToPlane (standardChartSpec 1) :=
  IsOpenImmersion.isoOfRangeEq (Spec.map (CommRingCat.ofHom (algebraMap AA LA)))
    (pullback.fst affineToPlane (standardChartSpec 1)) (by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
      congr 1
      rw [Scheme.Hom.opensRange_pullbackFst, standardChartSpec_range,
        ← Scheme.Hom.comp_preimage]
      change _ = (embedFromChart 2 affineCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
        Proj.basicOpen GG (MvPolynomial.X 1)
      rw [embedFromChart_preimage 2 affineCoordinates (by simp [affineCoordinates]) 1 zero_lt_one
        (MvPolynomial.X 1) (MvPolynomial.isHomogeneous_X _ _)]
      simp only [MvPolynomial.eval₂Hom_X']
      apply TopologicalSpace.Opens.ext
      exact PrimeSpectrum.localization_away_comap_range LA ay)

private def zYToB : pullback affineToPlane (standardChartSpec 1) ⟶ Spec ↧BB :=
  zYPullIso.inv ≫ Spec.map (CommRingCat.ofHom bToLA)

private theorem zYToB_fac : zYToB ≫ Spec.map (CommRingCat.ofHom (chartEval 1 yCoordinates)) =
    pullback.snd affineToPlane (standardChartSpec 1) := by
  apply (cancel_mono (standardChartSpec 1)).mp
  rw [Category.assoc, ← pullback.condition]
  change (zYPullIso.inv ≫ Spec.map (CommRingCat.ofHom bToLA)) ≫ yToPlane = _
  rw [Category.assoc, overlapPlaneReverse, ← Category.assoc]
  congr 1
  exact IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

private def yPullIso : pullback cubicImmersion (standardChartSpec 1) ≅ Spec ↧BB :=
  imageChartIsoRight (Spec.map (CommRingCat.ofHom (chartEval 1 yCoordinates)))
    (standardChartSpec 1) affineToPlane zYToB zYToB_fac

private def yRestrictPullIso : yChart.toScheme ≅
    pullback cubicImmersion (standardChartSpec 1) :=
  IsOpenImmersion.isoOfRangeEq yChart.ι (pullback.fst cubicImmersion (standardChartSpec 1)) (by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
    congr 1
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.opensRange_pullbackFst,
      standardChartSpec_range, ← Scheme.Hom.comp_preimage]
    rfl)

def yChartIso : yChart.toScheme ≅ Spec ↧YCoordinateRing :=
  yRestrictPullIso ≪≫ yPullIso

def zChartMap : Spec ↧(W.toAffine.CoordinateRing) ⟶ E.left := zChartIso.inv ≫ zChart.ι

def yChartMap : Spec ↧YCoordinateRing ⟶ E.left := yChartIso.inv ≫ yChart.ι

private theorem zChartMap_immersion : zChartMap ≫ cubicImmersion = affineToPlane := by
  have h : zPullIso.hom ≫ Spec.map (CommRingCat.ofHom (chartEval 2 affineCoordinates)) =
      pullback.snd cubicImmersion (standardChartSpec 2) := by
    exact IsClosedImmersion.lift_fac _ _ _
  have hz : zRestrictPullIso.hom ≫ pullback.fst cubicImmersion (standardChartSpec 2) =
      zChart.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hf : zChartIso.hom ≫ affineToPlane = zChart.ι ≫ cubicImmersion := by
    change (zRestrictPullIso.hom ≫ zPullIso.hom) ≫
      (Spec.map (CommRingCat.ofHom (chartEval 2 affineCoordinates)) ≫ standardChartSpec 2) = _
    rw [Category.assoc, ← Category.assoc zPullIso.hom, h, pullback.condition.symm,
      ← Category.assoc, hz]
  rw [zChartMap, Category.assoc, ← hf, Iso.inv_hom_id_assoc]

private theorem yChartMap_immersion : yChartMap ≫ cubicImmersion = yToPlane := by
  have h : yPullIso.hom ≫ Spec.map (CommRingCat.ofHom (chartEval 1 yCoordinates)) =
      pullback.snd cubicImmersion (standardChartSpec 1) := by
    exact IsClosedImmersion.lift_fac _ _ _
  have hy : yRestrictPullIso.hom ≫ pullback.fst cubicImmersion (standardChartSpec 1) =
      yChart.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hf : yChartIso.hom ≫ yToPlane = yChart.ι ≫ cubicImmersion := by
    change (yRestrictPullIso.hom ≫ yPullIso.hom) ≫
      (Spec.map (CommRingCat.ofHom (chartEval 1 yCoordinates)) ≫ standardChartSpec 1) = _
    rw [Category.assoc, ← Category.assoc yPullIso.hom, h, pullback.condition.symm,
      ← Category.assoc, hy]
  rw [yChartMap, Category.assoc, ← hf, Iso.inv_hom_id_assoc]

def yToZCoordinates : W.toAffine.CoordinateRing →+*
    Localization.Away (AdjoinRoot.root yAffinePolynomial) := aToLB

def zToYCoordinates : YCoordinateRing →+*
    Localization.Away (AdjoinRoot.root W.toAffine.polynomial) := bToLA

theorem transition_agreement_y :
    Spec.map (CommRingCat.ofHom yToZCoordinates) ≫ zChartMap =
      Spec.map (CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial)))) ≫ yChartMap := by
  apply (cancel_mono cubicImmersion).mp
  simpa only [Category.assoc, zChartMap_immersion, yChartMap_immersion, yToZCoordinates, LB, BB, bv] using overlapPlane

theorem transition_agreement_z :
    Spec.map (CommRingCat.ofHom zToYCoordinates) ≫ yChartMap =
      Spec.map (CommRingCat.ofHom (algebraMap W.toAffine.CoordinateRing
        (Localization.Away (AdjoinRoot.root W.toAffine.polynomial)))) ≫ zChartMap := by
  apply (cancel_mono cubicImmersion).mp
  simpa only [Category.assoc, zChartMap_immersion, yChartMap_immersion, zToYCoordinates, LA, AA, ay] using overlapPlaneReverse

theorem yToZCoordinates_x : yToZCoordinates (AdjoinRoot.of W.toAffine.polynomial X) =
    algebraMap YCoordinateRing (Localization.Away (AdjoinRoot.root yAffinePolynomial))
      (AdjoinRoot.of yAffinePolynomial X) * IsLocalization.Away.invSelf
        (AdjoinRoot.root yAffinePolynomial) := aToLB_x

theorem yToZCoordinates_y : yToZCoordinates (AdjoinRoot.root W.toAffine.polynomial) =
    IsLocalization.Away.invSelf (AdjoinRoot.root yAffinePolynomial) := aToLB_y

theorem zToYCoordinates_u : zToYCoordinates (AdjoinRoot.of yAffinePolynomial X) =
    algebraMap W.toAffine.CoordinateRing (Localization.Away (AdjoinRoot.root W.toAffine.polynomial))
      (AdjoinRoot.of W.toAffine.polynomial X) * IsLocalization.Away.invSelf
        (AdjoinRoot.root W.toAffine.polynomial) := bToLA_u

theorem zToYCoordinates_v : zToYCoordinates (AdjoinRoot.root yAffinePolynomial) =
    IsLocalization.Away.invSelf (AdjoinRoot.root W.toAffine.polynomial) := bToLA_v

theorem zChartMap_preimage_y : zChartMap ⁻¹ᵁ yChart =
    PrimeSpectrum.basicOpen (AdjoinRoot.root W.toAffine.polynomial) := by
  change zChartMap ⁻¹ᵁ ((cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ
    Proj.basicOpen G (MvPolynomial.X 1)) = _
  rw [← Scheme.Hom.comp_preimage, ← Category.assoc, zChartMap_immersion]
  change (embedFromChart 2 affineCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
    Proj.basicOpen GG (MvPolynomial.X 1) = _
  rw [embedFromChart_preimage 2 affineCoordinates (by simp [affineCoordinates])
    1 zero_lt_one (MvPolynomial.X 1) (MvPolynomial.isHomogeneous_X _ _)]
  simp [affineCoordinates]

theorem yChartMap_preimage_z : yChartMap ⁻¹ᵁ zChart =
    PrimeSpectrum.basicOpen (AdjoinRoot.root yAffinePolynomial) := by
  change yChartMap ⁻¹ᵁ ((cubicImmersion ≫ planeToIntegral) ⁻¹ᵁ
    Proj.basicOpen G (MvPolynomial.X 2)) = _
  rw [← Scheme.Hom.comp_preimage, ← Category.assoc, yChartMap_immersion]
  change (embedFromChart 1 yCoordinates ≫ pullback.snd _ _) ⁻¹ᵁ
    Proj.basicOpen GG (MvPolynomial.X 2) = _
  rw [embedFromChart_preimage 1 yCoordinates (by simp [yCoordinates])
    1 zero_lt_one (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X _ _)]
  simp [yCoordinates]

theorem overlapEquiv_base : overlapEquiv.toRingHom.comp
    (algebraMap W.toAffine.CoordinateRing
      (Localization.Away (AdjoinRoot.root W.toAffine.polynomial))) = yToZCoordinates := by
  apply RingHom.ext
  exact aOverlap_base

theorem overlapEquiv_symm_base : overlapEquiv.symm.toRingHom.comp
    (algebraMap YCoordinateRing (Localization.Away (AdjoinRoot.root yAffinePolynomial))) =
      zToYCoordinates := by
  apply RingHom.ext
  exact bOverlap_base

theorem yChart_equation : AdjoinRoot.root yAffinePolynomial =
    (AdjoinRoot.of yAffinePolynomial X) ^ 3 +
      (AdjoinRoot.root yAffinePolynomial) ^ 3 := by
  have h := brel
  change bv = bu ^ 3 + bv ^ 3
  linear_combination h

def infinityCoordinates : YCoordinateRing →+* ℂ := yOrigin

def finitePointCoordinates : W.toAffine.CoordinateRing →+* ℂ := zOrigin

theorem infinity_chart :
    Spec.map (CommRingCat.ofHom infinityCoordinates) ≫ yChartMap = infinity := by
  apply (cancel_mono cubicImmersion).mp
  rw [Category.assoc, yChartMap_immersion, infinity_immersion]
  rfl

theorem finitePoint_chart :
    Spec.map (CommRingCat.ofHom finitePointCoordinates) ≫ zChartMap = finitePoint := by
  apply (cancel_mono cubicImmersion).mp
  rw [Category.assoc, zChartMap_immersion, finitePoint_immersion]
  rfl

theorem infinityCoordinates_values :
    infinityCoordinates (AdjoinRoot.of yAffinePolynomial X) = 0 ∧
      infinityCoordinates (AdjoinRoot.root yAffinePolynomial) = 0 := by
  simp [infinityCoordinates, yOrigin]

theorem finitePointCoordinates_values :
    finitePointCoordinates (AdjoinRoot.of W.toAffine.polynomial X) = 0 ∧
      finitePointCoordinates (AdjoinRoot.root W.toAffine.polynomial) = 1 := by
  simp [finitePointCoordinates, zOrigin]

theorem zChartMap_over : zChartMap ≫ E.hom =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing)) := by
  rw [← cubicImmersion_toBase, ← Category.assoc, zChartMap_immersion]
  exact embedFromChart_base 2 affineCoordinates

theorem yChartMap_over : yChartMap ≫ E.hom =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ YCoordinateRing)) := by
  rw [← cubicImmersion_toBase, ← Category.assoc, yChartMap_immersion]
  exact embedFromChart_base 1 yCoordinates

end

end Overlap

end HodgeLean.Foundations.Program.CompensationCubic
