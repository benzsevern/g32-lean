import HodgeLean.Foundations.Curves.CubicGroupDefs
import HodgeLean.Foundations.Curves.CubicAddPoints
import HodgeLean.Foundations.Curves.CubicReduced
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

set_option maxHeartbeats 400000

/-! # Proofs for the curves C3 spec

The proofs of the `_aux` theorems that `CubicGroup.lean` (frozen) restates. Addition is glued
from two homogeneous (2,2) addition laws over sixteen pieces (`CubicAddLaws.lean`,
`CubicAddPoints.lean`, `CubicReduced.lean`).
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Curves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry.ComplexPoint
open scoped TensorProduct

/-! The point comparison first uses the affine nonsingularity criterion. -/
private theorem W_equation_iff_nonsingular {x y : ℂ} :
    W.toAffine.Equation x y ↔ W.toAffine.Nonsingular x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular

/-- A complex point in the Weierstrass affine chart is evaluation at its two
coordinates. -/
private theorem zChart_factorization (P : ComplexPoint E)
    (hP : P ∈ AlgebraicGeometry.Point.overOpen zChart) :
    ∃ (x y : ℂ) (h : W.toAffine.Equation x y),
      P.left = Spec.map (CommRingCat.ofHom (affineEval x y h)) ≫ zChartMap := by
  let q := ComplexPoint.liftToOpen E zChart P hP
  let p := q ≫ zChartIso.hom
  let φ : W.toAffine.CoordinateRing →+* ℂ := (Spec.homEquiv p).hom
  have hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing)) =
      𝟙 (Spec ↧ℂ) := by
    dsimp [p, q]
    rw [← zChartMap_over, ← Category.assoc, zChartMap]
    simp [ComplexPoint.liftToOpen_fac]
  have hφ : φ.comp (algebraMap ℂ W.toAffine.CoordinateRing) = RingHom.id ℂ := by
    apply DFunLike.ext
    intro c
    have h := congrArg Spec.preimage hp
    simpa [φ, Spec.preimage_comp] using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) c
  let φα : W.toAffine.CoordinateRing →ₐ[ℂ] ℂ :=
    { toRingHom := φ, commutes' := fun c => DFunLike.congr_fun hφ c }
  let x := φα (AdjoinRoot.of W.toAffine.polynomial Polynomial.X)
  let y := φα (AdjoinRoot.root W.toAffine.polynomial)
  have hcoeff : φ.comp (AdjoinRoot.of W.toAffine.polynomial) = Polynomial.evalRingHom x := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.evalRingHom]
      change φ (AdjoinRoot.of W.toAffine.polynomial (Polynomial.C c)) =
        Polynomial.eval₂ (RingHom.id ℂ) x (Polynomial.C c)
      rw [Polynomial.eval₂_C]
      change φ ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C (Polynomial.C c))) = c
      rw [AdjoinRoot.mk_C]
      exact DFunLike.congr_fun hφ c
    · simp [x, φα]
  have hxy : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [W, WeierstrassCurve.ofJ1728]
    apply sub_eq_zero.mp
    have hroot := congrArg φ (AdjoinRoot.eval₂_root W.toAffine.polynomial)
    rw [Polynomial.hom_eval₂] at hroot
    rw [hcoeff] at hroot
    rw [map_zero] at hroot
    rw [Polynomial.eval₂_evalRingHom,
      WeierstrassCurve.Affine.evalEval_polynomial] at hroot
    simpa [W, WeierstrassCurve.ofJ1728, y, φα] using hroot
  refine ⟨x, y, hxy, ?_⟩
  have hφeval : φ = affineEval x y hxy := by
    apply DFunLike.ext
    intro a
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [← AdjoinRoot.aeval_eq]
    change φ (Polynomial.eval₂ (AdjoinRoot.of W.toAffine.polynomial)
      (AdjoinRoot.root W.toAffine.polynomial) g) = _
    rw [Polynomial.hom_eval₂, hcoeff]
    change Polynomial.eval₂ (Polynomial.evalRingHom x) y g = _
    rw [AdjoinRoot.aeval_eq, affineEval, AdjoinRoot.lift_mk]
  have hp_eq : p = Spec.map (CommRingCat.ofHom (affineEval x y hxy)) := by
    apply (Spec.homEquiv).injective
    apply CommRingCat.hom_ext
    change φ = (Spec.homEquiv (Spec.map (CommRingCat.ofHom (affineEval x y hxy)))).hom
    simpa using hφeval
  rw [← hp_eq]
  dsimp [p, q]
  simp [zChartMap, Category.assoc, ComplexPoint.liftToOpen_fac]

/-- A complex point in the infinity chart is evaluation at coordinates satisfying
the chart equation. -/
private theorem yChart_factorization (P : ComplexPoint E)
    (hP : P ∈ AlgebraicGeometry.Point.overOpen yChart) :
    ∃ (u v : ℂ) (h : v = u ^ 3 + u * v ^ 2),
      P.left = Spec.map (CommRingCat.ofHom (AdjoinRoot.lift (Polynomial.evalRingHom u) v (by
        rw [Polynomial.eval₂_evalRingHom]
        rw [yAffinePolynomial]
        rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
          Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.evalEval_mul, Polynomial.evalEval_C,
          Polynomial.eval_X, Polynomial.evalEval_pow, Polynomial.evalEval_X]
        linear_combination h))) ≫ yChartMap := by
  let q := ComplexPoint.liftToOpen E yChart P hP
  let p := q ≫ yChartIso.hom
  let ψ : YCoordinateRing →+* ℂ := (Spec.homEquiv p).hom
  have hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ YCoordinateRing)) = 𝟙 (Spec ↧ℂ) := by
    dsimp [p, q]
    rw [← yChartMap_over, ← Category.assoc, yChartMap]
    simp [ComplexPoint.liftToOpen_fac]
  have hψ : ψ.comp (algebraMap ℂ YCoordinateRing) = RingHom.id ℂ := by
    apply DFunLike.ext
    intro c
    have h := congrArg Spec.preimage hp
    simpa [ψ, Spec.preimage_comp] using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) c
  let ψα : YCoordinateRing →ₐ[ℂ] ℂ :=
    { toRingHom := ψ, commutes' := fun c => DFunLike.congr_fun hψ c }
  let u := ψα (AdjoinRoot.of yAffinePolynomial Polynomial.X)
  let v := ψα (AdjoinRoot.root yAffinePolynomial)
  have huv : v = u ^ 3 + u * v ^ 2 := by
    have h := congrArg ψ yChart_equation
    simpa [u, v, ψα] using h
  refine ⟨u, v, huv, ?_⟩
  let ev : YCoordinateRing →+* ℂ := AdjoinRoot.lift (Polynomial.evalRingHom u) v (by
    rw [Polynomial.eval₂_evalRingHom]
    rw [yAffinePolynomial]
    rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
      Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.evalEval_mul, Polynomial.evalEval_C,
      Polynomial.eval_X, Polynomial.evalEval_pow, Polynomial.evalEval_X]
    linear_combination huv)
  have hcoeff : ψ.comp (AdjoinRoot.of yAffinePolynomial) = Polynomial.evalRingHom u := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.evalRingHom]
      change ψ (AdjoinRoot.of yAffinePolynomial (Polynomial.C c)) =
        Polynomial.eval₂ (RingHom.id ℂ) u (Polynomial.C c)
      rw [Polynomial.eval₂_C]
      change ψ ((AdjoinRoot.mk yAffinePolynomial) (Polynomial.C (Polynomial.C c))) = c
      rw [AdjoinRoot.mk_C]
      exact DFunLike.congr_fun hψ c
    · simp [u, ψα]
  have hψev : ψ = ev := by
    apply DFunLike.ext
    intro a
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [← AdjoinRoot.aeval_eq]
    change ψ (Polynomial.eval₂ (AdjoinRoot.of yAffinePolynomial)
      (AdjoinRoot.root yAffinePolynomial) g) = _
    rw [Polynomial.hom_eval₂, hcoeff]
    change Polynomial.eval₂ (Polynomial.evalRingHom u) v g = _
    rw [AdjoinRoot.aeval_eq]
    simp [ev]
  have hp_eq : p = Spec.map (CommRingCat.ofHom ev) := by
    apply (Spec.homEquiv).injective
    apply CommRingCat.hom_ext
    change ψ = (Spec.homEquiv (Spec.map (CommRingCat.ofHom ev))).hom
    simpa using hψev
  rw [← hp_eq]
  dsimp [p, q]
  simp [yChartMap, Category.assoc, ComplexPoint.liftToOpen_fac]

/-- The only infinity-chart point with vanishing second coordinate is its origin. -/
private theorem yChart_zero_second_coordinate {u v : ℂ}
    (h : v = u ^ 3 + u * v ^ 2) (hv : v = 0) : u = 0 := by
  rw [hv] at h
  have hu : u ^ 3 = 0 := by simpa using h.symm
  by_contra hne
  exact (pow_ne_zero 3 hne) hu

private theorem yChart_point_eq_infinity_of_second_zero (P : ComplexPoint E)
    (hP : P ∈ AlgebraicGeometry.Point.overOpen yChart)
    (u v : ℂ) (h : v = u ^ 3 + u * v ^ 2)
    (hfac : P.left = Spec.map (CommRingCat.ofHom (AdjoinRoot.lift
      (Polynomial.evalRingHom u) v (by
        rw [Polynomial.eval₂_evalRingHom]
        rw [yAffinePolynomial]
        rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
          Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.evalEval_mul, Polynomial.evalEval_C,
          Polynomial.eval_X, Polynomial.evalEval_pow, Polynomial.evalEval_X]
        linear_combination h))) ≫ yChartMap)
    (hv : v = 0) : P = Over.homMk infinity infinity_over := by
  have hu : u = 0 := yChart_zero_second_coordinate h hv
  have hscalar : infinityCoordinates.comp (algebraMap ℂ YCoordinateRing) = RingHom.id ℂ := by
    have hp : Spec.map (CommRingCat.ofHom infinityCoordinates) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ YCoordinateRing)) = 𝟙 (Spec ↧ℂ) := by
      rw [← yChartMap_over, ← Category.assoc, infinity_chart, infinity_over]
    apply DFunLike.ext
    intro c
    have h' := congrArg Spec.preimage hp
    simpa [Spec.preimage_comp] using
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') c
  have hcoeff : infinityCoordinates.comp (AdjoinRoot.of yAffinePolynomial) =
      Polynomial.evalRingHom (0 : ℂ) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.evalRingHom]
      change infinityCoordinates (AdjoinRoot.of yAffinePolynomial (Polynomial.C c)) =
        Polynomial.eval₂ (RingHom.id ℂ) 0 (Polynomial.C c)
      rw [Polynomial.eval₂_C]
      change infinityCoordinates ((AdjoinRoot.mk yAffinePolynomial)
        (Polynomial.C (Polynomial.C c))) = c
      rw [AdjoinRoot.mk_C]
      exact DFunLike.congr_fun hscalar c
    · simp only [RingHom.comp_apply, Polynomial.evalRingHom]
      change infinityCoordinates (AdjoinRoot.of yAffinePolynomial Polynomial.X) = _
      simpa using infinityCoordinates_values.1
  have heval : AdjoinRoot.lift (Polynomial.evalRingHom u) v (by
        rw [Polynomial.eval₂_evalRingHom]
        rw [yAffinePolynomial]
        rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
          Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.evalEval_mul, Polynomial.evalEval_C,
          Polynomial.eval_X, Polynomial.evalEval_pow, Polynomial.evalEval_X]
        linear_combination h) = infinityCoordinates := by
    apply DFunLike.ext
    intro a
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [← AdjoinRoot.aeval_eq]
    change (AdjoinRoot.lift (Polynomial.evalRingHom u) v _)
        (Polynomial.eval₂ (AdjoinRoot.of yAffinePolynomial)
          (AdjoinRoot.root yAffinePolynomial) g) =
      infinityCoordinates (Polynomial.eval₂ (AdjoinRoot.of yAffinePolynomial)
        (AdjoinRoot.root yAffinePolynomial) g)
    rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, hcoeff]
    rw [infinityCoordinates_values.2]
    simp [hu, hv]
  apply Over.OverMorphism.ext
  change P.left = infinity
  rw [hfac, ← infinity_chart]
  rw [heval]

/-- The complex point of `E` represented by an affine Weierstrass point.
This packages the coordinate evaluation map as a point over `Spec ℂ`. -/
private noncomputable def affineComplexPoint (x y : ℂ) (h : W.toAffine.Equation x y) :
    ComplexPoint E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (affineEval x y h)) ≫ zChartMap) (by
    rw [Category.assoc, zChartMap_over, ← Spec.map_comp]
    have hbase : (affineEval x y h).comp (algebraMap ℂ W.toAffine.CoordinateRing) =
        RingHom.id ℂ := by
      ext c
      change (affineEval x y h)
        ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C (Polynomial.C c))) = c
      simp [affineEval]
    change Spec.map (CommRingCat.ofHom
      ((affineEval x y h).comp (algebraMap ℂ W.toAffine.CoordinateRing))) = _
    rw [hbase]
    exact Spec.map_id _)

private theorem affineComplexPoint_left (x y : ℂ) (h : W.toAffine.Equation x y) :
    (affineComplexPoint x y h).left =
      Spec.map (CommRingCat.ofHom (affineEval x y h)) ≫ zChartMap :=
  rfl

private noncomputable def zChartOver :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing))) ⟶ E :=
  Over.homMk zChartMap zChartMap_over

private noncomputable def yChartOver :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ YCoordinateRing))) ⟶ E :=
  Over.homMk yChartMap yChartMap_over

private theorem affineComplexPoint_mem_zChart (x y : ℂ) (h : W.toAffine.Equation x y) :
    affineComplexPoint x y h ∈ AlgebraicGeometry.Point.overOpen zChart := by
  let p : ComplexPoint (Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing)))) :=
    (ComplexPoint.affineSpecEquiv W.toAffine.CoordinateRing).symm
      { toRingHom := affineEval x y h
        commutes' := by
          intro c
          change (affineEval x y h)
            ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C (Polynomial.C c))) = c
          simp [affineEval] }
  have hp : affineComplexPoint x y h = Point.map zChartOver p := by
    apply Over.OverMorphism.ext
    rfl
  rw [hp, Point.mem_overOpen_map_iff]
  have hpre : zChartOver.left ⁻¹ᵁ zChart = ⊤ := by
    change zChartMap ⁻¹ᵁ zChart = ⊤
    rw [zChartMap, Scheme.Hom.comp_preimage, zChart.ι_preimage_self]
    simp
  rw [hpre]
  trivial

private theorem zChart_point_eq_affineComplexPoint (P : ComplexPoint E)
    (hP : P ∈ AlgebraicGeometry.Point.overOpen zChart) :
    ∃ (x y : ℂ) (h : W.toAffine.Equation x y), P = affineComplexPoint x y h := by
  obtain ⟨x, y, h, hPxy⟩ := zChart_factorization P hP
  refine ⟨x, y, h, ?_⟩
  apply Over.OverMorphism.ext
  rw [affineComplexPoint_left]
  exact hPxy

/-- Every complex point other than infinity belongs to the affine chart. -/
private theorem mem_zChart_of_ne_infinity (P : ComplexPoint E)
    (hP : P ≠ Over.homMk infinity infinity_over) :
    P ∈ AlgebraicGeometry.Point.overOpen zChart := by
  have hc : P ∈ AlgebraicGeometry.Point.overOpen zChart ∨
      P ∈ AlgebraicGeometry.Point.overOpen yChart := by
    have h : P ∈ AlgebraicGeometry.Point.overOpen (zChart ⊔ yChart) := by
      rw [charts_cover]
      trivial
    exact h
  rcases hc with hz | hy
  · exact hz
  · obtain ⟨u, v, huv, hfac⟩ := yChart_factorization P hy
    by_contra hnz
    have hv : v = 0 := by
      rw [← not_ne_iff]
      intro hv
      apply hnz
      change P.left.base (IsLocalRing.closedPoint ℂ) ∈ zChart
      rw [hfac]
      change (Spec.map (CommRingCat.ofHom (AdjoinRoot.lift
        (Polynomial.evalRingHom u) v _))).base (IsLocalRing.closedPoint ℂ) ∈
          yChartMap ⁻¹ᵁ zChart
      rw [yChartMap_preimage_z]
      have hev : Polynomial.eval₂ (Polynomial.evalRingHom u) v yAffinePolynomial = 0 := by
        rw [Polynomial.eval₂_evalRingHom]
        rw [yAffinePolynomial]
        rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
          Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.evalEval_mul, Polynomial.evalEval_C,
          Polynomial.eval_X, Polynomial.evalEval_pow, Polynomial.evalEval_X]
        linear_combination huv
      change PrimeSpectrum.comap (AdjoinRoot.lift (Polynomial.evalRingHom u) v hev)
        (IsLocalRing.closedPoint ℂ) ∈
          PrimeSpectrum.basicOpen (AdjoinRoot.root yAffinePolynomial)
      rw [PrimeSpectrum.mem_basicOpen]
      simpa [IsLocalRing.closedPoint, Ideal.mem_comap] using hv
    exact hP (yChart_point_eq_infinity_of_second_zero P hy u v huv hfac hv)

private theorem infinityPoint_not_mem_zChart :
    Over.homMk infinity infinity_over ∉ AlgebraicGeometry.Point.overOpen zChart := by
  intro h
  change infinity.base (IsLocalRing.closedPoint ℂ) ∈ zChart at h
  have h' : IsLocalRing.closedPoint ℂ ∈ infinity ⁻¹ᵁ zChart := h
  rw [infinity_zChart] at h'
  exact h'

private theorem affineComplexPoint_ne_infinity (x y : ℂ) (h : W.toAffine.Equation x y) :
    affineComplexPoint x y h ≠ Over.homMk infinity infinity_over := by
  intro heq
  apply infinityPoint_not_mem_zChart
  rw [← heq]
  exact affineComplexPoint_mem_zChart x y h

private theorem affineComplexPoint_coordinates {x y x' y' : ℂ}
    {h : W.toAffine.Equation x y} {h' : W.toAffine.Equation x' y'}
    (heq : affineComplexPoint x y h = affineComplexPoint x' y' h') :
    x = x' ∧ y = y' := by
  have hleft := congrArg Over.Hom.left heq
  rw [affineComplexPoint_left, affineComplexPoint_left] at hleft
  have hspec : Spec.map (CommRingCat.ofHom (affineEval x y h)) =
      Spec.map (CommRingCat.ofHom (affineEval x' y' h')) := by
    rw [zChartMap] at hleft
    have hchart : Spec.map (CommRingCat.ofHom (affineEval x y h)) ≫ zChartIso.inv =
        Spec.map (CommRingCat.ofHom (affineEval x' y' h')) ≫ zChartIso.inv := by
      rw [← cancel_mono zChart.ι]
      simpa [Category.assoc] using hleft
    rw [← cancel_mono zChartIso.inv]
    exact hchart
  have hring : affineEval x y h = affineEval x' y' h' := by
    have hp := congrArg (fun f ↦ (Spec.homEquiv f).hom) hspec
    simpa [Spec.homEquiv_apply] using hp
  constructor
  · have hx := DFunLike.congr_fun hring
        (AdjoinRoot.of W.toAffine.polynomial Polynomial.X)
    simpa [affineEval] using hx
  · have hy := DFunLike.congr_fun hring (AdjoinRoot.root W.toAffine.polynomial)
    simpa [affineEval] using hy

/-- The point of the cubic represented by a Mathlib affine Weierstrass point. -/
private noncomputable def complexPointOfAffine : W.toAffine.Point → ComplexPoint E
  | .zero => Over.homMk infinity infinity_over
  | .some x y h => affineComplexPoint x y h.1

private theorem complexPointOfAffine_injective : Function.Injective complexPointOfAffine := by
  intro A B hAB
  cases A with
  | zero =>
      cases B with
      | zero => rfl
      | some x y h => exact (affineComplexPoint_ne_infinity x y h.1 hAB.symm).elim
  | some x y h =>
      cases B with
      | zero => exact (affineComplexPoint_ne_infinity x y h.1 hAB).elim
      | some x' y' h' =>
          obtain ⟨rfl, rfl⟩ := affineComplexPoint_coordinates hAB
          rfl

private theorem complexPointOfAffine_surjective : Function.Surjective complexPointOfAffine := by
  intro P
  by_cases hP : P = Over.homMk infinity infinity_over
  · exact ⟨.zero, hP.symm⟩
  · obtain ⟨x, y, hxy, rfl⟩ :=
      zChart_point_eq_affineComplexPoint P (mem_zChart_of_ne_infinity P hP)
    exact ⟨.some x y (W_equation_iff_nonsingular.mp hxy), rfl⟩

/-! Coordinate involutions used to construct the global negation morphism. -/

private noncomputable def zNegCoordinates :
    W.toAffine.CoordinateRing →+* W.toAffine.CoordinateRing :=
  AdjoinRoot.lift (AdjoinRoot.of W.toAffine.polynomial)
    (- AdjoinRoot.root W.toAffine.polynomial) (by
      let x := AdjoinRoot.of W.toAffine.polynomial Polynomial.X
      let y := AdjoinRoot.root W.toAffine.polynomial
      let f : ℂ →+* W.toAffine.CoordinateRing := algebraMap ℂ W.toAffine.CoordinateRing
      have hcoeff : AdjoinRoot.of W.toAffine.polynomial = Polynomial.eval₂RingHom f x := by
        apply Polynomial.ringHom_ext
        · intro c
          simp [x, f, AdjoinRoot.algebraMap_eq']
        · simp [x]
      have hr := AdjoinRoot.eval₂_root W.toAffine.polynomial
      rw [hcoeff, Polynomial.eval₂_eval₂RingHom_apply] at hr ⊢
      have hxy : (W.map f).toAffine.Equation x y := by
        rw [WeierstrassCurve.Affine.Equation,
          WeierstrassCurve.Affine.map_polynomial]
        exact hr
      have ha1 : (W.map f).toAffine.a₁ = 0 := by
        change f W.a₁ = 0
        rw [show W.a₁ = 0 by simp [W, WeierstrassCurve.ofJ1728], map_zero]
      have ha2 : (W.map f).toAffine.a₂ = 0 := by
        change f W.a₂ = 0
        rw [show W.a₂ = 0 by simp [W, WeierstrassCurve.ofJ1728], map_zero]
      have ha3 : (W.map f).toAffine.a₃ = 0 := by
        change f W.a₃ = 0
        rw [show W.a₃ = 0 by simp [W, WeierstrassCurve.ofJ1728], map_zero]
      have ha4 : (W.map f).toAffine.a₄ = 1 := by
        change f W.a₄ = 1
        rw [show W.a₄ = 1 by simp [W, WeierstrassCurve.ofJ1728], map_one]
      have ha6 : (W.map f).toAffine.a₆ = 0 := by
        change f W.a₆ = 0
        rw [show W.a₆ = 0 by simp [W, WeierstrassCurve.ofJ1728], map_zero]
      have hn : (W.map f).toAffine.Equation x (-y) := by
        rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
        rw [ha1, ha2, ha3, ha4, ha6] at hxy ⊢
        simpa using hxy
      rw [← WeierstrassCurve.Affine.map_polynomial]
      exact hn)

private noncomputable def yNegCoordinates : YCoordinateRing →+* YCoordinateRing :=
  let u := AdjoinRoot.of yAffinePolynomial Polynomial.X
  let v := AdjoinRoot.root yAffinePolynomial
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℂ YCoordinateRing) (-u)) (-v) (by
    have heval (a b : YCoordinateRing) :
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ YCoordinateRing) a)
      b yAffinePolynomial = b - a ^ 3 - a * b ^ 2 := by
      simp [yAffinePolynomial, Polynomial.eval₂_eval₂RingHom_apply,
        Polynomial.evalEval_C]
    rw [heval]
    have h := yChart_equation
    dsimp [u, v]
    linear_combination -h)

private theorem zNegCoordinates_X :
    zNegCoordinates (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) =
      AdjoinRoot.of W.toAffine.polynomial Polynomial.X := by
  simp [zNegCoordinates]

private theorem zNegCoordinates_Y :
    zNegCoordinates (AdjoinRoot.root W.toAffine.polynomial) =
      -AdjoinRoot.root W.toAffine.polynomial := by
  simp [zNegCoordinates]

private theorem yNegCoordinates_U :
    yNegCoordinates (AdjoinRoot.of yAffinePolynomial Polynomial.X) =
      -AdjoinRoot.of yAffinePolynomial Polynomial.X := by
  simp [yNegCoordinates]

private theorem yNegCoordinates_V :
    yNegCoordinates (AdjoinRoot.root yAffinePolynomial) =
      -AdjoinRoot.root yAffinePolynomial := by
  simp [yNegCoordinates]

private theorem zNegCoordinates_over :
    zNegCoordinates.comp (algebraMap ℂ W.toAffine.CoordinateRing) =
      algebraMap ℂ W.toAffine.CoordinateRing := by
  ext c
  change zNegCoordinates ((AdjoinRoot.mk W.toAffine.polynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [zNegCoordinates, AdjoinRoot.algebraMap_eq']

private theorem yNegCoordinates_over :
    yNegCoordinates.comp (algebraMap ℂ YCoordinateRing) =
      algebraMap ℂ YCoordinateRing := by
  ext c
  change yNegCoordinates ((AdjoinRoot.mk yAffinePolynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [yNegCoordinates, AdjoinRoot.algebraMap_eq']

private noncomputable def zChartNeg : zChart.toScheme ⟶ E.left :=
  zChartIso.hom ≫ Spec.map (CommRingCat.ofHom zNegCoordinates) ≫ zChartMap

private noncomputable def yChartNeg : yChart.toScheme ⟶ E.left :=
  yChartIso.hom ≫ Spec.map (CommRingCat.ofHom yNegCoordinates) ≫ yChartMap

private theorem zChartNeg_over : zChartNeg ≫ E.hom = zChart.ι ≫ E.hom := by
  rw [zChartNeg, Category.assoc, Category.assoc, zChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing) ≫
      CommRingCat.ofHom zNegCoordinates =
        CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing) by
    apply CommRingCat.hom_ext
    exact zNegCoordinates_over]
  rw [← zChartMap_over]
  simp [zChartMap, Category.assoc]

private theorem yChartNeg_over : yChartNeg ≫ E.hom = yChart.ι ≫ E.hom := by
  rw [yChartNeg, Category.assoc, Category.assoc, yChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ YCoordinateRing) ≫
      CommRingCat.ofHom yNegCoordinates =
        CommRingCat.ofHom (algebraMap ℂ YCoordinateRing) by
    apply CommRingCat.hom_ext
    exact yNegCoordinates_over]
  rw [← yChartMap_over]
  simp [yChartMap, Category.assoc]

private noncomputable def yOverlapNeg :
    Localization.Away (AdjoinRoot.root yAffinePolynomial) →+*
      Localization.Away (AdjoinRoot.root yAffinePolynomial) :=
  IsLocalization.Away.lift
    (S := Localization.Away (AdjoinRoot.root yAffinePolynomial))
    (P := Localization.Away (AdjoinRoot.root yAffinePolynomial))
    (AdjoinRoot.root yAffinePolynomial)
    (g := (algebraMap YCoordinateRing
      (Localization.Away (AdjoinRoot.root yAffinePolynomial))).comp yNegCoordinates) (by
      rw [RingHom.comp_apply, yNegCoordinates_V]
      simpa only [map_neg] using (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (AdjoinRoot.root yAffinePolynomial))
        (AdjoinRoot.root yAffinePolynomial)).neg)

private theorem yOverlapNeg_algebraMap (a : YCoordinateRing) :
    yOverlapNeg (algebraMap YCoordinateRing
      (Localization.Away (AdjoinRoot.root yAffinePolynomial)) a) =
      algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial)) (yNegCoordinates a) := by
  simp [yOverlapNeg, IsLocalization.Away.lift_eq]

private theorem yOverlapNeg_invSelf :
    yOverlapNeg (IsLocalization.Away.invSelf (AdjoinRoot.root yAffinePolynomial)) =
      -IsLocalization.Away.invSelf (AdjoinRoot.root yAffinePolynomial) := by
  let a : Localization.Away (AdjoinRoot.root yAffinePolynomial) :=
    algebraMap YCoordinateRing _ (AdjoinRoot.root yAffinePolynomial)
  have ha : IsUnit a := IsLocalization.Away.algebraMap_isUnit _
  apply ha.mul_left_cancel
  have hm : (-a) * yOverlapNeg
      (IsLocalization.Away.invSelf (AdjoinRoot.root yAffinePolynomial)) = 1 := by
    calc
      (-a) * yOverlapNeg (IsLocalization.Away.invSelf
          (AdjoinRoot.root yAffinePolynomial)) =
          yOverlapNeg a * yOverlapNeg (IsLocalization.Away.invSelf
            (AdjoinRoot.root yAffinePolynomial)) := by
            rw [yOverlapNeg_algebraMap, yNegCoordinates_V, map_neg]
      _ = yOverlapNeg (a * IsLocalization.Away.invSelf
          (AdjoinRoot.root yAffinePolynomial)) := (map_mul _ _ _).symm
      _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
  calc
    a * yOverlapNeg (IsLocalization.Away.invSelf
        (AdjoinRoot.root yAffinePolynomial)) = -1 := by linear_combination -hm
    _ = a * (-IsLocalization.Away.invSelf
        (AdjoinRoot.root yAffinePolynomial)) := by
      rw [mul_neg, IsLocalization.Away.mul_invSelf]

private theorem yToZCoordinates_over :
    yToZCoordinates.comp (algebraMap ℂ W.toAffine.CoordinateRing) =
      algebraMap ℂ (Localization.Away (AdjoinRoot.root yAffinePolynomial)) := by
  have h := congrArg (fun f : Spec ↧(Localization.Away
      (AdjoinRoot.root yAffinePolynomial)) ⟶ E.left ↦ f ≫ E.hom)
    transition_agreement_y
  simp only [Category.assoc, zChartMap_over, yChartMap_over, ← Spec.map_comp] at h
  have hr := congrArg (fun f ↦ (Spec.homEquiv f).hom) h
  apply RingHom.ext
  intro c
  have hc := DFunLike.congr_fun hr c
  calc
    yToZCoordinates ((algebraMap ℂ W.toAffine.CoordinateRing) c) =
        (algebraMap YCoordinateRing _)
          ((algebraMap ℂ YCoordinateRing) c) := by
            simpa [Spec.homEquiv_apply] using hc
    _ = (algebraMap ℂ _) c := by
      exact DFunLike.congr_fun
        (IsScalarTower.algebraMap_eq ℂ YCoordinateRing
          (Localization.Away (AdjoinRoot.root yAffinePolynomial))) c

private theorem yOverlapNeg_transition :
    yOverlapNeg.comp yToZCoordinates = yToZCoordinates.comp zNegCoordinates := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      rw [show zNegCoordinates
          ((AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C c)) =
          (AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C c) by
        simp [zNegCoordinates]]
      change yOverlapNeg (yToZCoordinates
          ((AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C c))) =
        yToZCoordinates ((AdjoinRoot.of W.toAffine.polynomial) (Polynomial.C c))
      change yOverlapNeg (yToZCoordinates (algebraMap ℂ _ c)) =
        yToZCoordinates (algebraMap ℂ _ c)
      change yOverlapNeg ((yToZCoordinates.comp
        (algebraMap ℂ W.toAffine.CoordinateRing)) c) =
          (yToZCoordinates.comp (algebraMap ℂ W.toAffine.CoordinateRing)) c
      rw [yToZCoordinates_over]
      calc
        yOverlapNeg ((algebraMap ℂ _) c) =
            yOverlapNeg ((algebraMap YCoordinateRing _)
              ((algebraMap ℂ YCoordinateRing) c)) := by
                congr 1
        _ = (algebraMap YCoordinateRing _)
            (yNegCoordinates ((algebraMap ℂ YCoordinateRing) c)) :=
              yOverlapNeg_algebraMap _
        _ = (algebraMap YCoordinateRing _)
            ((algebraMap ℂ YCoordinateRing) c) := by
              congr 1
              simp [yNegCoordinates, AdjoinRoot.algebraMap_eq']
        _ = (algebraMap ℂ _) c := DFunLike.congr_fun
          (IsScalarTower.algebraMap_eq ℂ YCoordinateRing
            (Localization.Away (AdjoinRoot.root yAffinePolynomial))) c
    · simp [zNegCoordinates_X, yToZCoordinates_x, yOverlapNeg_algebraMap,
        yOverlapNeg_invSelf, yNegCoordinates_U]
  · simp [zNegCoordinates_Y, yToZCoordinates_y, yOverlapNeg_invSelf]

private theorem chartNeg_agree_on_yOverlap :
    Spec.map (CommRingCat.ofHom yToZCoordinates) ≫ zChartIso.inv ≫ zChartNeg =
      Spec.map (CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial)))) ≫
          yChartIso.inv ≫ yChartNeg := by
  rw [zChartNeg, yChartNeg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [show CommRingCat.ofHom zNegCoordinates ≫ CommRingCat.ofHom yToZCoordinates =
      CommRingCat.ofHom yToZCoordinates ≫ CommRingCat.ofHom yOverlapNeg by
    apply CommRingCat.hom_ext
    exact yOverlapNeg_transition.symm]
  rw [show CommRingCat.ofHom yNegCoordinates ≫
      CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial))) =
      CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial))) ≫
          CommRingCat.ofHom yOverlapNeg by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (yOverlapNeg_algebraMap a).symm]
  rw [Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [transition_agreement_y]

private noncomputable def yOverlapToE :
    Spec ↧(Localization.Away (AdjoinRoot.root yAffinePolynomial)) ⟶ E.left :=
  Spec.map (CommRingCat.ofHom (algebraMap YCoordinateRing
    (Localization.Away (AdjoinRoot.root yAffinePolynomial)))) ≫ yChartMap

private instance : IsOpenImmersion yChartMap := by
  dsimp [yChartMap]
  infer_instance

private instance : IsOpenImmersion yOverlapToE := by
  dsimp [yOverlapToE]
  infer_instance

private theorem yOverlapToE_opensRange :
    yOverlapToE.opensRange = zChart ⊓ yChart := by
  change (Spec.map (CommRingCat.ofHom (algebraMap YCoordinateRing
    (Localization.Away (AdjoinRoot.root yAffinePolynomial)))) ≫ yChartMap).opensRange = _
  rw [Scheme.Hom.opensRange_comp,
    Scheme.Hom.opensRange_localizationAway
      (R := CommRingCat.of YCoordinateRing) (AdjoinRoot.root yAffinePolynomial),
    ← yChartMap_preimage_z,
    Scheme.Hom.image_preimage_eq_opensRange_inf]
  have hy : yChartMap.opensRange = yChart := by
    change (yChartIso.inv ≫ yChart.ι).opensRange = yChart
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    simp
  rw [hy, inf_comm]

private noncomputable def yOverlapIso :
    Spec ↧(Localization.Away (AdjoinRoot.root yAffinePolynomial)) ≅
      (zChart ⊓ yChart).toScheme :=
  IsOpenImmersion.isoOfRangeEq yOverlapToE (zChart ⊓ yChart).ι (by
    rw [← Scheme.Hom.coe_opensRange, yOverlapToE_opensRange,
      Scheme.Opens.range_ι])

private theorem yOverlapIso_hom_ι :
    yOverlapIso.hom ≫ (zChart ⊓ yChart).ι = yOverlapToE :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem yOverlapIso_hom_to_yChart :
    yOverlapIso.hom ≫ E.left.homOfLE inf_le_right =
      Spec.map (CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial)))) ≫ yChartIso.inv := by
  rw [← cancel_mono yChart.ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, yOverlapIso_hom_ι]
  rfl

private theorem yOverlapIso_hom_to_zChart :
    yOverlapIso.hom ≫ E.left.homOfLE inf_le_left =
      Spec.map (CommRingCat.ofHom yToZCoordinates) ≫ zChartIso.inv := by
  rw [← cancel_mono zChart.ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, yOverlapIso_hom_ι]
  change yOverlapToE = Spec.map (CommRingCat.ofHom yToZCoordinates) ≫ zChartMap
  exact transition_agreement_y.symm

private theorem chartNeg_agree :
    E.left.homOfLE inf_le_left ≫ zChartNeg =
      E.left.homOfLE inf_le_right ≫ yChartNeg := by
  rw [← cancel_epi yOverlapIso.hom]
  rw [← Category.assoc, yOverlapIso_hom_to_zChart,
    ← Category.assoc, yOverlapIso_hom_to_yChart]
  exact chartNeg_agree_on_yOverlap

private theorem chartNeg_pullback :
    pullback.fst zChart.ι yChart.ι ≫ zChartNeg =
      pullback.snd zChart.ι yChart.ι ≫ yChartNeg := by
  rw [← cancel_epi (isPullback_opens_inf zChart yChart).isoPullback.hom]
  simpa [Category.assoc] using chartNeg_agree

private theorem chartNeg_pullback_symm :
    pullback.fst yChart.ι zChart.ι ≫ yChartNeg =
      pullback.snd yChart.ι zChart.ι ≫ zChartNeg := by
  rw [← cancel_epi (pullbackSymmetry zChart.ι yChart.ι).hom]
  simpa [Category.assoc] using chartNeg_pullback.symm

private noncomputable abbrev negCoverOpen : Bool → E.left.Opens
  | false => zChart
  | true => yChart

private theorem negCoverOpen_isCover : TopologicalSpace.IsOpenCover negCoverOpen := by
  change (⨆ b, negCoverOpen b) = ⊤
  rw [iSup_bool_eq]
  change yChart ⊔ zChart = ⊤
  rw [sup_comm, charts_cover]

private noncomputable abbrev negCover : E.left.OpenCover :=
  E.left.openCoverOfIsOpenCover negCoverOpen negCoverOpen_isCover

private noncomputable abbrev negLocal : (b : Bool) → negCover.X b ⟶ E.left
  | false => zChartNeg
  | true => yChartNeg

private theorem negLocal_compatible_ff :
    pullback.fst (negCover.f false) (negCover.f false) ≫ negLocal false =
      pullback.snd (negCover.f false) (negCover.f false) ≫ negLocal false := by
  have h : pullback.fst zChart.ι zChart.ι = pullback.snd zChart.ι zChart.ι :=
    (cancel_mono zChart.ι).mp pullback.condition
  exact congrArg (fun f ↦ f ≫ zChartNeg) h

private theorem negLocal_compatible_ft :
    pullback.fst (negCover.f false) (negCover.f true) ≫ negLocal false =
      pullback.snd (negCover.f false) (negCover.f true) ≫ negLocal true := by
  exact chartNeg_pullback

private theorem negLocal_compatible_tf :
    pullback.fst (negCover.f true) (negCover.f false) ≫ negLocal true =
      pullback.snd (negCover.f true) (negCover.f false) ≫ negLocal false := by
  exact chartNeg_pullback_symm

private theorem negLocal_compatible_tt :
    pullback.fst (negCover.f true) (negCover.f true) ≫ negLocal true =
      pullback.snd (negCover.f true) (negCover.f true) ≫ negLocal true := by
  have h : pullback.fst yChart.ι yChart.ι = pullback.snd yChart.ι yChart.ι :=
    (cancel_mono yChart.ι).mp pullback.condition
  exact congrArg (fun f ↦ f ≫ yChartNeg) h

private theorem negLocal_compatible (b c : Bool) :
    pullback.fst (negCover.f b) (negCover.f c) ≫ negLocal b =
      pullback.snd (negCover.f b) (negCover.f c) ≫ negLocal c := by
  exact Bool.rec (Bool.rec negLocal_compatible_ff negLocal_compatible_ft c)
    (Bool.rec negLocal_compatible_tf negLocal_compatible_tt c) b

private noncomputable def cubicNeg : E.left ⟶ E.left :=
  negCover.glueMorphisms negLocal negLocal_compatible

private theorem zChart_cubicNeg : zChart.ι ≫ cubicNeg = zChartNeg := by
  exact negCover.ι_glueMorphisms negLocal negLocal_compatible false

private theorem yChart_cubicNeg : yChart.ι ≫ cubicNeg = yChartNeg := by
  exact negCover.ι_glueMorphisms negLocal negLocal_compatible true

private theorem cubicNeg_over : cubicNeg ≫ E.hom = E.hom := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hx : x ∈ zChart ∨ x ∈ yChart := by
    have h : x ∈ zChart ⊔ yChart := by rw [charts_cover]; trivial
    exact h
  rcases hx with hx | hx
  · refine ⟨zChart, hx, ?_⟩
    rw [← Category.assoc, zChart_cubicNeg, zChartNeg_over]
  · refine ⟨yChart, hx, ?_⟩
    rw [← Category.assoc, yChart_cubicNeg, yChartNeg_over]

private noncomputable def cubicNegOver : E ⟶ E :=
  Over.homMk cubicNeg cubicNeg_over

private theorem yChartMap_cubicNeg :
    yChartMap ≫ cubicNeg =
      Spec.map (CommRingCat.ofHom yNegCoordinates) ≫ yChartMap := by
  calc
    yChartMap ≫ cubicNeg = yChartIso.inv ≫ (yChart.ι ≫ cubicNeg) := by rfl
    _ = yChartIso.inv ≫ yChartNeg := by rw [yChart_cubicNeg]
    _ = Spec.map (CommRingCat.ofHom yNegCoordinates) ≫ yChartMap := by
      simp [yChartNeg, Category.assoc]

private theorem zChartMap_cubicNeg :
    zChartMap ≫ cubicNeg =
      Spec.map (CommRingCat.ofHom zNegCoordinates) ≫ zChartMap := by
  calc
    zChartMap ≫ cubicNeg = zChartIso.inv ≫ (zChart.ι ≫ cubicNeg) := by rfl
    _ = zChartIso.inv ≫ zChartNeg := by rw [zChart_cubicNeg]
    _ = Spec.map (CommRingCat.ofHom zNegCoordinates) ≫ zChartMap := by
      simp [zChartNeg, Category.assoc]

private theorem neg_equation {x y : ℂ} (h : W.toAffine.Equation x y) :
    W.toAffine.Equation x (-y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simpa [W, WeierstrassCurve.ofJ1728] using h

private theorem affineEval_comp_zNegCoordinates (x y : ℂ)
    (h : W.toAffine.Equation x y) :
    (affineEval x y h).comp zNegCoordinates =
      affineEval x (-y) (neg_equation h) := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simp [affineEval, zNegCoordinates, AdjoinRoot.algebraMap_eq']
    · simp [affineEval, zNegCoordinates_X]
  · simp [affineEval, zNegCoordinates_Y]

private theorem affineComplexPoint_cubicNeg (x y : ℂ)
    (h : W.toAffine.Equation x y) :
    (affineComplexPoint x y h).left ≫ cubicNeg =
      (affineComplexPoint x (-y) (neg_equation h)).left := by
  rw [affineComplexPoint_left, affineComplexPoint_left, Category.assoc,
    zChartMap_cubicNeg, ← Category.assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom zNegCoordinates ≫ CommRingCat.ofHom (affineEval x y h) =
      CommRingCat.ofHom (affineEval x (-y) (neg_equation h)) by
    apply CommRingCat.hom_ext
    exact affineEval_comp_zNegCoordinates x y h]

private theorem cubicNeg_infinity : infinity ≫ cubicNeg = infinity := by
  rw [← infinity_chart, Category.assoc]
  rw [yChartMap_cubicNeg]
  simp only [← Category.assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom yNegCoordinates ≫
      CommRingCat.ofHom infinityCoordinates =
      CommRingCat.ofHom infinityCoordinates by
    apply CommRingCat.hom_ext
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        simp [yNegCoordinates, infinityCoordinates, AdjoinRoot.algebraMap_eq']
      · change infinityCoordinates (yNegCoordinates
          (AdjoinRoot.of yAffinePolynomial Polynomial.X)) = _
        rw [yNegCoordinates_U, map_neg, infinityCoordinates_values.1, neg_zero]
        exact infinityCoordinates_values.1.symm
    · change infinityCoordinates (yNegCoordinates
        (AdjoinRoot.root yAffinePolynomial)) = _
      rw [yNegCoordinates_V, map_neg, infinityCoordinates_values.2, neg_zero]
      exact infinityCoordinates_values.2.symm]

/-- Spec S1: the complex points of `E` are Mathlib's points of `W`, compatibly with the charts. -/
theorem exists_isCubicPointEquiv_aux :
    ∃ e : ComplexPoint E ≃ W.toAffine.Point, IsCubicPointEquiv e := by
  let g : W.toAffine.Point ≃ ComplexPoint E :=
    Equiv.ofBijective complexPointOfAffine
      ⟨complexPointOfAffine_injective, complexPointOfAffine_surjective⟩
  refine ⟨g.symm, ?_, ?_⟩
  · intro P hP
    have hP' : P = Over.homMk infinity infinity_over := by
      apply Over.OverMorphism.ext
      exact hP
    rw [hP']
    apply g.injective
    rw [g.apply_symm_apply]
    rfl
  · intro x y h P hP
    have hP' : P = affineComplexPoint x y h.1 := by
      apply Over.OverMorphism.ext
      rw [affineComplexPoint_left]
      exact hP
    rw [hP']
    apply g.injective
    rw [g.apply_symm_apply]
    rfl

/-! Algebraic identities underlying the finite--finite pieces of the addition morphism.

These are stated without divisions.  Consequently they apply directly in the localizations of
the coordinate ring used for the basic-open pieces of the eventual gluing construction. -/

private theorem chord_addition_equation {R : Type*} [CommRing R] {x₁ y₁ x₂ y₂ l : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hl : l * (x₂ - x₁) = y₂ - y₁) (hu : IsUnit (x₂ - x₁)) :
    let x₃ := l ^ 2 - x₁ - x₂
    let y₃ := l * (x₁ - x₃) - y₁
    y₃ ^ 2 = x₃ ^ 3 + x₃ := by
  dsimp
  have hs : l * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1 := by
    apply hu.mul_left_cancel
    linear_combination (y₁ + y₂) * hl + h₂ - h₁
  have hk : l ^ 2 * (x₁ - x₂) - 2 * l * y₁ +
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) = 0 := by
    linear_combination -l * hl - hs
  linear_combination h₁ - (l ^ 2 - 2 * x₁ - x₂) * hk

private theorem tangentChord_addition_equation {R : Type*} [CommRing R] {x₁ y₁ x₂ y₂ l : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hl : l * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1)
    (hu : IsUnit (y₁ + y₂)) :
    let x₃ := l ^ 2 - x₁ - x₂
    let y₃ := l * (x₁ - x₃) - y₁
    y₃ ^ 2 = x₃ ^ 3 + x₃ := by
  dsimp
  have hs : l * (x₂ - x₁) = y₂ - y₁ := by
    apply hu.mul_left_cancel
    linear_combination (x₂ - x₁) * hl + h₁ - h₂
  have hk : l ^ 2 * (x₁ - x₂) - 2 * l * y₁ +
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) = 0 := by
    linear_combination -l * hs - hl
  linear_combination h₁ - (l ^ 2 - 2 * x₁ - x₂) * hk

private theorem chord_tangent_slopes_eq {R : Type*} [CommRing R]
    {x₁ y₁ x₂ y₂ l k : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hl : l * (x₂ - x₁) = y₂ - y₁)
    (hk : k * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1)
    (hu : IsUnit (x₂ - x₁)) (hv : IsUnit (y₁ + y₂)) : l = k := by
  apply hv.mul_right_cancel
  rw [hk]
  apply hu.mul_left_cancel
  linear_combination (y₁ + y₂) * hl + h₂ - h₁

private theorem chord_tangent_outputs_eq {R : Type*} [CommRing R]
    {x₁ y₁ x₂ y₂ l k : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hl : l * (x₂ - x₁) = y₂ - y₁)
    (hk : k * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1)
    (hu : IsUnit (x₂ - x₁)) (hv : IsUnit (y₁ + y₂)) :
    l ^ 2 - x₁ - x₂ = k ^ 2 - x₁ - x₂ ∧
      l * (x₁ - (l ^ 2 - x₁ - x₂)) - y₁ =
        k * (x₁ - (k ^ 2 - x₁ - x₂)) - y₁ := by
  rw [chord_tangent_slopes_eq h₁ h₂ hl hk hu hv]
  exact ⟨rfl, rfl⟩

private theorem reciprocalChord_addition_equation {R : Type*} [CommRing R] {x₁ y₁ x₂ y₂ μ : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hμ : μ * (y₂ - y₁) = x₂ - x₁) (hu : IsUnit (y₂ - y₁)) :
    let A := 1 - μ ^ 2 * (x₁ + x₂)
    let B := -1 + μ ^ 2 * (2 * x₁ + x₂) - μ ^ 3 * y₁
    B ^ 2 = A ^ 3 + μ ^ 4 * A := by
  dsimp
  have hs : μ * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) = y₁ + y₂ := by
    apply hu.mul_left_cancel
    linear_combination (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) * hμ - h₂ + h₁
  have hk : μ ^ 2 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) - 2 * μ * y₁ +
      x₁ - x₂ = 0 := by
    linear_combination μ * hs + hμ
  linear_combination μ ^ 6 * h₁ +
    μ ^ 2 * (2 * μ ^ 2 * x₁ + μ ^ 2 * x₂ - 1) * hk

private theorem reciprocalTangentChord_addition_equation {R : Type*} [CommRing R]
    {x₁ y₁ x₂ y₂ μ : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hμ : μ * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) = y₁ + y₂)
    (hu : IsUnit (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1)) :
    let A := 1 - μ ^ 2 * (x₁ + x₂)
    let B := -1 + μ ^ 2 * (2 * x₁ + x₂) - μ ^ 3 * y₁
    B ^ 2 = A ^ 3 + μ ^ 4 * A := by
  dsimp
  have hs : μ * (y₂ - y₁) = x₂ - x₁ := by
    apply hu.mul_left_cancel
    linear_combination (y₂ - y₁) * hμ + h₂ - h₁
  have hk : μ ^ 2 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) - 2 * μ * y₁ +
      x₁ - x₂ = 0 := by
    linear_combination μ * hμ + hs
  linear_combination μ ^ 6 * h₁ +
    μ ^ 2 * (2 * μ ^ 2 * x₁ + μ ^ 2 * x₂ - 1) * hk

private theorem reciprocal_slopes_eq {R : Type*} [CommRing R]
    {x₁ y₁ x₂ y₂ μ ν : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hμ : μ * (y₂ - y₁) = x₂ - x₁)
    (hν : ν * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) = y₁ + y₂)
    (hu : IsUnit (y₂ - y₁))
    (hv : IsUnit (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1)) : μ = ν := by
  apply hv.mul_right_cancel
  rw [hν]
  apply hu.mul_left_cancel
  linear_combination
    (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) * hμ - h₂ + h₁

private theorem reciprocal_outputs_eq {R : Type*} [CommRing R]
    {x₁ y₁ x₂ y₂ μ ν : R}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂)
    (hμ : μ * (y₂ - y₁) = x₂ - x₁)
    (hν : ν * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1) = y₁ + y₂)
    (hu : IsUnit (y₂ - y₁))
    (hv : IsUnit (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1)) :
    1 - μ ^ 2 * (x₁ + x₂) = 1 - ν ^ 2 * (x₁ + x₂) ∧
      -1 + μ ^ 2 * (2 * x₁ + x₂) - μ ^ 3 * y₁ =
        -1 + ν ^ 2 * (2 * x₁ + x₂) - ν ^ 3 * y₁ := by
  rw [reciprocal_slopes_eq h₁ h₂ hμ hν hu hv]
  exact ⟨rfl, rfl⟩

private theorem reciprocal_coordinates_scale {R : Type*} [CommRing R]
    {x₁ y₁ x₂ l μ : R} (hμ : μ * l = 1) :
    let x₃ := l ^ 2 - x₁ - x₂
    let y₃ := l * (x₁ - x₃) - y₁
    let A := 1 - μ ^ 2 * (x₁ + x₂)
    let B := -1 + μ ^ 2 * (2 * x₁ + x₂) - μ ^ 3 * y₁
    A = μ ^ 2 * x₃ ∧ B = μ ^ 3 * y₃ := by
  dsimp
  constructor
  · linear_combination -(μ * l + 1) * hμ
  · linear_combination
      (-μ ^ 2 * (2 * x₁ + x₂) + (μ * l) ^ 2 + μ * l + 1) * hμ

private theorem reciprocal_y_chart_equation {R : Type*} [CommRing R] (A B μ t : R)
    (hAB : B ^ 2 = A ^ 3 + μ ^ 4 * A) (ht : B * t = 1) :
    μ ^ 3 * t = (μ * A * t) ^ 3 + (μ * A * t) * (μ ^ 3 * t) ^ 2 := by
  apply sub_eq_zero.mp
  calc
    μ ^ 3 * t - ((μ * A * t) ^ 3 + (μ * A * t) * (μ ^ 3 * t) ^ 2) =
        μ ^ 3 * t ^ 3 * (B ^ 2 - A ^ 3 - μ ^ 4 * A) +
          μ ^ 3 * t * (1 - (B * t) ^ 2) := by ring
    _ = 0 := by rw [hAB, ht]; ring
  

private theorem finite_addition_basic_opens_cover {x₁ y₁ x₂ y₂ : ℂ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + x₁) (h₂ : y₂ ^ 2 = x₂ ^ 3 + x₂) :
    x₂ - x₁ ≠ 0 ∨ y₁ + y₂ ≠ 0 ∨ y₂ - y₁ ≠ 0 ∨
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + 1 ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hxx, hys, hyd, hS⟩
  have hx : x₂ = x₁ := sub_eq_zero.mp hxx
  have hy : y₂ = y₁ := sub_eq_zero.mp hyd
  have hy₁ : y₁ = 0 := by
    rw [hy] at hys
    linear_combination (2 : ℂ)⁻¹ * hys
  have hS' : 3 * x₁ ^ 2 + 1 = 0 := by
    rw [hx] at hS
    linear_combination hS
  have hcurve : x₁ * (x₁ ^ 2 + 1) = 0 := by
    rw [hy₁, zero_pow (by norm_num : 2 ≠ 0)] at h₁
    linear_combination -h₁
  rcases mul_eq_zero.mp hcurve with hx₁ | hx₁
  · rw [hx₁] at hS'
    norm_num at hS'
  · have hx₁' : x₁ ^ 2 = -1 := by linear_combination hx₁
    rw [hx₁'] at hS'
    norm_num at hS'

noncomputable section

private abbrev AddA := W.toAffine.CoordinateRing
private def addXCoord : AddA := AdjoinRoot.of W.toAffine.polynomial Polynomial.X
private def addYCoord : AddA := AdjoinRoot.root W.toAffine.polynomial

private theorem addA_relation : addYCoord ^ 2 - addXCoord ^ 3 - addXCoord = 0 := by
  let f : ℂ →+* AddA := algebraMap ℂ AddA
  have hcoeff : AdjoinRoot.of W.toAffine.polynomial =
      Polynomial.eval₂RingHom f addXCoord := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [addXCoord, f, AdjoinRoot.algebraMap_eq']
    · simp [addXCoord]
  have hr := AdjoinRoot.eval₂_root W.toAffine.polynomial
  rw [hcoeff, Polynomial.eval₂_eval₂RingHom_apply] at hr
  have hxy : (W.map f).toAffine.Equation addXCoord addYCoord := by
    rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.map_polynomial]
    exact hr
  rw [WeierstrassCurve.Affine.equation_iff] at hxy
  simp [W, WeierstrassCurve.ofJ1728] at hxy
  linear_combination hxy

private abbrev AddZZ := AddA ⊗[ℂ] AddA
private def addX₁ : AddZZ :=
  (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addXCoord
private def addY₁ : AddZZ :=
  (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addYCoord
private def addX₂ : AddZZ :=
  (Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord
private def addY₂ : AddZZ :=
  (Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addYCoord
private def chordDenom : AddZZ := addX₂ - addX₁
private abbrev ChordRing := Localization.Away chordDenom
private def chordInv : ChordRing := IsLocalization.Away.invSelf chordDenom
private def chordMap (a : AddZZ) : ChordRing := algebraMap AddZZ ChordRing a
private def chordSlope : ChordRing := (chordMap addY₂ - chordMap addY₁) * chordInv
private def chordX : ChordRing := chordSlope ^ 2 - chordMap addX₁ - chordMap addX₂
private def chordY : ChordRing := chordSlope * (chordMap addX₁ - chordX) - chordMap addY₁

private theorem chordMap_relation_left :
    chordMap addY₁ ^ 2 = chordMap addX₁ ^ 3 + chordMap addX₁ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ ChordRing) h
  simp only [map_sub, map_pow, map_zero] at h'
  change (algebraMap AddZZ ChordRing)
      ((Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addYCoord) ^ 2 =
    (algebraMap AddZZ ChordRing)
        ((Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addXCoord) ^ 3 +
      (algebraMap AddZZ ChordRing)
        ((Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addXCoord)
  linear_combination h'

private theorem chordMap_relation_right :
    chordMap addY₂ ^ 2 = chordMap addX₂ ^ 3 + chordMap addX₂ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ ChordRing) h
  simp only [map_sub, map_pow, map_zero] at h'
  change (algebraMap AddZZ ChordRing)
      ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addYCoord) ^ 2 =
    (algebraMap AddZZ ChordRing)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord) ^ 3 +
      (algebraMap AddZZ ChordRing)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord)
  linear_combination h'

private theorem chord_denom_unit : IsUnit (chordMap addX₂ - chordMap addX₁) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨chordInv, ?_⟩
  simpa [chordInv, chordMap, chordDenom, map_sub] using
    (IsLocalization.Away.mul_invSelf chordDenom (S := ChordRing))

private theorem chordSlope_spec :
    chordSlope * (chordMap addX₂ - chordMap addX₁) =
      chordMap addY₂ - chordMap addY₁ := by
  have h : (chordMap addX₂ - chordMap addX₁) * chordInv = 1 := by
    simpa [chordInv, chordMap, chordDenom, map_sub] using
      (IsLocalization.Away.mul_invSelf chordDenom (S := ChordRing))
  calc
    chordSlope * (chordMap addX₂ - chordMap addX₁) =
        (chordMap addY₂ - chordMap addY₁) *
          ((chordMap addX₂ - chordMap addX₁) * chordInv) := by
            simp only [chordSlope]
            ring
    _ = chordMap addY₂ - chordMap addY₁ := by rw [h, mul_one]

private theorem chord_coordinates_equation : chordY ^ 2 = chordX ^ 3 + chordX := by
  exact chord_addition_equation chordMap_relation_left chordMap_relation_right chordSlope_spec
    chord_denom_unit

private def chordCoordinates : AddA →+* ChordRing :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℂ ChordRing) chordX) chordY (by
    have heval (a b : ChordRing) :
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ ChordRing) a) b
          W.toAffine.polynomial = b ^ 2 - a ^ 3 - a := by
      simp [WeierstrassCurve.Affine.polynomial, W, WeierstrassCurve.ofJ1728,
        Polynomial.eval₂_eval₂RingHom_apply, Polynomial.evalEval_C]
      <;> ring
    rw [heval]
    linear_combination chord_coordinates_equation)

private theorem chordCoordinates_X : chordCoordinates addXCoord = chordX := by
  simp [chordCoordinates, addXCoord, AdjoinRoot.lift_of]

private theorem chordCoordinates_Y : chordCoordinates addYCoord = chordY := by
  simp [chordCoordinates, addYCoord]

private theorem chordCoordinates_over :
    chordCoordinates.comp (algebraMap ℂ AddA) = algebraMap ℂ ChordRing := by
  ext c
  change chordCoordinates ((AdjoinRoot.mk W.toAffine.polynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [chordCoordinates, AdjoinRoot.algebraMap_eq']

private def chordLocal : Spec ↧ChordRing ⟶ E.left :=
  Spec.map (CommRingCat.ofHom chordCoordinates) ≫ zChartMap

private theorem chordLocal_over :
    chordLocal ≫ E.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ ChordRing)) := by
  rw [chordLocal, Category.assoc, zChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ AddA) ≫
      CommRingCat.ofHom chordCoordinates =
      CommRingCat.ofHom (algebraMap ℂ ChordRing) by
    apply CommRingCat.hom_ext
    exact chordCoordinates_over]

private def tangentDenom : AddZZ := addY₁ + addY₂
private abbrev TangentRing := Localization.Away tangentDenom
private def tangentInv : TangentRing := IsLocalization.Away.invSelf tangentDenom
private def tangentMap (a : AddZZ) : TangentRing := algebraMap AddZZ TangentRing a
private def tangentSlope : TangentRing :=
  (tangentMap addX₁ ^ 2 + tangentMap addX₁ * tangentMap addX₂ +
    tangentMap addX₂ ^ 2 + 1) * tangentInv
private def tangentX : TangentRing :=
  tangentSlope ^ 2 - tangentMap addX₁ - tangentMap addX₂
private def tangentY : TangentRing :=
  tangentSlope * (tangentMap addX₁ - tangentX) - tangentMap addY₁

private theorem tangentMap_relation_left :
    tangentMap addY₁ ^ 2 = tangentMap addX₁ ^ 3 + tangentMap addX₁ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ TangentRing) h
  simp only [map_sub, map_pow, map_zero] at h'
  change (algebraMap AddZZ TangentRing)
      ((Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addYCoord) ^ 2 =
    (algebraMap AddZZ TangentRing)
        ((Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addXCoord) ^ 3 +
      (algebraMap AddZZ TangentRing)
        ((Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) addXCoord)
  linear_combination h'

private theorem tangentMap_relation_right :
    tangentMap addY₂ ^ 2 = tangentMap addX₂ ^ 3 + tangentMap addX₂ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ TangentRing) h
  simp only [map_sub, map_pow, map_zero] at h'
  change (algebraMap AddZZ TangentRing)
      ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addYCoord) ^ 2 =
    (algebraMap AddZZ TangentRing)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord) ^ 3 +
      (algebraMap AddZZ TangentRing)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord)
  linear_combination h'

private theorem tangent_denom_unit :
    IsUnit (tangentMap addY₁ + tangentMap addY₂) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨tangentInv, ?_⟩
  simpa [tangentInv, tangentMap, tangentDenom, map_add] using
    (IsLocalization.Away.mul_invSelf tangentDenom (S := TangentRing))

private theorem tangentSlope_spec :
    tangentSlope * (tangentMap addY₁ + tangentMap addY₂) =
      tangentMap addX₁ ^ 2 + tangentMap addX₁ * tangentMap addX₂ +
        tangentMap addX₂ ^ 2 + 1 := by
  have h : (tangentMap addY₁ + tangentMap addY₂) * tangentInv = 1 := by
    simpa [tangentInv, tangentMap, tangentDenom, map_add] using
      (IsLocalization.Away.mul_invSelf tangentDenom (S := TangentRing))
  calc
    tangentSlope * (tangentMap addY₁ + tangentMap addY₂) =
        (tangentMap addX₁ ^ 2 + tangentMap addX₁ * tangentMap addX₂ +
          tangentMap addX₂ ^ 2 + 1) *
          ((tangentMap addY₁ + tangentMap addY₂) * tangentInv) := by
            simp only [tangentSlope]
            ring
    _ = _ := by rw [h, mul_one]

private theorem tangent_coordinates_equation : tangentY ^ 2 = tangentX ^ 3 + tangentX := by
  exact tangentChord_addition_equation tangentMap_relation_left tangentMap_relation_right
    tangentSlope_spec tangent_denom_unit

private def tangentCoordinates : AddA →+* TangentRing :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℂ TangentRing) tangentX) tangentY (by
    have heval (a b : TangentRing) :
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ TangentRing) a) b
          W.toAffine.polynomial = b ^ 2 - a ^ 3 - a := by
      simp [WeierstrassCurve.Affine.polynomial, W, WeierstrassCurve.ofJ1728,
        Polynomial.eval₂_eval₂RingHom_apply, Polynomial.evalEval_C]
      <;> ring
    rw [heval]
    linear_combination tangent_coordinates_equation)

private theorem tangentCoordinates_over :
    tangentCoordinates.comp (algebraMap ℂ AddA) = algebraMap ℂ TangentRing := by
  ext c
  change tangentCoordinates ((AdjoinRoot.mk W.toAffine.polynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [tangentCoordinates, AdjoinRoot.algebraMap_eq']

private def tangentLocal : Spec ↧TangentRing ⟶ E.left :=
  Spec.map (CommRingCat.ofHom tangentCoordinates) ≫ zChartMap

private theorem tangentLocal_over :
    tangentLocal ≫ E.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ TangentRing)) := by
  rw [tangentLocal, Category.assoc, zChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ AddA) ≫
      CommRingCat.ofHom tangentCoordinates =
      CommRingCat.ofHom (algebraMap ℂ TangentRing) by
    apply CommRingCat.hom_ext
    exact tangentCoordinates_over]

/-! The first antidiagonal chart.  We first invert `y₂-y₁`, so that the reciprocal
slope `μ = (x₂-x₁)/(y₂-y₁)` is regular, and then invert the numerator `B` of the
resulting `y`-coordinate.  In the infinity chart the sum has coordinates
`u = μ A / B`, `v = μ³ / B`. -/

private def reciprocalChordDenom : AddZZ := addY₂ - addY₁
private abbrev ReciprocalChordBase := Localization.Away reciprocalChordDenom
private def reciprocalChordMap (a : AddZZ) : ReciprocalChordBase :=
  algebraMap AddZZ ReciprocalChordBase a
private def reciprocalChordInv : ReciprocalChordBase :=
  IsLocalization.Away.invSelf reciprocalChordDenom
private def reciprocalChordMu : ReciprocalChordBase :=
  (reciprocalChordMap addX₂ - reciprocalChordMap addX₁) * reciprocalChordInv
private def reciprocalChordA : ReciprocalChordBase :=
  1 - reciprocalChordMu ^ 2 * (reciprocalChordMap addX₁ + reciprocalChordMap addX₂)
private def reciprocalChordB : ReciprocalChordBase :=
  -1 + reciprocalChordMu ^ 2 *
      (2 * reciprocalChordMap addX₁ + reciprocalChordMap addX₂) -
    reciprocalChordMu ^ 3 * reciprocalChordMap addY₁
private abbrev ReciprocalChordRing := Localization.Away reciprocalChordB
private def reciprocalChordBaseMap (a : ReciprocalChordBase) : ReciprocalChordRing :=
  algebraMap ReciprocalChordBase ReciprocalChordRing a
private def reciprocalChordBInv : ReciprocalChordRing :=
  IsLocalization.Away.invSelf reciprocalChordB
private def reciprocalChordU : ReciprocalChordRing :=
  reciprocalChordBaseMap (reciprocalChordMu * reciprocalChordA) * reciprocalChordBInv
private def reciprocalChordV : ReciprocalChordRing :=
  reciprocalChordBaseMap (reciprocalChordMu ^ 3) * reciprocalChordBInv

private theorem reciprocalChordMap_relation_left :
    reciprocalChordMap addY₁ ^ 2 =
      reciprocalChordMap addX₁ ^ 3 + reciprocalChordMap addX₁ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ ReciprocalChordBase) h
  simp only [map_sub, map_pow, map_zero] at h'
  dsimp [reciprocalChordMap, addX₁, addY₁]
  linear_combination h'

private theorem reciprocalChordMap_relation_right :
    reciprocalChordMap addY₂ ^ 2 =
      reciprocalChordMap addX₂ ^ 3 + reciprocalChordMap addX₂ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ ReciprocalChordBase) h
  simp only [map_sub, map_pow, map_zero] at h'
  change (algebraMap AddZZ ReciprocalChordBase)
      ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addYCoord) ^ 2 =
    (algebraMap AddZZ ReciprocalChordBase)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord) ^ 3 +
      (algebraMap AddZZ ReciprocalChordBase)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord)
  linear_combination h'

private theorem reciprocalChord_denom_unit :
    IsUnit (reciprocalChordMap addY₂ - reciprocalChordMap addY₁) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨reciprocalChordInv, ?_⟩
  simpa [reciprocalChordInv, reciprocalChordMap, reciprocalChordDenom, map_sub] using
    (IsLocalization.Away.mul_invSelf reciprocalChordDenom (S := ReciprocalChordBase))

private theorem reciprocalChordMu_spec :
    reciprocalChordMu * (reciprocalChordMap addY₂ - reciprocalChordMap addY₁) =
      reciprocalChordMap addX₂ - reciprocalChordMap addX₁ := by
  have h : (reciprocalChordMap addY₂ - reciprocalChordMap addY₁) *
      reciprocalChordInv = 1 := by
    simpa [reciprocalChordInv, reciprocalChordMap, reciprocalChordDenom, map_sub] using
      (IsLocalization.Away.mul_invSelf reciprocalChordDenom (S := ReciprocalChordBase))
  simp only [reciprocalChordMu]
  calc
    (reciprocalChordMap addX₂ - reciprocalChordMap addX₁) * reciprocalChordInv *
        (reciprocalChordMap addY₂ - reciprocalChordMap addY₁) =
      (reciprocalChordMap addX₂ - reciprocalChordMap addX₁) *
        ((reciprocalChordMap addY₂ - reciprocalChordMap addY₁) *
          reciprocalChordInv) := by ring
    _ = _ := by rw [h, mul_one]

private theorem reciprocalChord_AB :
    reciprocalChordB ^ 2 = reciprocalChordA ^ 3 +
      reciprocalChordMu ^ 4 * reciprocalChordA := by
  exact reciprocalChord_addition_equation reciprocalChordMap_relation_left
    reciprocalChordMap_relation_right reciprocalChordMu_spec reciprocalChord_denom_unit

private theorem reciprocalChordB_inverse :
    reciprocalChordBaseMap reciprocalChordB * reciprocalChordBInv = 1 := by
  simpa [reciprocalChordBaseMap, reciprocalChordBInv] using
    (IsLocalization.Away.mul_invSelf reciprocalChordB (S := ReciprocalChordRing))

private theorem reciprocalChord_y_equation :
    reciprocalChordV = reciprocalChordU ^ 3 + reciprocalChordU * reciprocalChordV ^ 2 := by
  simpa only [reciprocalChordV, reciprocalChordU, reciprocalChordBaseMap, map_pow, map_mul] using
    reciprocal_y_chart_equation
    (reciprocalChordBaseMap reciprocalChordA)
    (reciprocalChordBaseMap reciprocalChordB)
    (reciprocalChordBaseMap reciprocalChordMu)
    reciprocalChordBInv
    (by
      have h := congrArg reciprocalChordBaseMap reciprocalChord_AB
      dsimp [reciprocalChordBaseMap] at h ⊢
      simpa only [map_pow, map_add, map_mul] using h)
    reciprocalChordB_inverse

private def reciprocalChordCoordinates : YCoordinateRing →+* ReciprocalChordRing :=
  AdjoinRoot.lift
    (Polynomial.eval₂RingHom (algebraMap ℂ ReciprocalChordRing) reciprocalChordU)
    reciprocalChordV (by
    simp [yAffinePolynomial, Polynomial.eval₂_eval₂RingHom_apply,
      Polynomial.evalEval_C]
    linear_combination reciprocalChord_y_equation)

private def reciprocalChordLocal : Spec ↧ReciprocalChordRing ⟶ E.left :=
  Spec.map (CommRingCat.ofHom reciprocalChordCoordinates) ≫ yChartMap

private theorem reciprocalChordCoordinates_over :
    reciprocalChordCoordinates.comp (algebraMap ℂ YCoordinateRing) =
      algebraMap ℂ ReciprocalChordRing := by
  ext c
  change reciprocalChordCoordinates ((AdjoinRoot.mk yAffinePolynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [reciprocalChordCoordinates, AdjoinRoot.algebraMap_eq']

private theorem reciprocalChordLocal_over :
    reciprocalChordLocal ≫ E.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ ReciprocalChordRing)) := by
  rw [reciprocalChordLocal, Category.assoc, yChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ YCoordinateRing) ≫
      CommRingCat.ofHom reciprocalChordCoordinates =
      CommRingCat.ofHom (algebraMap ℂ ReciprocalChordRing) by
    apply CommRingCat.hom_ext
    exact reciprocalChordCoordinates_over]

/-! The complementary antidiagonal chart uses
`μ = (y₁+y₂)/(x₁²+x₁x₂+x₂²+1)`. -/

private def reciprocalTangentDenom : AddZZ :=
  addX₁ ^ 2 + addX₁ * addX₂ + addX₂ ^ 2 + 1

/-! The four first denominators already cover the finite--finite chart.  This is the
scheme-theoretic version of `finite_addition_basic_opens_cover`: their ideal is the unit ideal
in the tensor-product coordinate ring. -/

private def finiteAdditionDenom : Fin 4 → AddZZ
  | 0 => chordDenom
  | 1 => tangentDenom
  | 2 => reciprocalChordDenom
  | 3 => reciprocalTangentDenom

private theorem finiteAdditionDenom_span :
    Ideal.span (Set.range finiteAdditionDenom) = ⊤ := by
  let I : Ideal AddZZ := Ideal.span (Set.range finiteAdditionDenom)
  change I = ⊤
  apply I.eq_top_iff_one.mpr
  have hmem (i : Fin 4) : finiteAdditionDenom i ∈ I :=
    Ideal.subset_span (Set.mem_range_self i)
  have hdx : addX₂ - addX₁ ∈ I := by simpa [finiteAdditionDenom, chordDenom] using hmem 0
  have hys : addY₁ + addY₂ ∈ I := by simpa [finiteAdditionDenom, tangentDenom] using hmem 1
  have hyd : addY₂ - addY₁ ∈ I := by
    simpa [finiteAdditionDenom, reciprocalChordDenom] using hmem 2
  have hS : addX₁ ^ 2 + addX₁ * addX₂ + addX₂ ^ 2 + 1 ∈ I := by
    simpa [finiteAdditionDenom, reciprocalTangentDenom] using hmem 3
  have hy₁ : addY₁ ∈ I := by
    have : (2 : AddZZ) * addY₁ ∈ I := by
      convert I.sub_mem hys hyd using 1 <;> ring
    have hunit : IsUnit (2 : AddZZ) := by
      simpa only [map_ofNat] using
        (show IsUnit (2 : ℂ) from by norm_num).map (algebraMap ℂ AddZZ)
    exact (I.unit_mul_mem_iff_mem hunit).mp this
  have hcurve : addX₁ ^ 3 + addX₁ ∈ I := by
    have hrel := congrArg (fun a : AddA ↦
      (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) a)
      addA_relation
    simp only [map_sub, map_pow, map_zero] at hrel
    change addY₁ ^ 2 - addX₁ ^ 3 - addX₁ = 0 at hrel
    have hy₁sq : addY₁ ^ 2 ∈ I := I.mul_mem_left _ hy₁
    have heq : addX₁ ^ 3 + addX₁ = addY₁ ^ 2 := by linear_combination -hrel
    rwa [heq]
  have hx₁ : addX₁ ∈ I := by
    have hS' : 3 * addX₁ ^ 2 + 1 ∈ I := by
      convert I.sub_mem hS (I.mul_mem_left (addX₂ + 2 * addX₁) hdx) using 1 <;> ring
    have htwo : 2 * addX₁ ∈ I := by
      convert I.sub_mem (I.mul_mem_left 3 hcurve) (I.mul_mem_left addX₁ hS') using 1 <;> ring
    have hunit : IsUnit (2 : AddZZ) := by
      simpa only [map_ofNat] using
        (show IsUnit (2 : ℂ) from by norm_num).map (algebraMap ℂ AddZZ)
    exact (I.unit_mul_mem_iff_mem hunit).mp htwo
  have hS' : 3 * addX₁ ^ 2 + 1 ∈ I := by
    convert I.sub_mem hS (I.mul_mem_left (addX₂ + 2 * addX₁) hdx) using 1 <;> ring
  convert I.sub_mem hS' (I.mul_mem_left (3 * addX₁) hx₁) using 1 <;> ring

private def reciprocalChordCleared : AddZZ :=
  -(reciprocalChordDenom ^ 3) + chordDenom ^ 2 * reciprocalChordDenom *
      (2 * addX₁ + addX₂) - chordDenom ^ 3 * addY₁

private def reciprocalTangentCleared : AddZZ :=
  -(reciprocalTangentDenom ^ 3) + tangentDenom ^ 2 * reciprocalTangentDenom *
      (2 * addX₁ + addX₂) - tangentDenom ^ 3 * addY₁

private def finiteAdditionRefinedDenom : Fin 4 → AddZZ
  | 0 => chordDenom
  | 1 => tangentDenom
  | 2 => reciprocalChordDenom * reciprocalChordCleared
  | 3 => reciprocalTangentDenom * reciprocalTangentCleared

private theorem finiteAdditionRefinedDenom_span :
    Ideal.span (Set.range finiteAdditionRefinedDenom) = ⊤ := by
  let J : Ideal AddZZ := Ideal.span (Set.range finiteAdditionRefinedDenom)
  have hmem (i : Fin 4) : finiteAdditionRefinedDenom i ∈ J :=
    Ideal.subset_span (Set.mem_range_self i)
  have hdx : chordDenom ∈ J := by simpa [finiteAdditionRefinedDenom] using hmem 0
  have hsy : tangentDenom ∈ J := by simpa [finiteAdditionRefinedDenom] using hmem 1
  have hdy4 : reciprocalChordDenom ^ 4 ∈ J := by
    have h := hmem 2
    have h₁ := J.mul_mem_left
      (chordDenom * reciprocalChordDenom ^ 2 * (2 * addX₁ + addX₂)) hdx
    have h₂ := J.mul_mem_left (chordDenom ^ 2 * reciprocalChordDenom * addY₁) hdx
    convert J.sub_mem (J.add_mem (J.neg_mem h) h₁) h₂ using 1 <;>
      simp only [finiteAdditionRefinedDenom, reciprocalChordCleared] <;> ring
  have hS4 : reciprocalTangentDenom ^ 4 ∈ J := by
    have h := hmem 3
    have h₁ := J.mul_mem_left
      (tangentDenom * reciprocalTangentDenom ^ 2 * (2 * addX₁ + addX₂)) hsy
    have h₂ := J.mul_mem_left (tangentDenom ^ 2 * reciprocalTangentDenom * addY₁) hsy
    convert J.sub_mem (J.add_mem (J.neg_mem h) h₁) h₂ using 1 <;>
      simp only [finiteAdditionRefinedDenom, reciprocalTangentCleared] <;> ring
  have hpowers : Ideal.span ((fun x : AddZZ ↦ x ^ 4) ''
      Set.range finiteAdditionDenom) = ⊤ :=
    Ideal.span_pow_eq_top _ finiteAdditionDenom_span 4
  apply top_unique
  rw [← hpowers]
  apply Ideal.span_le.mpr
  rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
  fin_cases i
  · change chordDenom ^ 4 ∈ J
    convert J.mul_mem_left (chordDenom ^ 3) hdx using 1 <;> ring
  · change tangentDenom ^ 4 ∈ J
    convert J.mul_mem_left (tangentDenom ^ 3) hsy using 1 <;> ring
  · exact hdy4
  · exact hS4
private abbrev ReciprocalTangentBase := Localization.Away reciprocalTangentDenom
private def reciprocalTangentMap (a : AddZZ) : ReciprocalTangentBase :=
  algebraMap AddZZ ReciprocalTangentBase a
private def reciprocalTangentInv : ReciprocalTangentBase :=
  IsLocalization.Away.invSelf reciprocalTangentDenom
private def reciprocalTangentMu : ReciprocalTangentBase :=
  (reciprocalTangentMap addY₁ + reciprocalTangentMap addY₂) * reciprocalTangentInv
private def reciprocalTangentA : ReciprocalTangentBase :=
  1 - reciprocalTangentMu ^ 2 *
    (reciprocalTangentMap addX₁ + reciprocalTangentMap addX₂)
private def reciprocalTangentB : ReciprocalTangentBase :=
  -1 + reciprocalTangentMu ^ 2 *
      (2 * reciprocalTangentMap addX₁ + reciprocalTangentMap addX₂) -
    reciprocalTangentMu ^ 3 * reciprocalTangentMap addY₁
private abbrev ReciprocalTangentRing := Localization.Away reciprocalTangentB
private def reciprocalTangentBaseMap (a : ReciprocalTangentBase) : ReciprocalTangentRing :=
  algebraMap ReciprocalTangentBase ReciprocalTangentRing a
private def reciprocalTangentBInv : ReciprocalTangentRing :=
  IsLocalization.Away.invSelf reciprocalTangentB
private def reciprocalTangentU : ReciprocalTangentRing :=
  reciprocalTangentBaseMap (reciprocalTangentMu * reciprocalTangentA) * reciprocalTangentBInv
private def reciprocalTangentV : ReciprocalTangentRing :=
  reciprocalTangentBaseMap (reciprocalTangentMu ^ 3) * reciprocalTangentBInv

private theorem reciprocalTangentMap_relation_left :
    reciprocalTangentMap addY₁ ^ 2 =
      reciprocalTangentMap addX₁ ^ 3 + reciprocalTangentMap addX₁ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeLeftRingHom (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ ReciprocalTangentBase) h
  simp only [map_sub, map_pow, map_zero] at h'
  dsimp [reciprocalTangentMap, addX₁, addY₁]
  linear_combination h'

private theorem reciprocalTangentMap_relation_right :
    reciprocalTangentMap addY₂ ^ 2 =
      reciprocalTangentMap addX₂ ^ 3 + reciprocalTangentMap addX₂ := by
  have h := congrArg (fun a : AddA ↦
    (Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) a)
    addA_relation
  have h' := congrArg (algebraMap AddZZ ReciprocalTangentBase) h
  simp only [map_sub, map_pow, map_zero] at h'
  change (algebraMap AddZZ ReciprocalTangentBase)
      ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addYCoord) ^ 2 =
    (algebraMap AddZZ ReciprocalTangentBase)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord) ^ 3 +
      (algebraMap AddZZ ReciprocalTangentBase)
        ((Algebra.TensorProduct.includeRight (R := ℂ) (A := AddA) (B := AddA)) addXCoord)
  linear_combination h'

private theorem reciprocalTangent_denom_unit :
    IsUnit (reciprocalTangentMap addX₁ ^ 2 +
      reciprocalTangentMap addX₁ * reciprocalTangentMap addX₂ +
      reciprocalTangentMap addX₂ ^ 2 + 1) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨reciprocalTangentInv, ?_⟩
  simpa [reciprocalTangentInv, reciprocalTangentMap, reciprocalTangentDenom,
    map_add, map_mul, map_pow] using
    (IsLocalization.Away.mul_invSelf reciprocalTangentDenom (S := ReciprocalTangentBase))

private theorem reciprocalTangentMu_spec :
    reciprocalTangentMu *
      (reciprocalTangentMap addX₁ ^ 2 +
        reciprocalTangentMap addX₁ * reciprocalTangentMap addX₂ +
        reciprocalTangentMap addX₂ ^ 2 + 1) =
      reciprocalTangentMap addY₁ + reciprocalTangentMap addY₂ := by
  have h : (reciprocalTangentMap addX₁ ^ 2 +
      reciprocalTangentMap addX₁ * reciprocalTangentMap addX₂ +
      reciprocalTangentMap addX₂ ^ 2 + 1) * reciprocalTangentInv = 1 := by
    simpa [reciprocalTangentInv, reciprocalTangentMap, reciprocalTangentDenom,
      map_add, map_mul, map_pow] using
      (IsLocalization.Away.mul_invSelf reciprocalTangentDenom (S := ReciprocalTangentBase))
  simp only [reciprocalTangentMu]
  calc
    (reciprocalTangentMap addY₁ + reciprocalTangentMap addY₂) * reciprocalTangentInv *
        (reciprocalTangentMap addX₁ ^ 2 +
          reciprocalTangentMap addX₁ * reciprocalTangentMap addX₂ +
          reciprocalTangentMap addX₂ ^ 2 + 1) =
      (reciprocalTangentMap addY₁ + reciprocalTangentMap addY₂) *
        ((reciprocalTangentMap addX₁ ^ 2 +
          reciprocalTangentMap addX₁ * reciprocalTangentMap addX₂ +
          reciprocalTangentMap addX₂ ^ 2 + 1) * reciprocalTangentInv) := by ring
    _ = _ := by rw [h, mul_one]

private theorem reciprocalChordB_clear_denominator :
    reciprocalChordB * reciprocalChordMap reciprocalChordDenom ^ 3 =
      reciprocalChordMap reciprocalChordCleared := by
  calc
    reciprocalChordB * reciprocalChordMap reciprocalChordDenom ^ 3 =
        -(reciprocalChordMap reciprocalChordDenom ^ 3) +
          (reciprocalChordMu * reciprocalChordMap reciprocalChordDenom) ^ 2 *
            reciprocalChordMap reciprocalChordDenom *
              (2 * reciprocalChordMap addX₁ + reciprocalChordMap addX₂) -
          (reciprocalChordMu * reciprocalChordMap reciprocalChordDenom) ^ 3 *
            reciprocalChordMap addY₁ := by
      simp only [reciprocalChordB]
      ring
    _ = -(reciprocalChordMap reciprocalChordDenom ^ 3) +
          (reciprocalChordMap addX₂ - reciprocalChordMap addX₁) ^ 2 *
            reciprocalChordMap reciprocalChordDenom *
              (2 * reciprocalChordMap addX₁ + reciprocalChordMap addX₂) -
          (reciprocalChordMap addX₂ - reciprocalChordMap addX₁) ^ 3 *
            reciprocalChordMap addY₁ := by
      have hspec : reciprocalChordMu * reciprocalChordMap reciprocalChordDenom =
          reciprocalChordMap addX₂ - reciprocalChordMap addX₁ := by
        rw [show reciprocalChordMap reciprocalChordDenom =
          reciprocalChordMap addY₂ - reciprocalChordMap addY₁ by
            simp [reciprocalChordMap, reciprocalChordDenom, map_sub]]
        exact reciprocalChordMu_spec
      rw [hspec]
    _ = reciprocalChordMap reciprocalChordCleared := by
      simp only [reciprocalChordCleared, chordDenom, reciprocalChordMap,
        map_neg, map_sub, map_add, map_mul, map_pow, map_ofNat]

private theorem reciprocalTangentB_clear_denominator :
    reciprocalTangentB * reciprocalTangentMap reciprocalTangentDenom ^ 3 =
      reciprocalTangentMap reciprocalTangentCleared := by
  calc
    reciprocalTangentB * reciprocalTangentMap reciprocalTangentDenom ^ 3 =
        -(reciprocalTangentMap reciprocalTangentDenom ^ 3) +
          (reciprocalTangentMu * reciprocalTangentMap reciprocalTangentDenom) ^ 2 *
            reciprocalTangentMap reciprocalTangentDenom *
              (2 * reciprocalTangentMap addX₁ + reciprocalTangentMap addX₂) -
          (reciprocalTangentMu * reciprocalTangentMap reciprocalTangentDenom) ^ 3 *
            reciprocalTangentMap addY₁ := by
      simp only [reciprocalTangentB]
      ring
    _ = -(reciprocalTangentMap reciprocalTangentDenom ^ 3) +
          (reciprocalTangentMap addY₁ + reciprocalTangentMap addY₂) ^ 2 *
            reciprocalTangentMap reciprocalTangentDenom *
              (2 * reciprocalTangentMap addX₁ + reciprocalTangentMap addX₂) -
          (reciprocalTangentMap addY₁ + reciprocalTangentMap addY₂) ^ 3 *
            reciprocalTangentMap addY₁ := by
      have hspec : reciprocalTangentMu * reciprocalTangentMap reciprocalTangentDenom =
          reciprocalTangentMap addY₁ + reciprocalTangentMap addY₂ := by
        rw [show reciprocalTangentMap reciprocalTangentDenom =
          reciprocalTangentMap addX₁ ^ 2 +
            reciprocalTangentMap addX₁ * reciprocalTangentMap addX₂ +
            reciprocalTangentMap addX₂ ^ 2 + 1 by
              simp [reciprocalTangentMap, reciprocalTangentDenom,
                map_add, map_mul, map_pow]]
        exact reciprocalTangentMu_spec
      rw [hspec]
    _ = reciprocalTangentMap reciprocalTangentCleared := by
      simp only [reciprocalTangentCleared, tangentDenom, reciprocalTangentMap,
        map_neg, map_sub, map_add, map_mul, map_pow, map_ofNat]

private noncomputable def reciprocalChordRefinedEquiv :
    Localization.Away (reciprocalChordDenom * reciprocalChordCleared) ≃ₐ[AddZZ]
      ReciprocalChordRing := by
  have hu : IsUnit (reciprocalChordMap reciprocalChordDenom ^ 3) :=
    (IsLocalization.Away.algebraMap_isUnit reciprocalChordDenom).pow 3
  have ha : Associated reciprocalChordB (reciprocalChordMap reciprocalChordCleared) :=
    (associated_mul_unit_right reciprocalChordB _ hu).trans
      (.of_eq reciprocalChordB_clear_denominator)
  letI : IsLocalization.Away
      ((algebraMap AddZZ ReciprocalChordBase) reciprocalChordCleared)
      ReciprocalChordRing := IsLocalization.Away.of_associated (by
        simpa [reciprocalChordMap] using ha)
  letI : IsLocalization.Away (reciprocalChordDenom * reciprocalChordCleared)
      ReciprocalChordRing :=
    IsLocalization.Away.mul' ReciprocalChordBase ReciprocalChordRing
      reciprocalChordDenom reciprocalChordCleared
  exact IsLocalization.algEquiv
    (Submonoid.powers (reciprocalChordDenom * reciprocalChordCleared)) _ _

private noncomputable def reciprocalTangentRefinedEquiv :
    Localization.Away (reciprocalTangentDenom * reciprocalTangentCleared) ≃ₐ[AddZZ]
      ReciprocalTangentRing := by
  have hu : IsUnit (reciprocalTangentMap reciprocalTangentDenom ^ 3) :=
    (IsLocalization.Away.algebraMap_isUnit reciprocalTangentDenom).pow 3
  have ha : Associated reciprocalTangentB
      (reciprocalTangentMap reciprocalTangentCleared) :=
    (associated_mul_unit_right reciprocalTangentB _ hu).trans
      (.of_eq reciprocalTangentB_clear_denominator)
  letI : IsLocalization.Away
      ((algebraMap AddZZ ReciprocalTangentBase) reciprocalTangentCleared)
      ReciprocalTangentRing := IsLocalization.Away.of_associated (by
        simpa [reciprocalTangentMap] using ha)
  letI : IsLocalization.Away (reciprocalTangentDenom * reciprocalTangentCleared)
      ReciprocalTangentRing :=
    IsLocalization.Away.mul' ReciprocalTangentBase ReciprocalTangentRing
      reciprocalTangentDenom reciprocalTangentCleared
  exact IsLocalization.algEquiv
    (Submonoid.powers (reciprocalTangentDenom * reciprocalTangentCleared)) _ _

private noncomputable def finiteAdditionCover : (Spec ↧AddZZ).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop finiteAdditionRefinedDenom
    finiteAdditionRefinedDenom_span

private theorem reciprocalTangent_AB :
    reciprocalTangentB ^ 2 = reciprocalTangentA ^ 3 +
      reciprocalTangentMu ^ 4 * reciprocalTangentA := by
  exact reciprocalTangentChord_addition_equation reciprocalTangentMap_relation_left
    reciprocalTangentMap_relation_right reciprocalTangentMu_spec reciprocalTangent_denom_unit

private theorem reciprocalTangentB_inverse :
    reciprocalTangentBaseMap reciprocalTangentB * reciprocalTangentBInv = 1 := by
  simpa [reciprocalTangentBaseMap, reciprocalTangentBInv] using
    (IsLocalization.Away.mul_invSelf reciprocalTangentB (S := ReciprocalTangentRing))

private theorem reciprocalTangent_y_equation :
    reciprocalTangentV = reciprocalTangentU ^ 3 +
      reciprocalTangentU * reciprocalTangentV ^ 2 := by
  simpa only [reciprocalTangentV, reciprocalTangentU, reciprocalTangentBaseMap,
    map_pow, map_mul] using
    reciprocal_y_chart_equation
      (reciprocalTangentBaseMap reciprocalTangentA)
      (reciprocalTangentBaseMap reciprocalTangentB)
      (reciprocalTangentBaseMap reciprocalTangentMu)
      reciprocalTangentBInv
      (by
        have h := congrArg reciprocalTangentBaseMap reciprocalTangent_AB
        dsimp [reciprocalTangentBaseMap] at h ⊢
        simpa only [map_pow, map_add, map_mul] using h)
      reciprocalTangentB_inverse

private def reciprocalTangentCoordinates : YCoordinateRing →+* ReciprocalTangentRing :=
  AdjoinRoot.lift
    (Polynomial.eval₂RingHom (algebraMap ℂ ReciprocalTangentRing) reciprocalTangentU)
    reciprocalTangentV (by
      simp [yAffinePolynomial, Polynomial.eval₂_eval₂RingHom_apply,
        Polynomial.evalEval_C]
      linear_combination reciprocalTangent_y_equation)

private def reciprocalTangentLocal : Spec ↧ReciprocalTangentRing ⟶ E.left :=
  Spec.map (CommRingCat.ofHom reciprocalTangentCoordinates) ≫ yChartMap

private theorem reciprocalTangentCoordinates_over :
    reciprocalTangentCoordinates.comp (algebraMap ℂ YCoordinateRing) =
      algebraMap ℂ ReciprocalTangentRing := by
  ext c
  change reciprocalTangentCoordinates ((AdjoinRoot.mk yAffinePolynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [reciprocalTangentCoordinates, AdjoinRoot.algebraMap_eq']

private theorem reciprocalTangentLocal_over :
    reciprocalTangentLocal ≫ E.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ ReciprocalTangentRing)) := by
  rw [reciprocalTangentLocal, Category.assoc, yChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ YCoordinateRing) ≫
      CommRingCat.ofHom reciprocalTangentCoordinates =
      CommRingCat.ofHom (algebraMap ℂ ReciprocalTangentRing) by
    apply CommRingCat.hom_ext
    exact reciprocalTangentCoordinates_over]

private noncomputable def reciprocalChordRefinedLocal :
    Spec ↧(Localization.Away (reciprocalChordDenom * reciprocalChordCleared)) ⟶ E.left :=
  Spec.map (CommRingCat.ofHom reciprocalChordRefinedEquiv.symm.toRingHom) ≫
    reciprocalChordLocal

private theorem reciprocalChordRefinedLocal_over :
    reciprocalChordRefinedLocal ≫ E.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (Localization.Away
          (reciprocalChordDenom * reciprocalChordCleared)))) := by
  rw [reciprocalChordRefinedLocal, Category.assoc, reciprocalChordLocal_over,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change reciprocalChordRefinedEquiv.symm ((algebraMap ℂ ReciprocalChordRing) a) =
    (algebraMap ℂ (Localization.Away
      (reciprocalChordDenom * reciprocalChordCleared))) a
  simpa only [IsScalarTower.algebraMap_apply ℂ AddZZ ReciprocalChordRing,
    IsScalarTower.algebraMap_apply ℂ AddZZ
      (Localization.Away (reciprocalChordDenom * reciprocalChordCleared))] using
    (reciprocalChordRefinedEquiv.symm.commutes (algebraMap ℂ AddZZ a))

private noncomputable def reciprocalTangentRefinedLocal :
    Spec ↧(Localization.Away (reciprocalTangentDenom * reciprocalTangentCleared)) ⟶ E.left :=
  Spec.map (CommRingCat.ofHom reciprocalTangentRefinedEquiv.symm.toRingHom) ≫
    reciprocalTangentLocal

private theorem reciprocalTangentRefinedLocal_over :
    reciprocalTangentRefinedLocal ≫ E.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (Localization.Away
          (reciprocalTangentDenom * reciprocalTangentCleared)))) := by
  rw [reciprocalTangentRefinedLocal, Category.assoc, reciprocalTangentLocal_over,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change reciprocalTangentRefinedEquiv.symm ((algebraMap ℂ ReciprocalTangentRing) a) =
    (algebraMap ℂ (Localization.Away
      (reciprocalTangentDenom * reciprocalTangentCleared))) a
  simpa only [IsScalarTower.algebraMap_apply ℂ AddZZ ReciprocalTangentRing,
    IsScalarTower.algebraMap_apply ℂ AddZZ
      (Localization.Away (reciprocalTangentDenom * reciprocalTangentCleared))] using
    (reciprocalTangentRefinedEquiv.symm.commutes (algebraMap ℂ AddZZ a))

private noncomputable def finiteAdditionLocal
    (i : Fin 4) : finiteAdditionCover.openCover.X i ⟶ E.left := by
  refine Fin.cases chordLocal ?_ i
  intro i
  refine Fin.cases tangentLocal ?_ i
  intro i
  refine Fin.cases reciprocalChordRefinedLocal ?_ i
  intro i
  refine Fin.cases reciprocalTangentRefinedLocal ?_ i
  intro j
  exact Fin.elim0 j

private noncomputable def finiteAdditionGlued
    (h : ∀ i j,
      pullback.fst (finiteAdditionCover.openCover.f i)
          (finiteAdditionCover.openCover.f j) ≫ finiteAdditionLocal i =
        pullback.snd (finiteAdditionCover.openCover.f i)
          (finiteAdditionCover.openCover.f j) ≫ finiteAdditionLocal j) :
    Spec ↧AddZZ ⟶ E.left :=
  finiteAdditionCover.openCover.glueMorphisms finiteAdditionLocal h

private theorem finiteAdditionGlued_restrict
    (h : ∀ i j,
      pullback.fst (finiteAdditionCover.openCover.f i)
          (finiteAdditionCover.openCover.f j) ≫ finiteAdditionLocal i =
        pullback.snd (finiteAdditionCover.openCover.f i)
          (finiteAdditionCover.openCover.f j) ≫ finiteAdditionLocal j)
    (i : Fin 4) :
    finiteAdditionCover.openCover.f i ≫ finiteAdditionGlued h =
      finiteAdditionLocal i := by
  exact finiteAdditionCover.openCover.ι_glueMorphisms finiteAdditionLocal h i

/-! Transport the four finite--finite formula domains from affine spectra to the actual
product scheme.  These are the open immersions that will form the finite part of the gluing
cover. -/

private noncomputable def zzTensorIso :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ AddA))) ⊗
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ AddA)))) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ AddZZ))) :=
  Over.isoMk (pullbackSpecIso ℂ AddA AddA) (pullbackSpecIso_hom_base ℂ AddA AddA)

private noncomputable def zzToProduct : Spec ↧AddZZ ⟶ (E ⊗ E).left :=
  zzTensorIso.inv.left ≫ (zChartOver ⊗ₘ zChartOver).left

private noncomputable def chordDomain : Spec ↧ChordRing ⟶ (E ⊗ E).left :=
  Spec.map (CommRingCat.ofHom (algebraMap AddZZ ChordRing)) ≫ zzToProduct

private noncomputable def tangentDomain : Spec ↧TangentRing ⟶ (E ⊗ E).left :=
  Spec.map (CommRingCat.ofHom (algebraMap AddZZ TangentRing)) ≫ zzToProduct

private noncomputable def reciprocalChordDomain :
    Spec ↧ReciprocalChordRing ⟶ (E ⊗ E).left :=
  Spec.map (CommRingCat.ofHom (algebraMap ReciprocalChordBase ReciprocalChordRing)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap AddZZ ReciprocalChordBase)) ≫ zzToProduct

private noncomputable def reciprocalTangentDomain :
    Spec ↧ReciprocalTangentRing ⟶ (E ⊗ E).left :=
  Spec.map (CommRingCat.ofHom (algebraMap ReciprocalTangentBase ReciprocalTangentRing)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap AddZZ ReciprocalTangentBase)) ≫ zzToProduct

private instance : IsOpenImmersion zzToProduct := by
  letI : IsOpenImmersion zChartOver.left := by
    change IsOpenImmersion zChartMap
    dsimp [zChartMap]
    infer_instance
  dsimp [zzToProduct]
  rw [Over.tensorHom_left]
  infer_instance

private instance : IsOpenImmersion chordDomain := by
  dsimp [chordDomain]
  infer_instance

private instance : IsOpenImmersion tangentDomain := by
  dsimp [tangentDomain]
  infer_instance

private instance : IsOpenImmersion reciprocalChordDomain := by
  dsimp [reciprocalChordDomain]
  infer_instance

private instance : IsOpenImmersion reciprocalTangentDomain := by
  dsimp [reciprocalTangentDomain]
  infer_instance

end

/-! The global addition morphism. Sixteen local pieces (a pair of affine charts, one of the two
homogeneous addition laws of `CubicAddLaws.lean`, an output chart) cover `E ⊗ E`; each one
computes the sum on complex points, so the pieces agree on overlaps because the chart products
are reduced. -/

noncomputable section

/-! Morphisms into `E` from a reduced scheme of finite type over `ℂ` are determined by their
values on complex points. -/

private instance : IsSeparated E.hom := inferInstance

private instance : LocallyOfFiniteType E.hom := inferInstance

private theorem hom_ext_of_complexPoints {X : Scheme} (s : X ⟶ Spec ↧ℂ) [IsReduced X]
    [LocallyOfFiniteType s] {f g : X ⟶ E.left} (hf : f ≫ E.hom = s) (hg : g ≫ E.hom = s)
    (H : ∀ p : Spec ↧ℂ ⟶ X, p ≫ s = 𝟙 _ → p ≫ f = p ≫ g) : f = g := by
  have : LocallyOfFiniteType (f ≫ E.hom) := by rw [hf]; infer_instance
  refine ext_of_apply_eq (K := ℂ) E.hom Set.univ isOpen_univ.isLocallyClosed dense_univ ?_
    (hf.trans hg.symm)
  intro x _ hx
  have hp := pointOfClosedPoint_comp s x hx
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  rw [← pointOfClosedPoint_apply s x hx a]
  change (pointOfClosedPoint s x hx ≫ f) a = (pointOfClosedPoint s x hx ≫ g) a
  rw [H _ hp]

/-- An affine chart of `E` with homogeneous coordinates, normalized at index `j`. -/
private structure CubicChart where
  A : Type
  [cr : CommRing A]
  [alg : Algebra ℂ A]
  [dom : IsDomain A]
  map : Spec ↧A ⟶ E.left
  [isOpen : IsOpenImmersion map]
  over : map ≫ E.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
  coords : Fin 3 → A
  isCubic : IsCubicTriple coords
  j : Fin 3
  out : ∀ {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L), IsCubicTriple s →
    ∀ u : L, s j * u = 1 → (A →+* L)
  out_coords : ∀ {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : IsCubicTriple s)
    (u : L) (hu : s j * u = 1) (k : Fin 3), out s hs u hu (coords k) = s k * u
  out_algebraMap : ∀ {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L)
    (hs : IsCubicTriple s) (u : L) (hu : s j * u = 1),
    (out s hs u hu).comp (algebraMap ℂ A) = algebraMap ℂ L
  point : ∀ ψ : A →+* ℂ, ψ.comp (algebraMap ℂ A) = RingHom.id ℂ →
    ∃ t : ℂ, t ≠ 0 ∧ ∃ P : W.toAffine.Point,
      Spec.map (CommRingCat.ofHom ψ) ≫ map = (complexPointOfAffine P).left ∧
        ∀ k, ψ (coords k) = t * cubicHomCoords P k

attribute [instance] CubicChart.cr CubicChart.alg CubicChart.dom CubicChart.isOpen

private instance : IsOpenImmersion zChartMap := by
  dsimp [zChartMap]
  infer_instance

private theorem addA_isCubicTriple : IsCubicTriple (![addXCoord, addYCoord, 1] : Fin 3 → AddA) := by
  simp only [IsCubicTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination addA_relation

private theorem zOut_eval {L : Type} [CommRing L] [Algebra ℂ L] (a b : L) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ L) a) b W.toAffine.polynomial =
      b ^ 2 - a ^ 3 - a := by
  simp [WeierstrassCurve.Affine.polynomial, W, WeierstrassCurve.ofJ1728,
    Polynomial.eval₂_eval₂RingHom_apply, Polynomial.evalEval_C]
  ring

private def zOut {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : IsCubicTriple s) (u : L)
    (hu : s 2 * u = 1) : AddA →+* L :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℂ L) (s 0 * u)) (s 1 * u) (by
    rw [zOut_eval]
    unfold IsCubicTriple at hs
    linear_combination u ^ 3 * hs + (s 0 * u * (s 2 * u + 1) - s 1 ^ 2 * u ^ 2) * hu)

private theorem zOut_coords {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : IsCubicTriple s)
    (u : L) (hu : s 2 * u = 1) (k : Fin 3) :
    zOut s hs u hu ((![addXCoord, addYCoord, 1] : Fin 3 → AddA) k) = s k * u := by
  fin_cases k
  · simp [zOut, addXCoord]
  · simp [zOut, addYCoord]
  · simpa using hu.symm

private theorem zOut_algebraMap {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L)
    (hs : IsCubicTriple s) (u : L) (hu : s 2 * u = 1) :
    (zOut s hs u hu).comp (algebraMap ℂ AddA) = algebraMap ℂ L := by
  ext c
  change zOut s hs u hu ((AdjoinRoot.mk W.toAffine.polynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [zOut]

private theorem zChart_point (ψ : AddA →+* ℂ) (hψ : ψ.comp (algebraMap ℂ AddA) = RingHom.id ℂ) :
    ∃ t : ℂ, t ≠ 0 ∧ ∃ P : W.toAffine.Point,
      Spec.map (CommRingCat.ofHom ψ) ≫ zChartMap = (complexPointOfAffine P).left ∧
        ∀ k, ψ ((![addXCoord, addYCoord, 1] : Fin 3 → AddA) k) = t * cubicHomCoords P k := by
  let x := ψ addXCoord
  let y := ψ addYCoord
  have hxy : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff_nonsingular, cubic_nonsingular_iff]
    have h := congrArg ψ addA_relation
    simp only [map_sub, map_pow, map_zero] at h
    linear_combination h
  have hψ' : ψ = affineEval x y hxy := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        have := DFunLike.congr_fun hψ c
        simp only [RingHom.comp_apply, RingHom.id_apply, AdjoinRoot.algebraMap_eq'] at this
        simp [affineEval]
        exact this
      · simp [affineEval, x, addXCoord]
    · simp [affineEval, y, addYCoord]
  refine ⟨1, one_ne_zero, .some x y (W_equation_iff_nonsingular.mp hxy), ?_, ?_⟩
  · rw [hψ']
    rfl
  · intro k
    fin_cases k <;> simp [cubicHomCoords, x, y]

private def zCubicChart : CubicChart where
  A := AddA
  dom := zCoordinateRing_isDomain
  map := zChartMap
  over := zChartMap_over
  coords := ![addXCoord, addYCoord, 1]
  isCubic := addA_isCubicTriple
  j := 2
  out s hs u hu := zOut s hs u hu
  out_coords := zOut_coords
  out_algebraMap := zOut_algebraMap
  point := zChart_point

private abbrev yU : YCoordinateRing := AdjoinRoot.of yAffinePolynomial Polynomial.X
private abbrev yV : YCoordinateRing := AdjoinRoot.root yAffinePolynomial

private theorem yCoords_isCubicTriple : IsCubicTriple (![yU, 1, yV] : Fin 3 → YCoordinateRing) := by
  simp only [IsCubicTriple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination yChart_equation

private def yOut {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : IsCubicTriple s) (w : L)
    (hw : s 1 * w = 1) : YCoordinateRing →+* L :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℂ L) (s 0 * w)) (s 2 * w) (by
    simp [yAffinePolynomial, Polynomial.eval₂_eval₂RingHom_apply, Polynomial.evalEval_C]
    unfold IsCubicTriple at hs
    linear_combination w ^ 3 * hs - s 2 * w * (1 + s 1 * w) * hw)

private theorem yOut_coords {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : IsCubicTriple s)
    (w : L) (hw : s 1 * w = 1) (k : Fin 3) :
    yOut s hs w hw ((![yU, 1, yV] : Fin 3 → YCoordinateRing) k) = s k * w := by
  fin_cases k
  · simp [yOut, yU]
  · simpa using hw.symm
  · simp [yOut, yV]

private theorem yOut_algebraMap {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L)
    (hs : IsCubicTriple s) (w : L) (hw : s 1 * w = 1) :
    (yOut s hs w hw).comp (algebraMap ℂ YCoordinateRing) = algebraMap ℂ L := by
  ext c
  change yOut s hs w hw ((AdjoinRoot.mk yAffinePolynomial)
    (Polynomial.C (Polynomial.C c))) = _
  simp [yOut]

private theorem yChart_point (ψ : YCoordinateRing →+* ℂ)
    (hψ : ψ.comp (algebraMap ℂ YCoordinateRing) = RingHom.id ℂ) :
    ∃ t : ℂ, t ≠ 0 ∧ ∃ P : W.toAffine.Point,
      Spec.map (CommRingCat.ofHom ψ) ≫ yChartMap = (complexPointOfAffine P).left ∧
        ∀ k, ψ ((![yU, 1, yV] : Fin 3 → YCoordinateRing) k) = t * cubicHomCoords P k := by
  let u := ψ yU
  let v := ψ yV
  have huv : v = u ^ 3 + u * v ^ 2 := by
    have h := congrArg ψ yChart_equation
    simpa [u, v] using h
  have hC (c : ℂ) : ψ (AdjoinRoot.of yAffinePolynomial (Polynomial.C c)) = c := by
    have := DFunLike.congr_fun hψ c
    simp only [RingHom.comp_apply, RingHom.id_apply, AdjoinRoot.algebraMap_eq'] at this
    exact this
  by_cases hv : v = 0
  · have hu : u = 0 := yChart_zero_second_coordinate huv hv
    have hψ' : ψ = infinityCoordinates := by
      apply AdjoinRoot.ringHom_ext
      · apply Polynomial.ringHom_ext
        · intro c
          have hscalar : infinityCoordinates.comp (algebraMap ℂ YCoordinateRing) =
              RingHom.id ℂ := by
            have hp : Spec.map (CommRingCat.ofHom infinityCoordinates) ≫
                Spec.map (CommRingCat.ofHom (algebraMap ℂ YCoordinateRing)) = 𝟙 (Spec ↧ℂ) := by
              rw [← yChartMap_over, ← Category.assoc, infinity_chart, infinity_over]
            apply DFunLike.ext
            intro c
            have h' := congrArg Spec.preimage hp
            simpa [Spec.preimage_comp] using
              DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') c
          rw [RingHom.comp_apply, RingHom.comp_apply, hC]
          exact (DFunLike.congr_fun hscalar c).symm
        · change u = infinityCoordinates yU
          rw [hu, infinityCoordinates_values.1]
      · change v = infinityCoordinates yV
        rw [hv, infinityCoordinates_values.2]
    refine ⟨1, one_ne_zero, 0, ?_, ?_⟩
    · rw [hψ', infinity_chart]
      rfl
    · intro k
      fin_cases k
      · simpa [cubicHomCoords] using hu
      · simp [cubicHomCoords]
      · simpa [cubicHomCoords] using hv
  · have hP : W.toAffine.Nonsingular (u / v) (1 / v) := by
      rw [cubic_nonsingular_iff]
      field_simp
      linear_combination huv
    refine ⟨v, hv, .some (u / v) (1 / v) hP, ?_, ?_⟩
    · let ψ' := IsLocalization.Away.lift (S := Localization.Away yV) yV
        (g := ψ) (isUnit_iff_ne_zero.mpr hv)
      have hψψ' : ψ = ψ'.comp (algebraMap YCoordinateRing (Localization.Away yV)) :=
        (IsLocalization.Away.lift_comp _ _).symm
      have hinv : ψ' (IsLocalization.Away.invSelf yV) = 1 / v := by
        have h := congrArg ψ' (IsLocalization.Away.mul_invSelf yV (S := Localization.Away yV))
        rw [map_mul, map_one, IsLocalization.Away.lift_eq] at h
        field_simp
        linear_combination h
      have heval : ψ'.comp yToZCoordinates = affineEval (u / v) (1 / v) hP.1 := by
        apply AdjoinRoot.ringHom_ext
        · apply Polynomial.ringHom_ext
          · intro c
            have h1 := DFunLike.congr_fun yToZCoordinates_over c
            simp only [RingHom.comp_apply] at h1 ⊢
            change ψ' (yToZCoordinates (algebraMap ℂ _ c)) = _
            rw [h1, IsScalarTower.algebraMap_apply ℂ YCoordinateRing (Localization.Away yV),
              IsLocalization.Away.lift_eq]
            simp [affineEval]
            exact hC c
          · simp only [RingHom.comp_apply]
            rw [yToZCoordinates_x, map_mul, IsLocalization.Away.lift_eq, hinv]
            simp [affineEval, u]
            ring
        · simp only [RingHom.comp_apply]
          rw [yToZCoordinates_y, hinv]
          simp [affineEval]
      change Spec.map (CommRingCat.ofHom ψ) ≫ yChartMap =
        Spec.map (CommRingCat.ofHom (affineEval (u / v) (1 / v) hP.1)) ≫ zChartMap
      have e₁ : Spec.map (CommRingCat.ofHom ψ) = Spec.map (CommRingCat.ofHom ψ') ≫
          Spec.map (CommRingCat.ofHom (algebraMap YCoordinateRing (Localization.Away yV))) := by
        rw [← Spec.map_comp, hψψ']
        rfl
      have e₂ : Spec.map (CommRingCat.ofHom (affineEval (u / v) (1 / v) hP.1)) =
          Spec.map (CommRingCat.ofHom ψ') ≫ Spec.map (CommRingCat.ofHom yToZCoordinates) := by
        rw [← Spec.map_comp, ← heval]
        rfl
      rw [e₁, e₂, Category.assoc, Category.assoc, transition_agreement_y]
    · intro k
      fin_cases k
      · simp [cubicHomCoords, u]
        field_simp
      · simp [cubicHomCoords]
        field_simp
      · simp [cubicHomCoords, v]

private def yCubicChart : CubicChart where
  A := YCoordinateRing
  dom := yCoordinateRing_isDomain
  map := yChartMap
  over := yChartMap_over
  coords := ![yU, 1, yV]
  isCubic := yCoords_isCubicTriple
  j := 1
  out s hs u hu := yOut s hs u hu
  out_coords := yOut_coords
  out_algebraMap := yOut_algebraMap
  point := yChart_point

private def cubicChart : Bool → CubicChart
  | false => zCubicChart
  | true => yCubicChart

private abbrev PairRing (b : Bool × Bool) : Type := (cubicChart b.1).A ⊗[ℂ] (cubicChart b.2).A

private def pairLeft (b : Bool × Bool) : Fin 3 → PairRing b := fun k ↦
  Algebra.TensorProduct.includeLeftRingHom ((cubicChart b.1).coords k)

private def pairRight (b : Bool × Bool) : Fin 3 → PairRing b := fun k ↦
  Algebra.TensorProduct.includeRight ((cubicChart b.2).coords k)

private def cubicLaw (ℓ : Bool) {R : Type*} [CommRing R] (p q : Fin 3 → R) : Fin 3 → R :=
  cond ℓ (cubicLawY p q) (cubicLawZ p q)

private theorem cubicLaw_isCubicTriple (ℓ : Bool) {R : Type*} [CommRing R] {p q : Fin 3 → R}
    (hp : IsCubicTriple p) (hq : IsCubicTriple q) : IsCubicTriple (cubicLaw ℓ p q) := by
  cases ℓ
  · exact cubicLawZ_isCubicTriple hp hq
  · exact cubicLawY_isCubicTriple hp hq

private theorem cubicLaw_smul (ℓ : Bool) {R : Type*} [CommRing R] (c d : R) (p q : Fin 3 → R) :
    cubicLaw ℓ (fun k ↦ c * p k) (fun k ↦ d * q k) =
      fun k ↦ c ^ 2 * d ^ 2 * cubicLaw ℓ p q k := by
  cases ℓ
  · exact cubicLawZ_smul c d p q
  · exact cubicLawY_smul c d p q

private theorem map_cubicLaw (ℓ : Bool) {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p q : Fin 3 → R) (k : Fin 3) :
    f (cubicLaw ℓ p q k) = cubicLaw ℓ (fun i ↦ f (p i)) (fun i ↦ f (q i)) k := by
  cases ℓ
  · exact map_cubicLawZ f p q k
  · exact map_cubicLawY f p q k

private theorem cubicLaw_correct (ℓ : Bool) (P Q : W.toAffine.Point)
    (h : cubicLaw ℓ (cubicHomCoords P) (cubicHomCoords Q) 1 ≠ 0 ∨
      cubicLaw ℓ (cubicHomCoords P) (cubicHomCoords Q) 2 ≠ 0) :
    cubicProjPoint (cubicLaw ℓ (cubicHomCoords P) (cubicHomCoords Q))
      (cubicLaw_isCubicTriple ℓ (cubicHomCoords_isCubicTriple P)
        (cubicHomCoords_isCubicTriple Q)) = P + Q := by
  cases ℓ
  · exact cubicLawZ_correct P Q h
  · exact cubicLawY_correct P Q h

private theorem pairLeft_isCubicTriple (b : Bool × Bool) : IsCubicTriple (pairLeft b) := by
  have h := congrArg (Algebra.TensorProduct.includeLeftRingHom (R := ℂ)
    (A := (cubicChart b.1).A) (B := (cubicChart b.2).A)) (cubicChart b.1).isCubic
  unfold IsCubicTriple at h ⊢
  simp only [pairLeft, map_mul, map_pow, map_add] at h ⊢
  exact h

private theorem pairRight_isCubicTriple (b : Bool × Bool) : IsCubicTriple (pairRight b) := by
  have h := congrArg (Algebra.TensorProduct.includeRight (R := ℂ)
    (A := (cubicChart b.1).A) (B := (cubicChart b.2).A)) (cubicChart b.2).isCubic
  unfold IsCubicTriple at h ⊢
  simp only [pairRight, map_mul, map_pow, map_add] at h ⊢
  exact h

private abbrev PieceIndex : Type := (Bool × Bool) × Bool × Bool

private def pieceTriple (i : PieceIndex) : Fin 3 → PairRing i.1 :=
  cubicLaw i.2.1 (pairLeft i.1) (pairRight i.1)

private theorem pieceTriple_isCubicTriple (i : PieceIndex) : IsCubicTriple (pieceTriple i) :=
  cubicLaw_isCubicTriple _ (pairLeft_isCubicTriple _) (pairRight_isCubicTriple _)

private abbrev PieceRing (i : PieceIndex) : Type :=
  Localization.Away (pieceTriple i (cubicChart i.2.2).j)

private def pieceValues (i : PieceIndex) : Fin 3 → PieceRing i := fun k ↦
  algebraMap (PairRing i.1) (PieceRing i) (pieceTriple i k)

private theorem pieceValues_isCubicTriple (i : PieceIndex) : IsCubicTriple (pieceValues i) := by
  have h := congrArg (algebraMap (PairRing i.1) (PieceRing i)) (pieceTriple_isCubicTriple i)
  unfold IsCubicTriple at h ⊢
  simp only [pieceValues, map_mul, map_pow, map_add] at h ⊢
  exact h

private theorem pieceValues_inv (i : PieceIndex) :
    pieceValues i (cubicChart i.2.2).j * IsLocalization.Away.invSelf
      (pieceTriple i (cubicChart i.2.2).j) = 1 :=
  IsLocalization.Away.mul_invSelf _

private def pieceOut (i : PieceIndex) : (cubicChart i.2.2).A →+* PieceRing i :=
  (cubicChart i.2.2).out (pieceValues i) (pieceValues_isCubicTriple i) _ (pieceValues_inv i)

private def pieceLocal (i : PieceIndex) : Spec ↧(PieceRing i) ⟶ E.left :=
  Spec.map (CommRingCat.ofHom (pieceOut i)) ≫ (cubicChart i.2.2).map

private def pairMap (b : Bool × Bool) : Spec ↧(PairRing b) ⟶ (E ⊗ E).left :=
  (pullbackSpecIso ℂ (cubicChart b.1).A (cubicChart b.2).A).inv ≫
    pullback.map _ _ _ _ (cubicChart b.1).map (cubicChart b.2).map (𝟙 _)
      (by rw [Category.comp_id, (cubicChart b.1).over])
      (by rw [Category.comp_id, (cubicChart b.2).over])

private instance (b : Bool × Bool) : IsOpenImmersion (pairMap b) := by
  dsimp [pairMap]
  infer_instance

private def pieceMap (i : PieceIndex) : Spec ↧(PieceRing i) ⟶ (E ⊗ E).left :=
  Spec.map (CommRingCat.ofHom (algebraMap (PairRing i.1) (PieceRing i))) ≫ pairMap i.1

private instance (i : PieceIndex) : IsOpenImmersion (pieceMap i) := by
  dsimp [pieceMap]
  infer_instance

private theorem pairMap_fst (b : Bool × Bool) :
    pairMap b ≫ pullback.fst E.hom E.hom =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (cubicChart b.1).map := by
  rw [pairMap, Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]

private theorem pairMap_snd (b : Bool × Bool) :
    pairMap b ≫ pullback.snd E.hom E.hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℂ)
        (A := (cubicChart b.1).A) (B := (cubicChart b.2).A)).toRingHom) ≫
        (cubicChart b.2).map := by
  rw [pairMap, Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

private theorem pairMap_over (b : Bool × Bool) :
    pairMap b ≫ (E ⊗ E).hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (PairRing b))) := by
  rw [Over.tensorObj_hom, ← Category.assoc, pairMap_fst, Category.assoc, (cubicChart b.1).over,
    ← Spec.map_comp]
  rfl

private theorem pieceMap_over (i : PieceIndex) :
    pieceMap i ≫ (E ⊗ E).hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i))) := by
  rw [pieceMap, Category.assoc, pairMap_over, ← Spec.map_comp]
  congr 1

private theorem pieceLocal_over (i : PieceIndex) :
    pieceLocal i ≫ E.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i))) := by
  rw [pieceLocal, Category.assoc, (cubicChart i.2.2).over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (cubicChart i.2.2).out_algebraMap _ _ _ _

/-- A complex point of an affine `ℂ`-scheme is a `ℂ`-algebra map to `ℂ`. -/
private theorem exists_ringHom_of_point {R : Type} [CommRing R] [Algebra ℂ R]
    (r : Spec ↧ℂ ⟶ Spec ↧R)
    (hr : r ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)) = 𝟙 _) :
    ∃ ρ : R →+* ℂ, ρ.comp (algebraMap ℂ R) = RingHom.id ℂ ∧
      r = Spec.map (CommRingCat.ofHom ρ) := by
  refine ⟨(Spec.preimage r).hom, ?_, by simp⟩
  have h := congrArg Spec.preimage hr
  rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at h
  exact congrArg CommRingCat.Hom.hom h

private noncomputable def cubicPointEquiv : W.toAffine.Point ≃ ComplexPoint E :=
  Equiv.ofBijective complexPointOfAffine
    ⟨complexPointOfAffine_injective, complexPointOfAffine_surjective⟩

open scoped Classical in
/-- The point of `W` attached to a complex point of `E`, or zero for a morphism not over `ℂ`. -/
private def pointOf (p : Spec ↧ℂ ⟶ E.left) : W.toAffine.Point :=
  if h : p ≫ E.hom = 𝟙 _ then cubicPointEquiv.symm (Over.homMk p h) else 0

private theorem pointOf_left (P : W.toAffine.Point) : pointOf (complexPointOfAffine P).left = P := by
  have h : (complexPointOfAffine P).left ≫ E.hom = 𝟙 (Spec ↧ℂ) := Over.w (complexPointOfAffine P)
  simp only [pointOf, h, ↓reduceDIte]
  apply cubicPointEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- The sum of the two components of a complex point of `E ⊗ E`. -/
private def cubicAddPoint (q : Spec ↧ℂ ⟶ (E ⊗ E).left) : Spec ↧ℂ ⟶ E.left :=
  (complexPointOfAffine (pointOf (q ≫ pullback.fst _ _) + pointOf (q ≫ pullback.snd _ _))).left

private theorem cubicHomCoords_ne (P : W.toAffine.Point) :
    cubicHomCoords P 1 ≠ 0 ∨ cubicHomCoords P 2 ≠ 0 := by
  cases P with
  | zero => left; simp [cubicHomCoords]
  | some x y h => right; simp [cubicHomCoords]

private theorem cubicProjPoint_congr {s s' : Fin 3 → ℂ} (h : s = s') (hs : IsCubicTriple s)
    (hs' : IsCubicTriple s') : cubicProjPoint s hs = cubicProjPoint s' hs' := by
  subst h
  rfl

private theorem includeLeft_over {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (Ψ : A ⊗[ℂ] B →+* ℂ) (hΨ : Ψ.comp (algebraMap ℂ (A ⊗[ℂ] B)) = RingHom.id ℂ) :
    (Ψ.comp Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap ℂ A) = RingHom.id ℂ := by
  ext c
  have := DFunLike.congr_fun hΨ c
  simpa [Algebra.TensorProduct.algebraMap_apply] using this

private theorem includeRight_over {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (Ψ : A ⊗[ℂ] B →+* ℂ) (hΨ : Ψ.comp (algebraMap ℂ (A ⊗[ℂ] B)) = RingHom.id ℂ) :
    (Ψ.comp (Algebra.TensorProduct.includeRight (R := ℂ) (A := A) (B := B)).toRingHom).comp
      (algebraMap ℂ B) = RingHom.id ℂ := by
  ext c
  have := DFunLike.congr_fun hΨ c
  simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes] at this ⊢
  exact this

private theorem pairMap_spec (b : Bool × Bool) (Ψ : PairRing b →+* ℂ) :
    Spec.map (CommRingCat.ofHom Ψ) ≫ pairMap b ≫ pullback.fst E.hom E.hom =
        Spec.map (CommRingCat.ofHom (Ψ.comp Algebra.TensorProduct.includeLeftRingHom)) ≫
          (cubicChart b.1).map ∧
      Spec.map (CommRingCat.ofHom Ψ) ≫ pairMap b ≫ pullback.snd E.hom E.hom =
        Spec.map (CommRingCat.ofHom (Ψ.comp (Algebra.TensorProduct.includeRight (R := ℂ)
          (A := (cubicChart b.1).A) (B := (cubicChart b.2).A)).toRingHom)) ≫
          (cubicChart b.2).map := by
  constructor
  · rw [pairMap_fst, ← Category.assoc, ← Spec.map_comp]
    rfl
  · rw [pairMap_snd, ← Category.assoc, ← Spec.map_comp]
    rfl

private theorem pieceTriple_values (i : PieceIndex) (Ψ : PairRing i.1 →+* ℂ) {t₁ t₂ : ℂ}
    {P₁ P₂ : W.toAffine.Point}
    (hv₁ : ∀ k, (Ψ.comp Algebra.TensorProduct.includeLeftRingHom) ((cubicChart i.1.1).coords k) =
      t₁ * cubicHomCoords P₁ k)
    (hv₂ : ∀ k, (Ψ.comp (Algebra.TensorProduct.includeRight (R := ℂ)
      (A := (cubicChart i.1.1).A) (B := (cubicChart i.1.2).A)).toRingHom)
        ((cubicChart i.1.2).coords k) = t₂ * cubicHomCoords P₂ k) (k : Fin 3) :
    Ψ (pieceTriple i k) =
      t₁ ^ 2 * t₂ ^ 2 * cubicLaw i.2.1 (cubicHomCoords P₁) (cubicHomCoords P₂) k := by
  rw [pieceTriple, map_cubicLaw]
  have e₁ : (fun k ↦ Ψ (pairLeft i.1 k)) = fun k ↦ t₁ * cubicHomCoords P₁ k := funext hv₁
  have e₂ : (fun k ↦ Ψ (pairRight i.1 k)) = fun k ↦ t₂ * cubicHomCoords P₂ k := funext hv₂
  rw [e₁, e₂, cubicLaw_smul]

private theorem pieceLocal_point (i : PieceIndex) (r : Spec ↧ℂ ⟶ Spec ↧(PieceRing i))
    (hr : r ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i))) = 𝟙 _) :
    r ≫ pieceLocal i = cubicAddPoint (r ≫ pieceMap i) := by
  obtain ⟨ρ, hρ, rfl⟩ := exists_ringHom_of_point r hr
  set Ψ : PairRing i.1 →+* ℂ := ρ.comp (algebraMap (PairRing i.1) (PieceRing i)) with hΨ
  have hΨalg : Ψ.comp (algebraMap ℂ (PairRing i.1)) = RingHom.id ℂ := by
    rw [hΨ, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hρ]
  obtain ⟨t₁, ht₁, P₁, hP₁, hv₁⟩ := (cubicChart i.1.1).point _ (includeLeft_over Ψ hΨalg)
  obtain ⟨t₂, ht₂, P₂, hP₂, hv₂⟩ := (cubicChart i.1.2).point _ (includeRight_over Ψ hΨalg)
  have hspec := pairMap_spec i.1 Ψ
  have hfst : (Spec.map (CommRingCat.ofHom ρ) ≫ pieceMap i) ≫ pullback.fst E.hom E.hom =
      (complexPointOfAffine P₁).left := by
    rw [← hP₁, ← hspec.1, pieceMap]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map _), ← Spec.map_comp]
    rfl
  have hsnd : (Spec.map (CommRingCat.ofHom ρ) ≫ pieceMap i) ≫ pullback.snd E.hom E.hom =
      (complexPointOfAffine P₂).left := by
    rw [← hP₂, ← hspec.2, pieceMap]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map _), ← Spec.map_comp]
    rfl
  set χ := ρ.comp (pieceOut i) with hχdef
  have hχ : χ.comp (algebraMap ℂ _) = RingHom.id ℂ := by
    rw [hχdef, RingHom.comp_assoc, pieceOut, (cubicChart i.2.2).out_algebraMap, hρ]
  obtain ⟨t₃, ht₃, P₃, hP₃, hv₃⟩ := (cubicChart i.2.2).point χ hχ
  set lam := ρ (IsLocalization.Away.invSelf (pieceTriple i (cubicChart i.2.2).j)) with hlamdef
  have hout (k : Fin 3) : χ ((cubicChart i.2.2).coords k) = Ψ (pieceTriple i k) * lam := by
    rw [hχdef, RingHom.comp_apply, pieceOut, (cubicChart i.2.2).out_coords, map_mul]
    rfl
  have hlam : Ψ (pieceTriple i (cubicChart i.2.2).j) * lam = 1 := by
    have h := congrArg ρ (pieceValues_inv i)
    rw [map_mul, map_one] at h
    exact h
  have hlam0 : lam ≠ 0 := right_ne_zero_of_mul_eq_one hlam
  have hval := pieceTriple_values i Ψ hv₁ hv₂
  have hlaw : cubicLaw i.2.1 (cubicHomCoords P₁) (cubicHomCoords P₂) =
      fun k ↦ t₃ / (t₁ ^ 2 * t₂ ^ 2 * lam) * cubicHomCoords P₃ k := by
    funext k
    have h := hv₃ k
    rw [hout, hval] at h
    field_simp
    linear_combination h
  have hc : t₃ / (t₁ ^ 2 * t₂ ^ 2 * lam) ≠ 0 := by
    have := pow_ne_zero 2 ht₁
    have := pow_ne_zero 2 ht₂
    positivity
  have hne : cubicLaw i.2.1 (cubicHomCoords P₁) (cubicHomCoords P₂) 1 ≠ 0 ∨
      cubicLaw i.2.1 (cubicHomCoords P₁) (cubicHomCoords P₂) 2 ≠ 0 := by
    rw [hlaw]
    rcases cubicHomCoords_ne P₃ with h | h
    · exact Or.inl (mul_ne_zero hc h)
    · exact Or.inr (mul_ne_zero hc h)
  have hsum : P₁ + P₂ = P₃ := by
    rw [← cubicLaw_correct _ P₁ P₂ hne]
    rw [cubicProjPoint_congr hlaw _ (by
      rw [← hlaw]
      exact cubicLaw_isCubicTriple _ (cubicHomCoords_isCubicTriple P₁)
        (cubicHomCoords_isCubicTriple P₂))]
    rw [cubicProjPoint_smul (cubicHomCoords_isCubicTriple P₃) hc, cubicProjPoint_homCoords]
  calc Spec.map (CommRingCat.ofHom ρ) ≫ pieceLocal i =
        Spec.map (CommRingCat.ofHom χ) ≫ (cubicChart i.2.2).map := by
          rw [pieceLocal, ← Category.assoc, ← Spec.map_comp]
          rfl
    _ = (complexPointOfAffine P₃).left := hP₃
    _ = cubicAddPoint (Spec.map (CommRingCat.ofHom ρ) ≫ pieceMap i) := by
          rw [cubicAddPoint, hfst, hsnd, pointOf_left, pointOf_left, hsum]

private theorem infinityCoordinates_comp :
    infinityCoordinates.comp (algebraMap ℂ YCoordinateRing) = RingHom.id ℂ := by
  have hp : Spec.map (CommRingCat.ofHom infinityCoordinates) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ YCoordinateRing)) = 𝟙 (Spec ↧ℂ) := by
    rw [← yChartMap_over, ← Category.assoc, infinity_chart, infinity_over]
  apply DFunLike.ext
  intro c
  have h' := congrArg Spec.preimage hp
  simpa [Spec.preimage_comp] using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') c

private theorem affineEval_comp (x y : ℂ) (h : W.toAffine.Equation x y) :
    (affineEval x y h).comp (algebraMap ℂ W.toAffine.CoordinateRing) = RingHom.id ℂ := by
  ext c
  change (affineEval x y h)
    ((AdjoinRoot.mk W.toAffine.polynomial) (Polynomial.C (Polynomial.C c))) = c
  simp [affineEval]

/-- Every complex point of `E` lies in one of the two charts. -/
private theorem exists_chart_point (p : Spec ↧ℂ ⟶ E.left) (hp : p ≫ E.hom = 𝟙 _) :
    ∃ b : Bool, ∃ ψ : (cubicChart b).A →+* ℂ, ψ.comp (algebraMap ℂ _) = RingHom.id ℂ ∧
      Spec.map (CommRingCat.ofHom ψ) ≫ (cubicChart b).map = p := by
  let P : ComplexPoint E := Over.homMk p hp
  by_cases hP : P = Over.homMk infinity infinity_over
  · refine ⟨true, infinityCoordinates, infinityCoordinates_comp, ?_⟩
    have := congrArg Over.Hom.left hP
    exact infinity_chart.trans this.symm
  · obtain ⟨x, y, h, hxy⟩ := zChart_factorization P (mem_zChart_of_ne_infinity P hP)
    exact ⟨false, affineEval x y h, affineEval_comp x y h, hxy.symm⟩

private theorem exists_piece_lift (i : PieceIndex) (Ψ : PairRing i.1 →+* ℂ)
    (hne : Ψ (pieceTriple i (cubicChart i.2.2).j) ≠ 0) (q : Spec ↧ℂ ⟶ (E ⊗ E).left)
    (hq : Spec.map (CommRingCat.ofHom Ψ) ≫ pairMap i.1 = q) :
    ∃ r : Spec ↧ℂ ⟶ Spec ↧(PieceRing i), r ≫ pieceMap i = q := by
  let ρ : PieceRing i →+* ℂ := IsLocalization.Away.lift (S := PieceRing i)
    (pieceTriple i (cubicChart i.2.2).j) (g := Ψ) (isUnit_iff_ne_zero.mpr hne)
  have hρ : ρ.comp (algebraMap (PairRing i.1) (PieceRing i)) = Ψ :=
    IsLocalization.Away.lift_comp _ _
  refine ⟨Spec.map (CommRingCat.ofHom ρ), ?_⟩
  rw [pieceMap, ← Category.assoc, ← Spec.map_comp, ← hq, ← hρ]
  rfl

/-- Every complex point of `E ⊗ E` lies in one of the sixteen pieces. -/
private theorem exists_piece_point (q : Spec ↧ℂ ⟶ (E ⊗ E).left) (hq : q ≫ (E ⊗ E).hom = 𝟙 _) :
    ∃ i : PieceIndex, ∃ r : Spec ↧ℂ ⟶ Spec ↧(PieceRing i), r ≫ pieceMap i = q := by
  have hq₁ : (q ≫ pullback.fst E.hom E.hom) ≫ E.hom = 𝟙 _ := by
    rw [Category.assoc]
    exact hq
  have hq₂ : (q ≫ pullback.snd E.hom E.hom) ≫ E.hom = 𝟙 _ := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact hq₁
  obtain ⟨b₁, ψ₁, hψ₁, h₁⟩ := exists_chart_point _ hq₁
  obtain ⟨b₂, ψ₂, hψ₂, h₂⟩ := exists_chart_point _ hq₂
  let ψ₁' : (cubicChart b₁).A →ₐ[ℂ] ℂ :=
    { toRingHom := ψ₁, commutes' := fun c ↦ DFunLike.congr_fun hψ₁ c }
  let ψ₂' : (cubicChart b₂).A →ₐ[ℂ] ℂ :=
    { toRingHom := ψ₂, commutes' := fun c ↦ DFunLike.congr_fun hψ₂ c }
  let Ψ' := Algebra.TensorProduct.lift ψ₁' ψ₂' (fun _ _ ↦ Commute.all _ _)
  let Ψ : PairRing (b₁, b₂) →+* ℂ := Ψ'.toRingHom
  have hΨalg : Ψ.comp (algebraMap ℂ (PairRing (b₁, b₂))) = RingHom.id ℂ := by
    ext c
    exact Ψ'.commutes c
  have hΨ₁ : Ψ.comp Algebra.TensorProduct.includeLeftRingHom = ψ₁ := by
    ext a
    simp [Ψ, Ψ', ψ₁']
  have hΨ₂ : Ψ.comp (Algebra.TensorProduct.includeRight (R := ℂ)
      (A := (cubicChart b₁).A) (B := (cubicChart b₂).A)).toRingHom = ψ₂ := by
    ext a
    simp [Ψ, Ψ', ψ₂']
  have hΨq : Spec.map (CommRingCat.ofHom Ψ) ≫ pairMap (b₁, b₂) = q := by
    have hspec := pairMap_spec (b₁, b₂) Ψ
    apply pullback.hom_ext
    · rw [Category.assoc, hspec.1]
      exact (congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f) ≫ (cubicChart b₁).map) hΨ₁).trans h₁
    · rw [Category.assoc, hspec.2]
      exact (congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f) ≫ (cubicChart b₂).map) hΨ₂).trans h₂
  obtain ⟨t₁, ht₁, P₁, -, hv₁⟩ := (cubicChart b₁).point _ (includeLeft_over Ψ hΨalg)
  obtain ⟨t₂, ht₂, P₂, -, hv₂⟩ := (cubicChart b₂).point _ (includeRight_over Ψ hΨalg)
  have ht : t₁ ^ 2 * t₂ ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht₁) (pow_ne_zero 2 ht₂)
  have key (ℓ o : Bool) (h : cubicLaw ℓ (cubicHomCoords P₁) (cubicHomCoords P₂)
      (cubicChart o).j ≠ 0) :
      ∃ i : PieceIndex, ∃ r : Spec ↧ℂ ⟶ Spec ↧(PieceRing i), r ≫ pieceMap i = q := by
    obtain ⟨r, hr⟩ := exists_piece_lift ((b₁, b₂), ℓ, o) Ψ (by
      rw [pieceTriple_values ((b₁, b₂), ℓ, o) Ψ hv₁ hv₂]
      exact mul_ne_zero ht h) q hΨq
    exact ⟨_, r, hr⟩
  rcases cubicLaw_exists_ne P₁ P₂ with h | h | h | h
  · exact key false true h
  · exact key false false h
  · exact key true true h
  · exact key true false h

private instance : LocallyOfFiniteType (E ⊗ E).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

private instance : JacobsonSpace (E ⊗ E).left := LocallyOfFiniteType.jacobsonSpace (E ⊗ E).hom

private theorem pieces_cover (x : (E ⊗ E).left) : ∃ i y, pieceMap i y = x := by
  by_contra hx
  push Not at hx
  let Z : Set (E ⊗ E).left := ⋂ i, (Set.range (pieceMap i))ᶜ
  have hZ : IsClosed Z :=
    isClosed_iInter fun i ↦ (pieceMap i).isOpenEmbedding.isOpen_range.isClosed_compl
  have hxZ : x ∈ Z := Set.mem_iInter.mpr fun i ⟨y, hy⟩ ↦ hx i y hy
  obtain ⟨c, hcZ, hc'⟩ := nonempty_inter_closedPoints ⟨x, hxZ⟩ hZ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  obtain ⟨i, r, hr⟩ := exists_piece_point (pointOfClosedPoint (E ⊗ E).hom c hc)
    (pointOfClosedPoint_comp _ _ _)
  obtain ⟨a⟩ : Nonempty (Spec ↧ℂ) := inferInstance
  have h : pieceMap i (r a) = c := by
    rw [← Scheme.Hom.comp_apply, hr, pointOfClosedPoint_apply]
  exact Set.mem_iInter.mp hcZ i ⟨r a, h⟩

private def pieceCover : (E ⊗ E).left.OpenCover :=
  Scheme.Cover.mkOfCovers PieceIndex (fun i ↦ Spec ↧(PieceRing i)) pieceMap pieces_cover

private theorem pairRing_isReduced (b : Bool × Bool) : _root_.IsReduced (PairRing b) := by
  rcases b with ⟨b₁, b₂⟩
  cases b₂
  · exact isReduced_tensor_zCoordinateRing (cubicChart b₁).A
  · exact isReduced_tensor_yCoordinateRing (cubicChart b₁).A

private instance (b : Bool × Bool) : _root_.IsReduced (PairRing b) := pairRing_isReduced b

private theorem pieceLocal_compatible (i j : PieceIndex) :
    pullback.fst (pieceMap i) (pieceMap j) ≫ pieceLocal i =
      pullback.snd (pieceMap i) (pieceMap j) ≫ pieceLocal j := by
  have : IsReduced (pullback (pieceMap i) (pieceMap j)) :=
    isReduced_of_isOpenImmersion (pullback.fst (pieceMap i) (pieceMap j))
  have hs : pullback.fst (pieceMap i) (pieceMap j) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i))) =
      pullback.fst (pieceMap i) (pieceMap j) ≫ pieceMap i ≫ (E ⊗ E).hom := by
    rw [pieceMap_over]
  have : LocallyOfFiniteType (pullback.fst (pieceMap i) (pieceMap j) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i)))) := by
    rw [hs]
    infer_instance
  have hj : pullback.snd (pieceMap i) (pieceMap j) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing j))) =
      pullback.fst (pieceMap i) (pieceMap j) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i))) := by
    rw [hs, ← pieceMap_over, ← Category.assoc, ← pullback.condition, Category.assoc]
  apply hom_ext_of_complexPoints _ (by rw [Category.assoc, pieceLocal_over])
    (by rw [Category.assoc, pieceLocal_over, hj])
  intro p hp
  have hr : (p ≫ pullback.fst (pieceMap i) (pieceMap j)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i))) = 𝟙 _ := by
    rw [Category.assoc]
    exact hp
  have hr' : (p ≫ pullback.snd (pieceMap i) (pieceMap j)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing j))) = 𝟙 _ := by
    rw [Category.assoc, hj]
    exact hp
  rw [← Category.assoc, pieceLocal_point i _ hr, ← Category.assoc, pieceLocal_point j _ hr',
    Category.assoc, Category.assoc, pullback.condition]

private def cubicAddLeft : (E ⊗ E).left ⟶ E.left :=
  pieceCover.glueMorphisms pieceLocal pieceLocal_compatible

private theorem pieceMap_cubicAddLeft (i : PieceIndex) : pieceMap i ≫ cubicAddLeft = pieceLocal i :=
  pieceCover.ι_glueMorphisms pieceLocal pieceLocal_compatible i

private theorem cubicAddLeft_over : cubicAddLeft ≫ E.hom = (E ⊗ E).hom := by
  refine pieceCover.hom_ext _ _ fun (i : PieceIndex) ↦ ?_
  change pieceMap i ≫ cubicAddLeft ≫ E.hom = pieceMap i ≫ (E ⊗ E).hom
  rw [← Category.assoc, pieceMap_cubicAddLeft, pieceLocal_over, pieceMap_over]

private def cubicAdd : E ⊗ E ⟶ E := Over.homMk cubicAddLeft cubicAddLeft_over

private theorem cubicAddLeft_point (q : Spec ↧ℂ ⟶ (E ⊗ E).left) (hq : q ≫ (E ⊗ E).hom = 𝟙 _) :
    q ≫ cubicAddLeft = cubicAddPoint q := by
  obtain ⟨i, r, hr⟩ := exists_piece_point q hq
  have hr' : r ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (PieceRing i))) = 𝟙 _ := by
    rw [← pieceMap_over, ← Category.assoc, hr, hq]
  rw [← hr, Category.assoc, pieceMap_cubicAddLeft, pieceLocal_point i r hr']

private theorem eq_cubicPointEquiv_symm (e : ComplexPoint E ≃ W.toAffine.Point)
    (he : IsCubicPointEquiv e) : e = cubicPointEquiv.symm := by
  ext P
  obtain ⟨A, rfl⟩ := cubicPointEquiv.surjective P
  rw [Equiv.symm_apply_apply]
  cases A with
  | zero => exact he.1 _ rfl
  | some x y h => exact he.2 x y h _ rfl

private theorem pointOf_complexPoint (P : ComplexPoint E) : pointOf P.left = cubicPointEquiv.symm P := by
  obtain ⟨A, rfl⟩ := cubicPointEquiv.surjective P
  rw [Equiv.symm_apply_apply]
  exact pointOf_left A

private theorem exists_add_morphism_main (e : ComplexPoint E ≃ W.toAffine.Point)
    (he : IsCubicPointEquiv e) :
    ∃ m : E ⊗ E ⟶ E, ∀ P Q : ComplexPoint E, lift P Q ≫ m = e.symm (e P + e Q) := by
  obtain rfl := eq_cubicPointEquiv_symm e he
  refine ⟨cubicAdd, fun P Q ↦ ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  change (lift P Q).left ≫ cubicAddLeft = _
  rw [cubicAddLeft_point _ (Over.w (lift P Q)), cubicAddPoint, Over.lift_left, pullback.lift_fst,
    pullback.lift_snd, pointOf_complexPoint, pointOf_complexPoint, Equiv.symm_symm]
  rfl

end

/-- Spec S2: addition is a morphism `E ⊗ E ⟶ E` over `Spec ℂ`. -/
theorem exists_add_morphism_aux (e : ComplexPoint E ≃ W.toAffine.Point)
    (he : IsCubicPointEquiv e) :
    ∃ m : E ⊗ E ⟶ E, ∀ P Q : ComplexPoint E, lift P Q ≫ m = e.symm (e P + e Q) :=
  exists_add_morphism_main e he

/-- Spec S3: negation is a morphism `E ⟶ E` over `Spec ℂ`. -/
theorem exists_neg_morphism_aux (e : ComplexPoint E ≃ W.toAffine.Point)
    (he : IsCubicPointEquiv e) :
    ∃ i : E ⟶ E, ∀ P : ComplexPoint E, P ≫ i = e.symm (-e P) := by
  refine ⟨cubicNegOver, ?_⟩
  intro P
  by_cases hP : P = Over.homMk infinity infinity_over
  · subst P
    have he0 : e (Over.homMk infinity infinity_over) = 0 :=
      he.1 _ rfl
    have ht : e.symm (-e (Over.homMk infinity infinity_over)) =
        Over.homMk infinity infinity_over := by
      apply e.injective
      rw [e.apply_symm_apply, he0, neg_zero]
    rw [ht]
    apply Over.OverMorphism.ext
    exact cubicNeg_infinity
  · obtain ⟨x, y, hxy, hleft⟩ :=
      zChart_point_eq_affineComplexPoint P (mem_zChart_of_ne_infinity P hP)
    have hPeq : P = affineComplexPoint x y hxy := hleft
    subst P
    let hns : W.toAffine.Nonsingular x y := W_equation_iff_nonsingular.mp hxy
    let hn := neg_equation hxy
    let hnns : W.toAffine.Nonsingular x (-y) := W_equation_iff_nonsingular.mp hn
    have heP : e (affineComplexPoint x y hxy) = .some x y hns :=
      he.2 x y hns _ (by simpa using affineComplexPoint_left x y hxy)
    have heN : e (affineComplexPoint x (-y) hn) = .some x (-y) hnns :=
      he.2 x (-y) hnns _ (by simpa using affineComplexPoint_left x (-y) hn)
    have hneg : -(.some x y hns : W.toAffine.Point) = .some x (-y) hnns := by
      rw [WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq]
      refine ⟨rfl, ?_⟩
      simp [WeierstrassCurve.Affine.negY, W, WeierstrassCurve.ofJ1728]
    have ht : e.symm (-e (affineComplexPoint x y hxy)) =
        affineComplexPoint x (-y) hn := by
      apply e.injective
      rw [e.apply_symm_apply, heP, hneg, heN]
    rw [ht]
    apply Over.OverMorphism.ext
    exact affineComplexPoint_cubicNeg x y hxy

end HodgeLean.Foundations.Curves
