import HodgeLean.Foundations.Program.CompensationCubicGroupDefs
import HodgeLean.Foundations.Program.CompensationCubicAddPoints
import HodgeLean.Foundations.Program.CompensationCubicReduced
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

set_option maxHeartbeats 400000

namespace HodgeLean.Foundations.Program.CompensationCubic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry.ComplexPoint
open scoped TensorProduct

private theorem W_equation_iff_nonsingular {x y : ℂ} :
    W.toAffine.Equation x y ↔ W.toAffine.Nonsingular x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular

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
    simp [W, HodgeLean.Foundations.Program.cp_W]
    apply sub_eq_zero.mp
    have hroot := congrArg φ (AdjoinRoot.eval₂_root W.toAffine.polynomial)
    rw [Polynomial.hom_eval₂] at hroot
    rw [hcoeff] at hroot
    rw [map_zero] at hroot
    rw [Polynomial.eval₂_evalRingHom,
      WeierstrassCurve.Affine.evalEval_polynomial] at hroot
    simpa [W, HodgeLean.Foundations.Program.cp_W, y, φα] using hroot
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

private theorem yChart_factorization (P : ComplexPoint E)
    (hP : P ∈ AlgebraicGeometry.Point.overOpen yChart) :
    ∃ (u v : ℂ) (h : v = u ^ 3 + v ^ 3),
      P.left = Spec.map (CommRingCat.ofHom (AdjoinRoot.lift (Polynomial.evalRingHom u) v (by
        rw [Polynomial.eval₂_evalRingHom]
        rw [yAffinePolynomial]
        rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
          Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
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
  have huv : v = u ^ 3 + v ^ 3 := by
    have h := congrArg ψ yChart_equation
    simpa [u, v, ψα] using h
  refine ⟨u, v, huv, ?_⟩
  let ev : YCoordinateRing →+* ℂ := AdjoinRoot.lift (Polynomial.evalRingHom u) v (by
    rw [Polynomial.eval₂_evalRingHom]
    rw [yAffinePolynomial]
    rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
      Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
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

private theorem yChart_zero_second_coordinate {u v : ℂ}
    (h : v = u ^ 3 + v ^ 3) (hv : v = 0) : u = 0 := by
  rw [hv] at h
  have hu : u ^ 3 = 0 := by simpa using h.symm
  by_contra hne
  exact (pow_ne_zero 3 hne) hu

private theorem yChart_point_eq_infinity_of_second_zero (P : ComplexPoint E)
    (hP : P ∈ AlgebraicGeometry.Point.overOpen yChart)
    (u v : ℂ) (h : v = u ^ 3 + v ^ 3)
    (hfac : P.left = Spec.map (CommRingCat.ofHom (AdjoinRoot.lift
      (Polynomial.evalRingHom u) v (by
        rw [Polynomial.eval₂_evalRingHom]
        rw [yAffinePolynomial]
        rw [Polynomial.evalEval_sub, Polynomial.evalEval_sub,
          Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_pow,
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
        rw [show W.a₁ = 0 by simp [W, HodgeLean.Foundations.Program.cp_W], map_zero]
      have ha2 : (W.map f).toAffine.a₂ = 0 := by
        change f W.a₂ = 0
        rw [show W.a₂ = 0 by simp [W, HodgeLean.Foundations.Program.cp_W], map_zero]
      have ha3 : (W.map f).toAffine.a₃ = 0 := by
        change f W.a₃ = 0
        rw [show W.a₃ = 0 by simp [W, HodgeLean.Foundations.Program.cp_W], map_zero]
      have ha4 : (W.map f).toAffine.a₄ = 0 := by
        change f W.a₄ = 0
        rw [show W.a₄ = 0 by simp [W, HodgeLean.Foundations.Program.cp_W], map_zero]
      have ha6 : (W.map f).toAffine.a₆ = 1 := by
        change f W.a₆ = 1
        rw [show W.a₆ = 1 by simp [W, HodgeLean.Foundations.Program.cp_W], map_one]
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
      b yAffinePolynomial = b - a ^ 3 - b ^ 3 := by
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
  simpa [W, HodgeLean.Foundations.Program.cp_W] using h

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

theorem exists_isCubicPointEquiv_aux :
    ∃ e : ComplexPoint E ≃ W.toAffine.Point, (fun e : ComplexPoint E ≃ W.toAffine.Point =>
  (∀ P : ComplexPoint E, P.left = infinity → e P = 0) ∧
    ∀ (x y : ℂ) (h : W.toAffine.Nonsingular x y) (P : ComplexPoint E),
      P.left = Spec.map (CommRingCat.ofHom (affineEval x y h.1)) ≫ zChartMap → e P = .some x y h) e := by
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

noncomputable section

private abbrev AddA := W.toAffine.CoordinateRing
private def addXCoord : AddA := AdjoinRoot.of W.toAffine.polynomial Polynomial.X
private def addYCoord : AddA := AdjoinRoot.root W.toAffine.polynomial

private theorem addA_relation : addYCoord ^ 2 - addXCoord ^ 3 - 1 = 0 := by
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
  simp [W, HodgeLean.Foundations.Program.cp_W] at hxy
  linear_combination hxy

end

noncomputable section

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

private structure CubicChart where
  A : Type
  [cr : CommRing A]
  [alg : Algebra ℂ A]
  [dom : IsDomain A]
  map : Spec ↧A ⟶ E.left
  [isOpen : IsOpenImmersion map]
  «over» : map ≫ E.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
  coords : Fin 3 → A
  isCubic : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) coords
  j : Fin 3
  out : ∀ {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L), (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s →
    ∀ u : L, s j * u = 1 → (A →+* L)
  out_coords : ∀ {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s)
    (u : L) (hu : s j * u = 1) (k : Fin 3), out s hs u hu (coords k) = s k * u
  out_algebraMap : ∀ {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L)
    (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (u : L) (hu : s j * u = 1),
    (out s hs u hu).comp (algebraMap ℂ A) = algebraMap ℂ L
  point : ∀ ψ : A →+* ℂ, ψ.comp (algebraMap ℂ A) = RingHom.id ℂ →
    ∃ t : ℂ, t ≠ 0 ∧ ∃ P : W.toAffine.Point,
      Spec.map (CommRingCat.ofHom ψ) ≫ map = (complexPointOfAffine P).left ∧
        ∀ k, ψ (coords k) = t * cubicHomCoords P k

attribute [instance] CubicChart.cr CubicChart.alg CubicChart.dom CubicChart.isOpen

private instance : IsOpenImmersion zChartMap := by
  dsimp [zChartMap]
  infer_instance

private theorem addA_isCubicTriple : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (![addXCoord, addYCoord, 1] : Fin 3 → AddA) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination addA_relation

private theorem zOut_eval {L : Type} [CommRing L] [Algebra ℂ L] (a b : L) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap ℂ L) a) b W.toAffine.polynomial =
      b ^ 2 - a ^ 3 - 1 := by
  simp [WeierstrassCurve.Affine.polynomial, W, HodgeLean.Foundations.Program.cp_W,
    Polynomial.eval₂_eval₂RingHom_apply, Polynomial.evalEval_C]
  ring

private def zOut {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (u : L)
    (hu : s 2 * u = 1) : AddA →+* L :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℂ L) (s 0 * u)) (s 1 * u) (by
    rw [zOut_eval]
    linear_combination u ^ 3 * hs + ((s 2 * u) ^ 2 + s 2 * u + 1 - s 1 ^ 2 * u ^ 2) * hu)

private theorem zOut_coords {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s)
    (u : L) (hu : s 2 * u = 1) (k : Fin 3) :
    zOut s hs u hu ((![addXCoord, addYCoord, 1] : Fin 3 → AddA) k) = s k * u := by
  fin_cases k
  · simp [zOut, addXCoord]
  · simp [zOut, addYCoord]
  · simpa using hu.symm

private theorem zOut_algebraMap {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L)
    (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (u : L) (hu : s 2 * u = 1) :
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
    simp only [map_sub, map_pow, map_zero, map_one] at h
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
  «over» := zChartMap_over
  coords := ![addXCoord, addYCoord, 1]
  isCubic := addA_isCubicTriple
  j := 2
  out s hs u hu := zOut s hs u hu
  out_coords := zOut_coords
  out_algebraMap := zOut_algebraMap
  point := zChart_point

private abbrev yU : YCoordinateRing := AdjoinRoot.of yAffinePolynomial Polynomial.X
private abbrev yV : YCoordinateRing := AdjoinRoot.root yAffinePolynomial

private theorem yCoords_isCubicTriple : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (![yU, 1, yV] : Fin 3 → YCoordinateRing) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination yChart_equation

private def yOut {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (w : L)
    (hw : s 1 * w = 1) : YCoordinateRing →+* L :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap ℂ L) (s 0 * w)) (s 2 * w) (by
    simp [yAffinePolynomial, Polynomial.eval₂_eval₂RingHom_apply, Polynomial.evalEval_C]
    linear_combination w ^ 3 * hs - s 2 * w * (1 + s 1 * w) * hw)

private theorem yOut_coords {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L) (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s)
    (w : L) (hw : s 1 * w = 1) (k : Fin 3) :
    yOut s hs w hw ((![yU, 1, yV] : Fin 3 → YCoordinateRing) k) = s k * w := by
  fin_cases k
  · simp [yOut, yU]
  · simpa using hw.symm
  · simp [yOut, yV]

private theorem yOut_algebraMap {L : Type} [CommRing L] [Algebra ℂ L] (s : Fin 3 → L)
    (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s) (w : L) (hw : s 1 * w = 1) :
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
  have huv : v = u ^ 3 + v ^ 3 := by
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
  «over» := yChartMap_over
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
    (hp : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) p) (hq : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) q) : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (cubicLaw ℓ p q) := by
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

private theorem pairLeft_isCubicTriple (b : Bool × Bool) : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (pairLeft b) := by
  have h := congrArg (Algebra.TensorProduct.includeLeftRingHom (R := ℂ)
    (A := (cubicChart b.1).A) (B := (cubicChart b.2).A)) (cubicChart b.1).isCubic
  dsimp only [] at h ⊢
  simp only [pairLeft, map_mul, map_pow, map_add] at h ⊢
  exact h

private theorem pairRight_isCubicTriple (b : Bool × Bool) : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (pairRight b) := by
  have h := congrArg (Algebra.TensorProduct.includeRight (R := ℂ)
    (A := (cubicChart b.1).A) (B := (cubicChart b.2).A)) (cubicChart b.2).isCubic
  dsimp only [] at h ⊢
  simp only [pairRight, map_mul, map_pow, map_add] at h ⊢
  exact h

private abbrev PieceIndex : Type := (Bool × Bool) × Bool × Bool

private def pieceTriple (i : PieceIndex) : Fin 3 → PairRing i.1 :=
  cubicLaw i.2.1 (pairLeft i.1) (pairRight i.1)

private theorem pieceTriple_isCubicTriple (i : PieceIndex) : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (pieceTriple i) :=
  cubicLaw_isCubicTriple _ (pairLeft_isCubicTriple _) (pairRight_isCubicTriple _)

private abbrev PieceRing (i : PieceIndex) : Type :=
  Localization.Away (pieceTriple i (cubicChart i.2.2).j)

private def pieceValues (i : PieceIndex) : Fin 3 → PieceRing i := fun k ↦
  algebraMap (PairRing i.1) (PieceRing i) (pieceTriple i k)

private theorem pieceValues_isCubicTriple (i : PieceIndex) : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) (pieceValues i) := by
  have h := congrArg (algebraMap (PairRing i.1) (PieceRing i)) (pieceTriple_isCubicTriple i)
  dsimp only [] at h ⊢
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

private def pointOf (p : Spec ↧ℂ ⟶ E.left) : W.toAffine.Point :=
  if h : p ≫ E.hom = 𝟙 _ then cubicPointEquiv.symm (Over.homMk p h) else 0

private theorem pointOf_left (P : W.toAffine.Point) : pointOf (complexPointOfAffine P).left = P := by
  have h : (complexPointOfAffine P).left ≫ E.hom = 𝟙 (Spec ↧ℂ) := Over.w (complexPointOfAffine P)
  simp only [pointOf, h, ↓reduceDIte]
  apply cubicPointEquiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

private def cubicAddPoint (q : Spec ↧ℂ ⟶ (E ⊗ E).left) : Spec ↧ℂ ⟶ E.left :=
  (complexPointOfAffine (pointOf (q ≫ pullback.fst _ _) + pointOf (q ≫ pullback.snd _ _))).left

private theorem cubicHomCoords_ne (P : W.toAffine.Point) :
    cubicHomCoords P 1 ≠ 0 ∨ cubicHomCoords P 2 ≠ 0 := by
  cases P with
  | zero => left; simp [cubicHomCoords]
  | some x y h => right; simp [cubicHomCoords]

private theorem cubicProjPoint_congr {s s' : Fin 3 → ℂ} (h : s = s') (hs : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s)
    (hs' : (fun p => p 1 ^ 2 * p 2 = p 0 ^ 3 + p 2 ^ 3) s') : cubicProjPoint s hs = cubicProjPoint s' hs' := by
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
      have h := cubicHomCoords_isCubicTriple P₃
      change cubicHomCoords P₃ 1 ^ 2 * cubicHomCoords P₃ 2 =
        cubicHomCoords P₃ 0 ^ 3 + cubicHomCoords P₃ 2 ^ 3 at h
      linear_combination (t₃ / (t₁ ^ 2 * t₂ ^ 2 * lam)) ^ 3 * h)]
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
    (he : (fun e : ComplexPoint E ≃ W.toAffine.Point =>
  (∀ P : ComplexPoint E, P.left = infinity → e P = 0) ∧
    ∀ (x y : ℂ) (h : W.toAffine.Nonsingular x y) (P : ComplexPoint E),
      P.left = Spec.map (CommRingCat.ofHom (affineEval x y h.1)) ≫ zChartMap → e P = .some x y h) e) : e = cubicPointEquiv.symm := by
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
    (he : (fun e : ComplexPoint E ≃ W.toAffine.Point =>
  (∀ P : ComplexPoint E, P.left = infinity → e P = 0) ∧
    ∀ (x y : ℂ) (h : W.toAffine.Nonsingular x y) (P : ComplexPoint E),
      P.left = Spec.map (CommRingCat.ofHom (affineEval x y h.1)) ≫ zChartMap → e P = .some x y h) e) :
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

theorem exists_add_morphism_aux (e : ComplexPoint E ≃ W.toAffine.Point)
    (he : (fun e : ComplexPoint E ≃ W.toAffine.Point =>
  (∀ P : ComplexPoint E, P.left = infinity → e P = 0) ∧
    ∀ (x y : ℂ) (h : W.toAffine.Nonsingular x y) (P : ComplexPoint E),
      P.left = Spec.map (CommRingCat.ofHom (affineEval x y h.1)) ≫ zChartMap → e P = .some x y h) e) :
    ∃ m : E ⊗ E ⟶ E, ∀ P Q : ComplexPoint E, lift P Q ≫ m = e.symm (e P + e Q) :=
  exists_add_morphism_main e he

theorem exists_neg_morphism_aux (e : ComplexPoint E ≃ W.toAffine.Point)
    (he : (fun e : ComplexPoint E ≃ W.toAffine.Point =>
  (∀ P : ComplexPoint E, P.left = infinity → e P = 0) ∧
    ∀ (x y : ℂ) (h : W.toAffine.Nonsingular x y) (P : ComplexPoint E),
      P.left = Spec.map (CommRingCat.ofHom (affineEval x y h.1)) ≫ zChartMap → e P = .some x y h) e) :
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
      simp [WeierstrassCurve.Affine.negY, W, HodgeLean.Foundations.Program.cp_W]
    have ht : e.symm (-e (affineComplexPoint x y hxy)) =
        affineComplexPoint x (-y) hn := by
      apply e.injective
      rw [e.apply_symm_apply, heP, hneg, heN]
    rw [ht]
    apply Over.OverMorphism.ext
    exact affineComplexPoint_cubicNeg x y hxy


noncomputable section

private theorem rho_equation {x y : ℂ} (h : W.toAffine.Equation x y) :
    W.toAffine.Equation (HodgeLean.Foundations.Program.cp_zeta * x) y :=
  HodgeLean.Foundations.Program.cp_W_equation_zeta h

private def zRhoCoordinates : W.toAffine.CoordinateRing →+* W.toAffine.CoordinateRing :=
  zOut ![algebraMap ℂ AddA HodgeLean.Foundations.Program.cp_zeta * addXCoord, addYCoord, 1] (by
    have hz : (algebraMap ℂ AddA HodgeLean.Foundations.Program.cp_zeta) ^ 3 = 1 := by
      rw [← map_pow, HodgeLean.Foundations.Program.cp_zeta_cube, map_one]
    simpa [mul_pow, hz] using addA_isCubicTriple) 1 (by simp)

private def yRhoCoordinates : YCoordinateRing →+* YCoordinateRing :=
  yOut ![algebraMap ℂ YCoordinateRing HodgeLean.Foundations.Program.cp_zeta * yU, 1, yV] (by
    have hz : (algebraMap ℂ YCoordinateRing HodgeLean.Foundations.Program.cp_zeta) ^ 3 = 1 := by
      rw [← map_pow, HodgeLean.Foundations.Program.cp_zeta_cube, map_one]
    simpa [mul_pow, hz] using yCoords_isCubicTriple) 1 (by simp)

private theorem zRhoCoordinates_X :
    zRhoCoordinates (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) =
      algebraMap ℂ AddA HodgeLean.Foundations.Program.cp_zeta * AdjoinRoot.of W.toAffine.polynomial Polynomial.X := by
  simp [zRhoCoordinates, zOut, addXCoord]
private theorem zRhoCoordinates_Y :
    zRhoCoordinates (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root W.toAffine.polynomial := by
  simp [zRhoCoordinates, zOut, addYCoord]
private theorem yRhoCoordinates_U :
    yRhoCoordinates (AdjoinRoot.of yAffinePolynomial Polynomial.X) =
      algebraMap ℂ YCoordinateRing HodgeLean.Foundations.Program.cp_zeta * AdjoinRoot.of yAffinePolynomial Polynomial.X := by
  simp [yRhoCoordinates, yOut]
private theorem yRhoCoordinates_V :
    yRhoCoordinates (AdjoinRoot.root yAffinePolynomial) = AdjoinRoot.root yAffinePolynomial := by
  simp [yRhoCoordinates, yOut]
private theorem zRhoCoordinates_over :
    zRhoCoordinates.comp (algebraMap ℂ W.toAffine.CoordinateRing) =
      algebraMap ℂ W.toAffine.CoordinateRing := by
  exact zOut_algebraMap _ _ _ _
private theorem yRhoCoordinates_over :
    yRhoCoordinates.comp (algebraMap ℂ YCoordinateRing) = algebraMap ℂ YCoordinateRing := by
  exact yOut_algebraMap _ _ _ _

private noncomputable def zChartRho : zChart.toScheme ⟶ E.left :=
  zChartIso.hom ≫ Spec.map (CommRingCat.ofHom zRhoCoordinates) ≫ zChartMap

private noncomputable def yChartRho : yChart.toScheme ⟶ E.left :=
  yChartIso.hom ≫ Spec.map (CommRingCat.ofHom yRhoCoordinates) ≫ yChartMap

private theorem zChartRho_over : zChartRho ≫ E.hom = zChart.ι ≫ E.hom := by
  rw [zChartRho, Category.assoc, Category.assoc, zChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing) ≫
      CommRingCat.ofHom zRhoCoordinates =
        CommRingCat.ofHom (algebraMap ℂ W.toAffine.CoordinateRing) by
    apply CommRingCat.hom_ext
    exact zRhoCoordinates_over]
  rw [← zChartMap_over]
  simp [zChartMap, Category.assoc]

private theorem yChartRho_over : yChartRho ≫ E.hom = yChart.ι ≫ E.hom := by
  rw [yChartRho, Category.assoc, Category.assoc, yChartMap_over, ← Spec.map_comp]
  rw [show CommRingCat.ofHom (algebraMap ℂ YCoordinateRing) ≫
      CommRingCat.ofHom yRhoCoordinates =
        CommRingCat.ofHom (algebraMap ℂ YCoordinateRing) by
    apply CommRingCat.hom_ext
    exact yRhoCoordinates_over]
  rw [← yChartMap_over]
  simp [yChartMap, Category.assoc]


private def yOverlapRho :
    Localization.Away (AdjoinRoot.root yAffinePolynomial) →+*
      Localization.Away (AdjoinRoot.root yAffinePolynomial) :=
  IsLocalization.Away.lift
    (S := Localization.Away (AdjoinRoot.root yAffinePolynomial))
    (P := Localization.Away (AdjoinRoot.root yAffinePolynomial))
    (AdjoinRoot.root yAffinePolynomial)
    (g := (algebraMap YCoordinateRing
      (Localization.Away (AdjoinRoot.root yAffinePolynomial))).comp yRhoCoordinates) (by
      rw [RingHom.comp_apply, yRhoCoordinates_V]
      exact IsLocalization.Away.algebraMap_isUnit _)
private theorem yOverlapRho_algebraMap (a : YCoordinateRing) :
    yOverlapRho (algebraMap YCoordinateRing
      (Localization.Away (AdjoinRoot.root yAffinePolynomial)) a) =
      algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial)) (yRhoCoordinates a) := by
  simp [yOverlapRho, IsLocalization.Away.lift_eq]
private theorem yOverlapRho_invSelf :
    yOverlapRho (IsLocalization.Away.invSelf (AdjoinRoot.root yAffinePolynomial)) =
      IsLocalization.Away.invSelf (AdjoinRoot.root yAffinePolynomial) := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (AdjoinRoot.root yAffinePolynomial))
    (AdjoinRoot.root yAffinePolynomial)).mul_left_cancel
  have hm : yOverlapRho (algebraMap YCoordinateRing
      (Localization.Away (AdjoinRoot.root yAffinePolynomial))
      (AdjoinRoot.root yAffinePolynomial)) = algebraMap YCoordinateRing _
        (AdjoinRoot.root yAffinePolynomial) := by
    rw [yOverlapRho_algebraMap, yRhoCoordinates_V]
  rw [← hm, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, hm,
    IsLocalization.Away.mul_invSelf]
private theorem yOverlapRho_scalar (c : ℂ) :
    yOverlapRho (algebraMap ℂ _ c) = algebraMap ℂ _ c := by
  change yOverlapRho (algebraMap YCoordinateRing _ (algebraMap ℂ YCoordinateRing c)) = _
  rw [yOverlapRho_algebraMap]
  have h := DFunLike.congr_fun yRhoCoordinates_over c
  exact (congrArg (algebraMap YCoordinateRing
    (Localization.Away (AdjoinRoot.root yAffinePolynomial))) h).trans
      (DFunLike.congr_fun (IsScalarTower.algebraMap_eq ℂ YCoordinateRing _) c)
private theorem yToZCoordinates_scalar (c : ℂ) :
    yToZCoordinates (algebraMap ℂ W.toAffine.CoordinateRing c) = algebraMap ℂ _ c :=
  DFunLike.congr_fun yToZCoordinates_over c
private theorem yOverlapRho_transition :
    yOverlapRho.comp yToZCoordinates = yToZCoordinates.comp zRhoCoordinates := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      change yOverlapRho (yToZCoordinates (algebraMap ℂ _ c)) =
        yToZCoordinates (zRhoCoordinates (algebraMap ℂ _ c))
      rw [yToZCoordinates_scalar, yOverlapRho_scalar]
      have h := DFunLike.congr_fun zRhoCoordinates_over c
      rw [show zRhoCoordinates (algebraMap ℂ _ c) = algebraMap ℂ _ c from h,
        yToZCoordinates_scalar]
    · simp [zRhoCoordinates_X, yToZCoordinates_x, map_mul,
        yOverlapRho_algebraMap, yOverlapRho_invSelf, yRhoCoordinates_U,
        yToZCoordinates_scalar, ← IsScalarTower.algebraMap_apply ℂ YCoordinateRing, mul_assoc]
  · simp [zRhoCoordinates_Y, yToZCoordinates_y, yOverlapRho_invSelf]

private theorem chartRho_agree_on_yOverlap :
    Spec.map (CommRingCat.ofHom yToZCoordinates) ≫ zChartIso.inv ≫ zChartRho =
      Spec.map (CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial)))) ≫
          yChartIso.inv ≫ yChartRho := by
  rw [zChartRho, yChartRho]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [show CommRingCat.ofHom zRhoCoordinates ≫ CommRingCat.ofHom yToZCoordinates =
      CommRingCat.ofHom yToZCoordinates ≫ CommRingCat.ofHom yOverlapRho by
    apply CommRingCat.hom_ext
    exact yOverlapRho_transition.symm]
  rw [show CommRingCat.ofHom yRhoCoordinates ≫
      CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial))) =
      CommRingCat.ofHom (algebraMap YCoordinateRing
        (Localization.Away (AdjoinRoot.root yAffinePolynomial))) ≫
          CommRingCat.ofHom yOverlapRho by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (yOverlapRho_algebraMap a).symm]
  rw [Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [transition_agreement_y]

private theorem chartRho_agree :
    E.left.homOfLE inf_le_left ≫ zChartRho =
      E.left.homOfLE inf_le_right ≫ yChartRho := by
  rw [← cancel_epi yOverlapIso.hom]
  rw [← Category.assoc, yOverlapIso_hom_to_zChart,
    ← Category.assoc, yOverlapIso_hom_to_yChart]
  exact chartRho_agree_on_yOverlap

private theorem chartRho_pullback :
    pullback.fst zChart.ι yChart.ι ≫ zChartRho =
      pullback.snd zChart.ι yChart.ι ≫ yChartRho := by
  rw [← cancel_epi (isPullback_opens_inf zChart yChart).isoPullback.hom]
  simpa [Category.assoc] using chartRho_agree

private theorem chartRho_pullback_symm :
    pullback.fst yChart.ι zChart.ι ≫ yChartRho =
      pullback.snd yChart.ι zChart.ι ≫ zChartRho := by
  rw [← cancel_epi (pullbackSymmetry zChart.ι yChart.ι).hom]
  simpa [Category.assoc] using chartRho_pullback.symm

private noncomputable abbrev rhoCoverOpen : Bool → E.left.Opens
  | false => zChart
  | true => yChart

private theorem rhoCoverOpen_isCover : TopologicalSpace.IsOpenCover rhoCoverOpen := by
  change (⨆ b, rhoCoverOpen b) = ⊤
  rw [iSup_bool_eq]
  change yChart ⊔ zChart = ⊤
  rw [sup_comm, charts_cover]

private noncomputable abbrev rhoCover : E.left.OpenCover :=
  E.left.openCoverOfIsOpenCover rhoCoverOpen rhoCoverOpen_isCover

private noncomputable abbrev rhoLocal : (b : Bool) → rhoCover.X b ⟶ E.left
  | false => zChartRho
  | true => yChartRho

private theorem rhoLocal_compatible_ff :
    pullback.fst (rhoCover.f false) (rhoCover.f false) ≫ rhoLocal false =
      pullback.snd (rhoCover.f false) (rhoCover.f false) ≫ rhoLocal false := by
  have h : pullback.fst zChart.ι zChart.ι = pullback.snd zChart.ι zChart.ι :=
    (cancel_mono zChart.ι).mp pullback.condition
  exact congrArg (fun f ↦ f ≫ zChartRho) h

private theorem rhoLocal_compatible_ft :
    pullback.fst (rhoCover.f false) (rhoCover.f true) ≫ rhoLocal false =
      pullback.snd (rhoCover.f false) (rhoCover.f true) ≫ rhoLocal true := by
  exact chartRho_pullback

private theorem rhoLocal_compatible_tf :
    pullback.fst (rhoCover.f true) (rhoCover.f false) ≫ rhoLocal true =
      pullback.snd (rhoCover.f true) (rhoCover.f false) ≫ rhoLocal false := by
  exact chartRho_pullback_symm

private theorem rhoLocal_compatible_tt :
    pullback.fst (rhoCover.f true) (rhoCover.f true) ≫ rhoLocal true =
      pullback.snd (rhoCover.f true) (rhoCover.f true) ≫ rhoLocal true := by
  have h : pullback.fst yChart.ι yChart.ι = pullback.snd yChart.ι yChart.ι :=
    (cancel_mono yChart.ι).mp pullback.condition
  exact congrArg (fun f ↦ f ≫ yChartRho) h

private theorem rhoLocal_compatible (b c : Bool) :
    pullback.fst (rhoCover.f b) (rhoCover.f c) ≫ rhoLocal b =
      pullback.snd (rhoCover.f b) (rhoCover.f c) ≫ rhoLocal c := by
  exact Bool.rec (Bool.rec rhoLocal_compatible_ff rhoLocal_compatible_ft c)
    (Bool.rec rhoLocal_compatible_tf rhoLocal_compatible_tt c) b

private noncomputable def cubicRho : E.left ⟶ E.left :=
  rhoCover.glueMorphisms rhoLocal rhoLocal_compatible

private theorem zChart_cubicRho : zChart.ι ≫ cubicRho = zChartRho := by
  exact rhoCover.ι_glueMorphisms rhoLocal rhoLocal_compatible false

private theorem yChart_cubicRho : yChart.ι ≫ cubicRho = yChartRho := by
  exact rhoCover.ι_glueMorphisms rhoLocal rhoLocal_compatible true

private theorem cubicRho_over : cubicRho ≫ E.hom = E.hom := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hx : x ∈ zChart ∨ x ∈ yChart := by
    have h : x ∈ zChart ⊔ yChart := by rw [charts_cover]; trivial
    exact h
  rcases hx with hx | hx
  · refine ⟨zChart, hx, ?_⟩
    rw [← Category.assoc, zChart_cubicRho, zChartRho_over]
  · refine ⟨yChart, hx, ?_⟩
    rw [← Category.assoc, yChart_cubicRho, yChartRho_over]

private noncomputable def cubicRhoOver : E ⟶ E :=
  Over.homMk cubicRho cubicRho_over

private theorem yChartMap_cubicRho :
    yChartMap ≫ cubicRho =
      Spec.map (CommRingCat.ofHom yRhoCoordinates) ≫ yChartMap := by
  calc
    yChartMap ≫ cubicRho = yChartIso.inv ≫ (yChart.ι ≫ cubicRho) := by rfl
    _ = yChartIso.inv ≫ yChartRho := by rw [yChart_cubicRho]
    _ = Spec.map (CommRingCat.ofHom yRhoCoordinates) ≫ yChartMap := by
      simp [yChartRho, Category.assoc]

private theorem zChartMap_cubicRho :
    zChartMap ≫ cubicRho =
      Spec.map (CommRingCat.ofHom zRhoCoordinates) ≫ zChartMap := by
  calc
    zChartMap ≫ cubicRho = zChartIso.inv ≫ (zChart.ι ≫ cubicRho) := by rfl
    _ = zChartIso.inv ≫ zChartRho := by rw [zChart_cubicRho]
    _ = Spec.map (CommRingCat.ofHom zRhoCoordinates) ≫ zChartMap := by
      simp [zChartRho, Category.assoc]

private theorem affineEval_comp_zRhoCoordinates (x y : ℂ)
    (h : W.toAffine.Equation x y) :
    (affineEval x y h).comp zRhoCoordinates =
      affineEval (HodgeLean.Foundations.Program.cp_zeta * x) y (rho_equation h) := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro c
      simp [affineEval, zRhoCoordinates, zOut, AdjoinRoot.algebraMap_eq']
    · simp [affineEval, zRhoCoordinates_X, AdjoinRoot.algebraMap_eq']
  · simp [affineEval, zRhoCoordinates_Y]

private theorem affineComplexPoint_cubicRho (x y : ℂ)
    (h : W.toAffine.Equation x y) :
    (affineComplexPoint x y h).left ≫ cubicRho =
      (affineComplexPoint (HodgeLean.Foundations.Program.cp_zeta * x) y (rho_equation h)).left := by
  rw [affineComplexPoint_left, affineComplexPoint_left, Category.assoc,
    zChartMap_cubicRho, ← Category.assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom zRhoCoordinates ≫ CommRingCat.ofHom (affineEval x y h) =
      CommRingCat.ofHom (affineEval (HodgeLean.Foundations.Program.cp_zeta * x) y (rho_equation h)) by
    apply CommRingCat.hom_ext
    exact affineEval_comp_zRhoCoordinates x y h]

private theorem cubicRho_infinity : infinity ≫ cubicRho = infinity := by
  rw [← infinity_chart, Category.assoc]
  rw [yChartMap_cubicRho]
  simp only [← Category.assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom yRhoCoordinates ≫
      CommRingCat.ofHom infinityCoordinates =
      CommRingCat.ofHom infinityCoordinates by
    apply CommRingCat.hom_ext
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        simp [yRhoCoordinates, yOut, infinityCoordinates, AdjoinRoot.algebraMap_eq']
      · change infinityCoordinates (yRhoCoordinates
          (AdjoinRoot.of yAffinePolynomial Polynomial.X)) = _
        rw [yRhoCoordinates_U, map_mul, infinityCoordinates_values.1, mul_zero]
        exact infinityCoordinates_values.1.symm
    · change infinityCoordinates (yRhoCoordinates
        (AdjoinRoot.root yAffinePolynomial)) = _
      rw [yRhoCoordinates_V, infinityCoordinates_values.2]
      exact infinityCoordinates_values.2.symm]


theorem exists_rho_morphism_aux (e : ComplexPoint E ≃ W.toAffine.Point)
    (he : (∀ P : ComplexPoint E, P.left = infinity → e P = 0) ∧
      ∀ (x y : ℂ) (h : W.toAffine.Nonsingular x y) (P : ComplexPoint E),
        P.left = Spec.map (CommRingCat.ofHom (affineEval x y h.1)) ≫ zChartMap →
          e P = .some x y h) :
    ∃ ρ : E ⟶ E, ∀ P : ComplexPoint E,
      e (P ≫ ρ) = HodgeLean.Foundations.Program.cp_cubicAut (e P) := by
  refine ⟨cubicRhoOver, ?_⟩
  intro P
  by_cases hP : P = Over.homMk infinity infinity_over
  · subst P
    have hfix : (Over.homMk infinity infinity_over : ComplexPoint E) ≫ cubicRhoOver =
        Over.homMk infinity infinity_over := by
      apply Over.OverMorphism.ext
      exact cubicRho_infinity
    rw [hfix, he.1 _ rfl]
    rfl
  · obtain ⟨x, y, hxy, rfl⟩ :=
      zChart_point_eq_affineComplexPoint P (mem_zChart_of_ne_infinity P hP)
    have hleft : ((affineComplexPoint x y hxy) ≫ cubicRhoOver).left =
        (affineComplexPoint (HodgeLean.Foundations.Program.cp_zeta * x) y (rho_equation hxy)).left :=
      affineComplexPoint_cubicRho x y hxy
    rw [he.2 x y (W_equation_iff_nonsingular.mp hxy) _ (affineComplexPoint_left x y hxy)]
    exact he.2 _ _ _ _ (hleft.trans (affineComplexPoint_left _ _ _))

end

end HodgeLean.Foundations.Program.CompensationCubic
