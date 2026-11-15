import HodgeLean.Foundations.ComplexPointGroup
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The group law in algebraic charts

Stage S10. HC no distance; AV milestone no distance. This retires nothing.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Filter Topology

namespace HodgeLean.Foundations

noncomputable section

/-- Products of smooth complex schemes have the sum of the relative dimensions.

Source: Mathlib `AlgebraicGeometry/Morphisms/Smooth.lean`, base change and
`smoothOfRelativeDimension_comp`; upstream `ComplexPoint/Manifold.lean`. -/
instance complexProduct_smoothOfRelativeDimension (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom] :
    SmoothOfRelativeDimension (d + e) (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom, CategoryTheory.Limits.pullback.condition]
  infer_instance

example (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom] :
    SmoothOfRelativeDimension (d + e) (X ⊗ Y).hom := inferInstance

/-- Coordinate comparison from an upstream product-scheme chart to the product of
the two upstream charts. Its source and target record the required neighborhood restrictions.

Source: upstream `ComplexPoint/Manifold.lean`, `localChart`, and
`ComplexPoint/AnalyticMap.lean`, applied to the two projections. -/
def productChartComparison (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) :
    OpenPartialHomeomorph (Fin (d + e) → ℂ) ((Fin d → ℂ) × (Fin e → ℂ)) :=
  (localChart (X ⊗ Y) (d + e) z).symm.trans
    ((complexPointProdHomeomorph X Y).toOpenPartialHomeomorph.trans
      ((localChart X d (Point.map (fst X Y) z)).prod
        (localChart Y e (Point.map (snd X Y) z))))

example (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) (w : Fin (d + e) → ℂ) :
    productChartComparison X Y d e z w =
      (localChart X d (Point.map (fst X Y) z)
        (Point.map (fst X Y) ((localChart (X ⊗ Y) (d + e) z).symm w)),
       localChart Y e (Point.map (snd X Y) z)
        (Point.map (snd X Y) ((localChart (X ⊗ Y) (d + e) z).symm w))) := rfl

/-- The forward product-chart comparison is analytic throughout its source.

Source: upstream `ComplexPoint/AnalyticMap.lean`,
`analyticAt_localChart_symm_map`, applied to the projections. -/
theorem analyticAt_productChartComparison (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) {w : Fin (d + e) → ℂ}
    (hw : w ∈ (productChartComparison X Y d e z).source) :
    AnalyticAt ℂ (productChartComparison X Y d e z) w := by
  exact (analyticAt_localChart_symm_map (X ⊗ Y) X (fst X Y) (d + e) d z
    hw.1 hw.2.2.1).prod
    (analyticAt_localChart_symm_map (X ⊗ Y) Y (snd X Y) (d + e) e z
      hw.1 hw.2.2.2)

example (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) {w : Fin (d + e) → ℂ}
    (hw : w ∈ (productChartComparison X Y d e z).source) :
    AnalyticAt ℂ (productChartComparison X Y d e z) w :=
  analyticAt_productChartComparison X Y d e z hw

private theorem analyticAt_chart_map_center
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y) (x : ComplexPoint X) (y : ComplexPoint Y) (h : Point.map f x = y) :
    AnalyticAt ℂ (fun u ↦ localChart Y e y (Point.map f ((localChart X d x).symm u)))
      (localChart X d x x) := by
  subst y
  apply analyticAt_localChart_symm_map
  · exact (localChart X d x).map_source (mem_localChart_source X d x)
  · rw [(localChart X d x).left_inv (mem_localChart_source X d x)]
    exact mem_localChart_source Y e _

@[simp] private theorem pointDomain_toUnit :
    toUnit (Over.mk (𝟙 (Spec ↧ℂ))) = 𝟙 (Over.mk (𝟙 (Spec ↧ℂ))) :=
  Subsingleton.elim _ _

private def leftSlice (X Y : Over (Spec ↧ℂ)) (y : ComplexPoint Y) : X ⟶ X ⊗ Y :=
  lift (𝟙 X) (toUnit X ≫ y)

private def rightSlice (X Y : Over (Spec ↧ℂ)) (x : ComplexPoint X) : Y ⟶ X ⊗ Y :=
  lift (toUnit Y ≫ x) (𝟙 Y)

private theorem map_leftSlice (X Y : Over (Spec ↧ℂ))
    (x : ComplexPoint X) (y : ComplexPoint Y) :
    Point.map (leftSlice X Y y) x = lift x y := by
  simp [leftSlice, Point.map]

private theorem map_rightSlice (X Y : Over (Spec ↧ℂ))
    (x : ComplexPoint X) (y : ComplexPoint Y) :
    Point.map (rightSlice X Y x) y = lift x y := by
  simp [rightSlice, Point.map]

private theorem surjective_derivative_of_slices
    {d e : ℕ} {H : (Fin (d + e) → ℂ) → (Fin d → ℂ) × (Fin e → ℂ)}
    {A : (Fin d → ℂ) → (Fin (d + e) → ℂ)}
    {B : (Fin e → ℂ) → (Fin (d + e) → ℂ)}
    {a : Fin (d + e) → ℂ} {u : Fin d → ℂ} {v : Fin e → ℂ}
    (hH : DifferentiableAt ℂ H a) (hA : DifferentiableAt ℂ A u)
    (hB : DifferentiableAt ℂ B v) (hAu : A u = a) (hBv : B v = a)
    (hHA : (fun t ↦ H (A t)) =ᶠ[𝓝 u] (fun t ↦ (t, v)))
    (hHB : (fun t ↦ H (B t)) =ᶠ[𝓝 v] (fun t ↦ (u, t))) :
    Function.Surjective (fderiv ℂ H a) := by
  have hHA' := (hasFDerivAt_prodMk_left (𝕜 := ℂ) u v).congr_of_eventuallyEq hHA
  have hHB' := (hasFDerivAt_prodMk_right (𝕜 := ℂ) u v).congr_of_eventuallyEq hHB
  have haA : HasFDerivAt H (fderiv ℂ H a) (A u) := by
    rw [hAu]; exact hH.hasFDerivAt
  have haB : HasFDerivAt H (fderiv ℂ H a) (B v) := by
    rw [hBv]; exact hH.hasFDerivAt
  have hcompA := haA.comp u hA.hasFDerivAt
  have hcompB := haB.comp v hB.hasFDerivAt
  have heA := hcompA.unique hHA'
  have heB := hcompB.unique hHB'
  intro q
  refine ⟨fderiv ℂ A u q.1 + fderiv ℂ B v q.2, ?_⟩
  rw [map_add]
  have heAq := DFunLike.congr_fun heA q.1
  have heBq := DFunLike.congr_fun heB q.2
  change fderiv ℂ H a (fderiv ℂ A u q.1) = (q.1, 0) at heAq
  change fderiv ℂ H a (fderiv ℂ B v q.2) = (0, q.2) at heBq
  rw [heAq, heBq]
  simp

private theorem productChartComparison_center_mem (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) :
    localChart (X ⊗ Y) (d + e) z z ∈ (productChartComparison X Y d e z).source := by
  have hz := mem_localChart_source (X ⊗ Y) (d + e) z
  refine ⟨(localChart (X ⊗ Y) (d + e) z).map_source hz, trivial, ?_, ?_⟩
  · change Point.map (fst X Y)
      ((localChart (X ⊗ Y) (d + e) z).symm (localChart (X ⊗ Y) (d + e) z z)) ∈ _
    rw [(localChart (X ⊗ Y) (d + e) z).left_inv hz]
    exact mem_localChart_source X d _
  · change Point.map (snd X Y)
      ((localChart (X ⊗ Y) (d + e) z).symm (localChart (X ⊗ Y) (d + e) z z)) ∈ _
    rw [(localChart (X ⊗ Y) (d + e) z).left_inv hz]
    exact mem_localChart_source Y e _

private theorem productChartComparison_derivative_surjective
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) :
    Function.Surjective (fderiv ℂ (productChartComparison X Y d e z)
      (localChart (X ⊗ Y) (d + e) z z)) := by
  let x := Point.map (fst X Y) z
  let y := Point.map (snd X Y) z
  let a := localChart (X ⊗ Y) (d + e) z
  let b := localChart X d x
  let c := localChart Y e y
  have hx := mem_localChart_source X d x
  have hy := mem_localChart_source Y e y
  have hz := mem_localChart_source (X ⊗ Y) (d + e) z
  have hpair : lift x y = z := by simp [x, y, Point.map]
  have hL : Point.map (leftSlice X Y y) x = z := (map_leftSlice X Y x y).trans hpair
  have hR : Point.map (rightSlice X Y x) y = z := (map_rightSlice X Y x y).trans hpair
  let A := fun u ↦ a (Point.map (leftSlice X Y y) (b.symm u))
  let B := fun v ↦ a (Point.map (rightSlice X Y x) (c.symm v))
  have hA := analyticAt_chart_map_center X (X ⊗ Y) d (d + e) (leftSlice X Y y) x z hL
  have hB := analyticAt_chart_map_center Y (X ⊗ Y) e (d + e) (rightSlice X Y x) y z hR
  have hAu : A (b x) = a z := by dsimp [A]; rw [b.left_inv hx, hL]
  have hBv : B (c y) = a z := by dsimp [B]; rw [c.left_inv hy, hR]
  apply surjective_derivative_of_slices
    (analyticAt_productChartComparison X Y d e z
      (productChartComparison_center_mem X Y d e z)).differentiableAt
    hA.differentiableAt hB.differentiableAt hAu hBv
  · have hc : ContinuousAt (fun u ↦ Point.map (leftSlice X Y y) (b.symm u)) (b x) :=
      (Point.continuous_map _).continuousAt.comp (b.continuousAt_symm (b.map_source hx))
    have hn : ∀ᶠ u in 𝓝 (b x), Point.map (leftSlice X Y y) (b.symm u) ∈ a.source :=
      hc (a.open_source.mem_nhds (by dsimp only; rw [b.left_inv hx, hL]; exact hz))
    filter_upwards [hn, b.open_target.mem_nhds (b.map_source hx)] with u hu hut
    change (b (Point.map (fst X Y) (a.symm (A u))),
      c (Point.map (snd X Y) (a.symm (A u)))) = (u, c y)
    dsimp [A]
    rw [a.left_inv hu]
    simp [Point.map, leftSlice, b.right_inv hut]
  · have hc : ContinuousAt (fun v ↦ Point.map (rightSlice X Y x) (c.symm v)) (c y) :=
      (Point.continuous_map _).continuousAt.comp (c.continuousAt_symm (c.map_source hy))
    have hn : ∀ᶠ v in 𝓝 (c y), Point.map (rightSlice X Y x) (c.symm v) ∈ a.source :=
      hc (a.open_source.mem_nhds (by dsimp only; rw [c.left_inv hy, hR]; exact hz))
    filter_upwards [hn, c.open_target.mem_nhds (c.map_source hy)] with v hv hvt
    change (b (Point.map (fst X Y) (a.symm (B v))),
      c (Point.map (snd X Y) (a.symm (B v)))) = (b x, v)
    dsimp [B]
    rw [a.left_inv hv]
    simp [Point.map, rightSlice, c.right_inv hvt]

/-- The inverse product-chart comparison is analytic at the pair of center coordinates.
Together with `analyticAt_productChartComparison`, this gives an analytic change of
coordinates near the selected point, in both directions.

Source: upstream `ComplexPoint/AnalyticMap.lean` for the projections and fixed-point
slices; Mathlib `OpenPartialHomeomorph.analyticAt_symm'` for the analytic inverse. -/
theorem analyticAt_productChartComparison_symm
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) :
    AnalyticAt ℂ (productChartComparison X Y d e z).symm
      (localChart X d (Point.map (fst X Y) z) (Point.map (fst X Y) z),
       localChart Y e (Point.map (snd X Y) z) (Point.map (snd X Y) z)) := by
  let H := productChartComparison X Y d e z
  let a := localChart (X ⊗ Y) (d + e) z z
  let D := fderiv ℂ H a
  have hs : Function.Surjective D := productChartComparison_derivative_surjective X Y d e z
  have hd : Module.finrank ℂ (Fin (d + e) → ℂ) =
      Module.finrank ℂ ((Fin d → ℂ) × (Fin e → ℂ)) := by
    simp [Module.finrank_prod]
  have hi : Function.Injective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs
  let i : (Fin (d + e) → ℂ) ≃L[ℂ] ((Fin d → ℂ) × (Fin e → ℂ)) :=
    (LinearEquiv.ofBijective D.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv
  have hDi : D = i.toContinuousLinearMap := by ext u <;> rfl
  have ha := H.analyticAt_symm' (productChartComparison_center_mem X Y d e z)
    (analyticAt_productChartComparison X Y d e z
      (productChartComparison_center_mem X Y d e z)) hDi
  have he : H a =
      (localChart X d (Point.map (fst X Y) z) (Point.map (fst X Y) z),
       localChart Y e (Point.map (snd X Y) z) (Point.map (snd X Y) z)) := by
    change (localChart X d (Point.map (fst X Y) z)
      (Point.map (fst X Y) ((localChart (X ⊗ Y) (d + e) z).symm
        (localChart (X ⊗ Y) (d + e) z z))),
      localChart Y e (Point.map (snd X Y) z)
      (Point.map (snd X Y) ((localChart (X ⊗ Y) (d + e) z).symm
        (localChart (X ⊗ Y) (d + e) z z)))) = _
    simp only [(localChart (X ⊗ Y) (d + e) z).left_inv
      (mem_localChart_source (X ⊗ Y) (d + e) z)]
  rwa [he] at ha

example (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (z : ComplexPoint (X ⊗ Y)) :
    AnalyticAt ℂ (productChartComparison X Y d e z).symm
      (localChart X d (Point.map (fst X Y) z) (Point.map (fst X Y) z),
       localChart Y e (Point.map (snd X Y) z) (Point.map (snd X Y) z)) :=
  analyticAt_productChartComparison_symm X Y d e z

/-- The upstream chart at the identity, translated so that the identity has coordinate zero.

Source: upstream `ComplexPoint/Manifold.lean`, `localChart`; Mumford,
Abelian Varieties, §1 (local coordinates at the identity). -/
def identityChart (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ) :=
  (localChart X d 1).transHomeomorph (Homeomorph.subRight (localChart X d 1 1))

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (x : ComplexPoint X) :
    identityChart X d x = localChart X d 1 x - localChart X d 1 1 := rfl

/-- The normalized chart sends the identity to zero.

Source: Mumford, Abelian Varieties, §1; the translation in `identityChart`. -/
theorem identityChart_one (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] : identityChart X d 1 = 0 := sub_self _

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] : identityChart X d 1 = 0 :=
  identityChart_one X d

private theorem identityChart_one_mem_source (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] : 1 ∈ (identityChart X d).source :=
  mem_localChart_source X d 1

private theorem identityChart_zero_mem_target (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] : 0 ∈ (identityChart X d).target := by
  rw [← identityChart_one X d]
  exact (identityChart X d).map_source (identityChart_one_mem_source X d)

private theorem identityChart_symm_zero (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] : (identityChart X d).symm 0 = 1 := by
  rw [← identityChart_one X d]
  exact (identityChart X d).left_inv (identityChart_one_mem_source X d)

/-- Multiplication expressed in the normalized algebraic chart at the identity.
The formula is a total function; the group-law identities are asserted on chart neighborhoods.

Source: Mumford, Abelian Varieties, §1; upstream `ComplexPoint/Manifold.lean`. -/
def chartGroupLaw (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (p : (Fin d → ℂ) × (Fin d → ℂ)) : Fin d → ℂ :=
  identityChart X d ((identityChart X d).symm p.1 * (identityChart X d).symm p.2)

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (u v : Fin d → ℂ) :
    chartGroupLaw X d (u, v) =
      identityChart X d ((identityChart X d).symm u * (identityChart X d).symm v) := rfl

/-- Right identity in coordinates, on the target of the normalized chart.

Source: Mumford, Abelian Varieties, §1 (identity law in local coordinates). -/
theorem chartGroupLaw_zero_right (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] {u : Fin d → ℂ}
    (hu : u ∈ (identityChart X d).target) : chartGroupLaw X d (u, 0) = u := by
  simp only [chartGroupLaw, identityChart_symm_zero, mul_one]
  exact (identityChart X d).right_inv hu

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    ∀ᶠ u in 𝓝 0, chartGroupLaw X d (u, 0) = u :=
  Filter.eventually_of_mem ((identityChart X d).open_target.mem_nhds
    (identityChart_zero_mem_target X d)) (fun _ hu ↦ chartGroupLaw_zero_right X d hu)

/-- Left identity in coordinates, on the target of the normalized chart.

Source: Mumford, Abelian Varieties, §1 (identity law in local coordinates). -/
theorem chartGroupLaw_zero_left (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] {v : Fin d → ℂ}
    (hv : v ∈ (identityChart X d).target) : chartGroupLaw X d (0, v) = v := by
  simp only [chartGroupLaw, identityChart_symm_zero, one_mul]
  exact (identityChart X d).right_inv hv

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    ∀ᶠ v in 𝓝 0, chartGroupLaw X d (0, v) = v :=
  Filter.eventually_of_mem ((identityChart X d).open_target.mem_nhds
    (identityChart_zero_mem_target X d)) (fun _ hv ↦ chartGroupLaw_zero_left X d hv)

/-- Commutativity of the coordinate law requires an explicit commutative group-object instance.
It holds for the total coordinate formula, hence in particular near zero.

Source: Mumford, Abelian Varieties, §1 (commutative group law). -/
theorem chartGroupLaw_comm (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (u v : Fin d → ℂ) :
    chartGroupLaw X d (u, v) = chartGroupLaw X d (v, u) := by
  simp only [chartGroupLaw, mul_comm]

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (p : (Fin d → ℂ) × (Fin d → ℂ)) :
    chartGroupLaw X d p = chartGroupLaw X d p.swap := chartGroupLaw_comm X d p.1 p.2

private theorem analyticAt_raw_chartGroupLaw (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    AnalyticAt ℂ (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦
      localChart X d 1 ((localChart X d 1).symm p.1 * (localChart X d 1).symm p.2))
      (localChart X d 1 1, localChart X d 1 1) := by
  let z : ComplexPoint (X ⊗ X) := lift (1 : ComplexPoint X) 1
  let a := localChart (X ⊗ X) (d + d) z
  let c := localChart X d 1
  let H := productChartComparison X X d d z
  have hfst : Point.map (fst X X) z = 1 := by simp [z, Point.map]
  have hsnd : Point.map (snd X X) z = 1 := by simp [z, Point.map]
  have he : H (a z) = (c 1, c 1) := by
    change (localChart X d (Point.map (fst X X) z)
      (Point.map (fst X X) (a.symm (a z))),
      localChart X d (Point.map (snd X X) z)
      (Point.map (snd X X) (a.symm (a z)))) = _
    rw [a.left_inv (mem_localChart_source (X ⊗ X) (d + d) z), hfst, hsnd]
  have hz := productChartComparison_center_mem X X d d z
  have ht : (c 1, c 1) ∈ H.target := he ▸ H.map_source hz
  have hv : H.symm (c 1, c 1) = a z := by rw [← he]; exact H.left_inv hz
  have hH : AnalyticAt ℂ H.symm (c 1, c 1) := by
    simpa only [hfst, hsnd] using analyticAt_productChartComparison_symm X X d d z
  have hm : Point.map (MonObj.mul : X ⊗ X ⟶ X) z = (1 : ComplexPoint X) := by
    change (1 : ComplexPoint X) * 1 = 1
    exact one_mul _
  have hM := analyticAt_chart_map_center (X ⊗ X) X (d + d) d
    (MonObj.mul : X ⊗ X ⟶ X) z 1 hm
  apply (hM.comp_of_eq hH hv).congr
  filter_upwards [H.open_target.mem_nhds ht] with p hp
  have hp' : lift (c.symm p.1) (c.symm p.2) ∈ a.source := by
    have hp2 := hp.2
    change lift ((localChart X d (Point.map (fst X X) z)).symm p.1)
      ((localChart X d (Point.map (snd X X) z)).symm p.2) ∈ a.source at hp2
    simpa only [hfst, hsnd] using hp2
  change c (Point.map (MonObj.mul : X ⊗ X ⟶ X)
    (a.symm (H.symm p))) = _
  have hval : H.symm p = a (lift (c.symm p.1) (c.symm p.2)) := by
    change a (lift ((localChart X d (Point.map (fst X X) z)).symm p.1)
      ((localChart X d (Point.map (snd X X) z)).symm p.2)) = _
    rw [hfst, hsnd]
  rw [hval, a.left_inv hp']
  rfl

/-- The normalized coordinate group law is complex analytic at the origin.
No commutativity or projectivity assumption is used.

Source: upstream `ComplexPoint/AnalyticMap.lean`, applied to multiplication,
and the analytic product-chart comparison above; Mumford, Abelian Varieties, §1. -/
theorem analyticAt_chartGroupLaw (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    AnalyticAt ℂ (chartGroupLaw X d) (0, 0) := by
  let c := localChart X d 1
  have hshift : AnalyticAt ℂ
      (fun p : (Fin d → ℂ) × (Fin d → ℂ) ↦ (p.1 + c 1, p.2 + c 1)) (0, 0) :=
    (analyticAt_fst.add analyticAt_const).prod (analyticAt_snd.add analyticAt_const)
  have h := (analyticAt_raw_chartGroupLaw X d).comp_of_eq hshift
    (show ((0 : Fin d → ℂ) + c 1, (0 : Fin d → ℂ) + c 1) = (c 1, c 1) by simp)
  exact h.sub analyticAt_const

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    AnalyticAt ℂ (chartGroupLaw X d) (0, 0) := analyticAt_chartGroupLaw X d

/-- The differential of multiplication in normalized coordinates is the sum of the projections.

Source: Mumford, Abelian Varieties, §1; differentiation of the two identity laws. -/
theorem fderiv_chartGroupLaw (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] :
    fderiv ℂ (chartGroupLaw X d) (0, 0) =
      ContinuousLinearMap.fst ℂ (Fin d → ℂ) (Fin d → ℂ) +
      ContinuousLinearMap.snd ℂ (Fin d → ℂ) (Fin d → ℂ) := by
  let F := chartGroupLaw X d
  let D := fderiv ℂ F (0, 0)
  have hF := (analyticAt_chartGroupLaw X d).differentiableAt.hasFDerivAt
  have ht := (identityChart X d).open_target.mem_nhds (identityChart_zero_mem_target X d)
  have hR : (fun u ↦ F (u, 0)) =ᶠ[𝓝 0] (fun u ↦ u) :=
    Filter.eventually_of_mem ht (fun _ hu ↦ chartGroupLaw_zero_right X d hu)
  have hL : (fun v ↦ F (0, v)) =ᶠ[𝓝 0] (fun v ↦ v) :=
    Filter.eventually_of_mem ht (fun _ hv ↦ chartGroupLaw_zero_left X d hv)
  have eR := (hF.comp (f := fun u : Fin d → ℂ ↦ (u, 0))
    (0 : Fin d → ℂ) (hasFDerivAt_prodMk_left (𝕜 := ℂ)
    (0 : Fin d → ℂ) (0 : Fin d → ℂ))).unique
    ((hasFDerivAt_id (𝕜 := ℂ) (0 : Fin d → ℂ)).congr_of_eventuallyEq hR)
  have eL := (hF.comp (f := fun v : Fin d → ℂ ↦ (0, v))
    (0 : Fin d → ℂ) (hasFDerivAt_prodMk_right (𝕜 := ℂ)
    (0 : Fin d → ℂ) (0 : Fin d → ℂ))).unique
    ((hasFDerivAt_id (𝕜 := ℂ) (0 : Fin d → ℂ)).congr_of_eventuallyEq hL)
  apply ContinuousLinearMap.ext
  intro p
  have eRu := DFunLike.congr_fun eR p.1
  have eLv := DFunLike.congr_fun eL p.2
  change D (p.1, 0) = p.1 at eRu
  change D (0, p.2) = p.2 at eLv
  change D p = p.1 + p.2
  calc
    D p = D ((p.1, 0) + (0, p.2)) := by congr 1; simp
    _ = D (p.1, 0) + D (0, p.2) := map_add _ _ _
    _ = p.1 + p.2 := by rw [eRu, eLv]

example (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom] (u v : Fin d → ℂ) :
    fderiv ℂ (chartGroupLaw X d) (0, 0) (u, v) = u + v := by
  rw [fderiv_chartGroupLaw]
  rfl

/-! Falsification on the actual trivial group scheme. Its structure morphism is
smooth of relative dimension zero, and its coordinate space has one element. -/

private abbrev trivialChartGroup : Over (Spec ↧ℂ) := 𝟙_ (Over (Spec ↧ℂ))

private instance trivialChartGroup_smooth : SmoothOfRelativeDimension 0 trivialChartGroup.hom := by
  change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ))
  infer_instance

example : SmoothOfRelativeDimension 0 trivialChartGroup.hom := inferInstance

example : chartGroupLaw trivialChartGroup 0 = 0 := Subsingleton.elim _ _

example (u v : Fin 0 → ℂ) : chartGroupLaw trivialChartGroup 0 (u, v) = 0 :=
  Subsingleton.elim _ _

example : AnalyticAt ℂ (chartGroupLaw trivialChartGroup 0) (0, 0) :=
  analyticAt_chartGroupLaw trivialChartGroup 0

example : fderiv ℂ (chartGroupLaw trivialChartGroup 0) (0, 0) = 0 := by
  rw [fderiv_chartGroupLaw]
  exact Subsingleton.elim _ _

/-! An independent positive-dimensional calculus check in the standard additive
coordinate: the formula is exactly addition and its derivative is the sum of projections.
This is a vector-space model check, not an identification of a bundled additive group
scheme with its complex points. The pinned API supplies affine charts, but no ready-made
additive group scheme with that chart identification was located; see the run report. -/

example (u v : ℂ) :
    (OpenPartialHomeomorph.refl ℂ)
      ((OpenPartialHomeomorph.refl ℂ).symm u + (OpenPartialHomeomorph.refl ℂ).symm v) =
      u + v := rfl

example : fderiv ℂ (fun p : ℂ × ℂ ↦ p.1 + p.2) (0, 0) =
    ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ :=
  (hasFDerivAt_fst.add hasFDerivAt_snd).fderiv

example : fderiv ℂ (fun p : ℂ × ℂ ↦ p.1 + p.2) (0, 0) (1, 2) = 3 := by
  have h : fderiv ℂ (fun p : ℂ × ℂ ↦ p.1 + p.2) (0, 0) =
      ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ :=
    (hasFDerivAt_fst.add hasFDerivAt_snd).fderiv
  rw [h]
  change (1 : ℂ) + 2 = 3
  norm_num

end
end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.complexProduct_smoothOfRelativeDimension
#print axioms HodgeLean.Foundations.productChartComparison
#print axioms HodgeLean.Foundations.analyticAt_productChartComparison
#print axioms HodgeLean.Foundations.analyticAt_productChartComparison_symm
#print axioms HodgeLean.Foundations.identityChart
#print axioms HodgeLean.Foundations.identityChart_one
#print axioms HodgeLean.Foundations.chartGroupLaw
#print axioms HodgeLean.Foundations.chartGroupLaw_zero_right
#print axioms HodgeLean.Foundations.chartGroupLaw_zero_left
#print axioms HodgeLean.Foundations.chartGroupLaw_comm
#print axioms HodgeLean.Foundations.analyticAt_chartGroupLaw
#print axioms HodgeLean.Foundations.fderiv_chartGroupLaw
