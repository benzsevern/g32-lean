import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeSourceParameters
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeSliceIndex
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeCanonicalChart
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeChartTransport
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeIndexComparison
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeOrientation

/-! # Local degree from a regular parameter chart

An affine source slice carries the full stalk quotient length. Its local
index is transported to the original source and its prescribed orientation.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular HodgeLean.Adapters
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem local_degree_from_regular_parameter_chart
    {X Z : Over (Spec (CommRingCat.of ℂ))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [Smooth X.hom] [Smooth Z.hom] [T1Space (ComplexPoint X)]
    (f : X ⟶ Z) [Flat f.left] (d : ℕ) (x : ComplexPoint X)
    (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (eZ : OpenPartialHomeomorph (ComplexPoint Z) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (heX : a3b4_IsHolChart X.hom eX) (hx : x ∈ (pointChart eX).source)
    (heZ : a3b4_IsHolChart Z.hom eZ) (hz : Point.map f x ∈ (pointChart eZ).source)
    (hz0 : pointChart eZ (Point.map f x) = 0)
    (U : Set (ComplexPoint X)) (hU : IsOpen U) (hxU : x ∈ U)
    (hisol : ∀ z ∈ U, Point.map f z = Point.map f x → z = x)
    (A : Z.left.Opens) (hA : IsAffineOpen A) (hxA : (Point.map f x).underlying ∈ A)
    (g : Fin d → Γ(Z.left, A))
    (hvalues : ∀ z ∈ (pointChart eZ).source, ∀ k, pointChart eZ z k = Point.evaluate A (g k) z)
    (hreg : RingTheory.Sequence.IsRegular (Z.left.presheaf.stalk (Point.map f x).underlying)
      (List.ofFn fun k => Z.left.presheaf.germ A (Point.map f x).underlying hxA (g k)))
    (hgen : Ideal.ofList (List.ofFn fun k =>
      Z.left.presheaf.germ A (Point.map f x).underlying hxA (g k)) =
      IsLocalRing.maximalIdeal (Z.left.presheaf.stalk (Point.map f x).underlying))
    (m : ℕ) (hm : pointFibreLength f.left x.underlying = m) :
    relativeHomologyMap ℚ (2 * d) (isolatedPairMap (TopCat.ofHom (Point.continuousMap f)) U x hisol)
      (neighborhoodOrientation d (pointChart eX) x hx U hU hxU) =
      (m : ℚ) • localClassOfChart d (pointChart eZ) (Point.map f x) hz := by
  classical
  obtain ⟨V, hV, hxV, hVA, hdim⟩ := exists_affine_of_point_chart_dimension_within
    X d eX heX x hx (f.left ⁻¹ᵁ A) hxA
  let Y := ComplexPoint.openScheme X V
  let j := ComplexPoint.openInclusion X V
  let F := j ≫ f
  let w := ComplexPoint.asOpenPoint X V x hxV
  letI : IsAffine Y.left := hV
  letI : SmoothOfRelativeDimension d Y.hom := hdim
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X.hom))
  letI : QuasiCompact Y.hom := (quasiCompact_iff_compactSpace Y.hom).2 inferInstance
  letI : IsSeparated Y.hom := inferInstanceAs (IsSeparated (V.ι ≫ X.hom))
  letI : Nonempty (ComplexPoint Y) := ⟨w⟩
  have hjw : Point.map j w = x := Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac X V x hxV)
  have hFw : Point.map F w = Point.map f x := by rw [Point.map_comp_apply, hjw]
  letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V.ι)
  have himage : (⊤ : Y.left.Opens) ≤ F.left ⁻¹ᵁ A := by
    intro y _
    exact hVA y.property
  have hparams := parameter_germs_at_equal_point A g (F.left w.underlying)
    (Point.map f x).underlying (himage (by trivial)) hxA
    (congrArg Point.underlying hFw) hreg hgen
  have hm' : pointFibreLength f.left (j.left w.underlying) = m := by
    have hpoint : j.left w.underlying = x.underlying := congrArg Point.underlying hjw
    rw [hpoint]
    exact hm
  obtain ⟨hsreg, hslen⟩ := affine_source_parameter_slice j f A himage w d g
    hparams.1 hparams.2 m hm' 
  let s := fun k => F.left.appLE A ⊤ himage (g k)
  have hsvalues (y : ComplexPoint Y) (k : Fin d) :
      Point.evaluate ⊤ (s k) y = Point.evaluate A (g k) (Point.map F y) :=
    evaluate_appLE_parameter F A ⊤ himage y (by trivial) (g k)
  let W : Set (ComplexPoint Y) := Point.map j ⁻¹' U ∩ Point.map F ⁻¹' (pointChart eZ).source
  have hW : IsOpen W := (hU.preimage (Point.continuousMap j).continuous).inter
    ((pointChart eZ).open_source.preimage (Point.continuousMap F).continuous)
  have hwW : w ∈ W := by
    change Point.map j w ∈ U ∧ Point.map F w ∈ (pointChart eZ).source
    rw [hjw, hFw]
    exact ⟨hxU, hz⟩
  obtain ⟨a, ha, hwa, ha0, hasource, hainv, hatarget⟩ :=
    exists_centered_canonical_point_chart Y d w W hW hwW
  have hs0 (k : Fin d) : Point.evaluate ⊤ (s k) w = 0 := by
    rw [hsvalues, hFw, ← hvalues _ hz k]
    exact congrFun hz0 k
  have hisoa : ∀ y ∈ (pointChart a).source,
      (fun k => Point.evaluate ⊤ (s k) y) = 0 → y = w := by
    intro y hy hzero
    have hyW := hasource hy
    have hcoords : pointChart eZ (Point.map F y) = pointChart eZ (Point.map F w) := by
      rw [hFw, hz0]
      funext k
      exact (hvalues _ hyW.2 k).trans ((hsvalues y k).symm.trans (congrFun hzero k))
    have hFy := (pointChart eZ).injOn hyW.2 (hFw.symm ▸ hz) hcoords
    apply (ComplexPoint.isOpenEmbedding_map_open X V).injective
    rw [hjw]
    apply hisol (Point.map j y) hyW.1
    simpa only [F, Point.map_comp_apply, hFw] using hFy
  letI : SmoothOfRelativeDimension d (Over.mk (𝟙 Y.left ≫ Y.hom)).hom :=
    inferInstanceAs (SmoothOfRelativeDimension d Y.hom)
  letI : LocallyOfFiniteType (Over.mk (𝟙 Y.left ≫ Y.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  have hidval (y : ComplexPoint (Over.mk (𝟙 Y.left ≫ Y.hom))) (k : Fin d) :
      Point.evaluate (X := Over.mk Y.hom) ⊤ (s k) (Point.map (Over.homMk (𝟙 Y.left) rfl) y) =
        Point.evaluate ⊤ (s k) y := by
    rw [Point.evaluate_map]
    rfl
  obtain ⟨r, hr, hball, hc, hzero, hindex⟩ :=
    regular_sequence_slice_local_index Y.hom (𝟙 Y.left) inferInstance d ⊤
      (show IsAffineOpen (⊤ : Y.left.Opens) from isAffineOpen_top Y.left) s w w
      (by trivial) (by intro k; rw [hidval]; exact hs0 k)
      hsreg m hslen (pointChart a) hwa ha0 ((chartAt (Fin d → ℂ) w) w)
      hainv hatarget (by intros; trivial) (by
        intro y hy hz'
        apply hisoa y hy
        simpa only [hidval] using hz')
  simp only [hidval] at hc hzero hindex
  obtain ⟨E, hE, hEsource, hEvalues⟩ :=
    a3b4a_classHolomorphicChart_openTransport X V 0 d a ha
  have hxE : x ∈ (pointChart E).source := by
    refine ⟨?_, by trivial⟩
    change x ∈ E.source
    rw [hEsource]
    exact ⟨w, hwa.1, hjw⟩
  have hE0 : pointChart E x = 0 := by
    rw [← hjw]
    exact (congrArg Prod.snd (hEvalues w)).trans ha0
  have hEinv (v : Fin d → ℂ) (hv : v ∈ (pointChart a).target) :
      v ∈ (pointChart E).target ∧ (pointChart E).symm v = Point.map j ((pointChart a).symm v) :=
    transported_point_chart_inverse (Point.map j) d a E hEsource hEvalues v hv
  let P := fun y : ComplexPoint Y => fun k => Point.evaluate ⊤ (s k) y
  let G := fun v => P ((pointChart a).symm v)
  have hG (v : Fin d → ℂ) (hv : v ∈ Metric.ball 0 r) :
      G v = pointChart eZ (Point.map f ((pointChart E).symm v)) := by
    rw [(hEinv v (hball (Metric.ball_subset_closedBall hv))).2]
    funext k
    have hyW := hasource ((pointChart a).map_target (hball (Metric.ball_subset_closedBall hv)))
    exact (hsvalues _ k).trans (hvalues _ hyW.2 k).symm
  have hdeg : relativeHomologyMap ℚ (2 * d)
      (isolatedPairMap (TopCat.ofHom (Point.continuousMap f)) U x hisol)
      (neighborhoodOrientation d (pointChart E) x hxE U hU hxU) =
      (m : ℚ) • localClassOfChart d (pointChart eZ) (Point.map f x) hz := by
    apply degree_of_chart_expression (TopCat.ofHom (Point.continuousMap f)) d
      (pointChart E) (pointChart eZ) x hxE hz hE0 hz0 U hU hxU hisol
      (Metric.ball 0 r) Metric.isOpen_ball (Metric.mem_ball_self hr)
      (fun v hv => (hEinv v (hball (Metric.ball_subset_closedBall hv))).1)
      (fun v hv => ?_) (fun v hv => ?_) G hG hc hzero (m : ℚ)
    · intro z hzcoord
      exact hindex z hzcoord
    · rw [(hEinv v (hball (Metric.ball_subset_closedBall hv))).2]
      exact (hasource ((pointChart a).map_target (hball (Metric.ball_subset_closedBall hv)))).1
    · rw [(hEinv v (hball (Metric.ball_subset_closedBall hv))).2]
      exact (hasource ((pointChart a).map_target (hball (Metric.ball_subset_closedBall hv)))).2
  rw [holomorphic_neighborhood_orientation_independent X d eX E heX hE x hx hxE U hU hxU]
  exact hdeg

end AlgebraicGeometry.SingularCycles
