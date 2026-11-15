import HodgeLean.Foundations.ChowProjectiveProofs

/-! # Set-level Chow for complex projective varieties

The E² statements of `ChowAbelianSurface`, `ChowAbelianSurface2` and
`ChowAbelianSurface3`, restated over an arbitrary `X : Over (Spec ↧ℂ)`.
Claimed, each under the displayed instances:
* finite sets of complex points have closed scheme carriers (locally of finite type);
* the projective image of a closed analytic subset has analytic local equations
  and analytic standard affine slices, for any projective presentation
  (integral and smooth);
* the punctured homogeneous cone of a closed subset is closed (no instance);
* set-level Chow, in exactly the binder shape of `bhg_lefschetzOneOne_of_chow`
  (integral, smooth, projective);
* `LefschetzOneOneFor X` for every abelian `X` (integral, smooth, projective
  group object), as an implication from set-level Chow through the existing bridge.

Not claimed: Chow for singular or nonreduced projective schemes, a comparison
of analytic structures beyond complex points, or any Hodge-span statement beyond
the existing E² consumer. Set-level Chow and the abelian endpoint depend on the
open point-extension obligation `adim3_remmert_stein_point`, through
`chowEE3_vertex_extension_of_point`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Curves
namespace HodgeLean.Foundations

/-- Finite sets of complex points of a complex scheme locally of finite type have
their literal image as a closed scheme carrier.
Source: Mathlib `pointEquivClosedPoint`, `ext_of_apply_closedPoint_eq`
(closed points over an algebraically closed field); generalizes `chowEE_finite_algebraic`. -/
theorem chowG_finite_algebraic (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (Z : Set (ComplexPoint X)) (hZ : Z.Finite) :
    IsClosed ((Point.underlying : ComplexPoint X → X.left) '' Z) ∧
      Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹'
        ((Point.underlying : ComplexPoint X → X.left) '' Z) :=
  chowG_finite_algebraic_aux X Z hZ

/-- The point [1:0] of ℙ¹ has a closed scheme carrier.
Source: Hartshorne, Algebraic Geometry, Chapter II §2, closed points of ℙ¹. -/
example : IsClosed ((Point.underlying : ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))) →
        ProjectiveSpace (Fin 2) (Spec ↧ℂ)) ''
      {ComplexProjectiveSpace.vectorToComplexPoint (![1, 0] : Fin 2 → ℂ)
        (by intro h; have := congrFun h 0; norm_num at this)}) := by
  have : LocallyOfFiniteType
      (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))).hom := by
    change LocallyOfFiniteType (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
    infer_instance
  exact (chowG_finite_algebraic _ _ (finite_singleton _)).1

/-- The identity of the cubic curve has a closed scheme carrier.
Source: abelian exponential at zero and finite singletons. -/
example : IsClosed ({(abelianExp Curves.E 0).underlying} : Set Curves.E.left) ∧
    ({abelianExp Curves.E 0} : Set (ComplexPoint Curves.E)) =
      Point.underlying ⁻¹' {(abelianExp Curves.E 0).underlying} := by
  simpa only [image_singleton] using
    chowG_finite_algebraic Curves.E {abelianExp Curves.E 0} (finite_singleton _)

/-- Local equations for the projective image, anchored at a specified normalized point,
for any integral smooth complex scheme and any projective presentation.
Source: Serre, GAGA, §§1–2, analytification of closed immersions;
Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3, analytic subsets;
generalizes `chowEE2_embedding_local_equations`. -/
theorem chowG_embedding_local_equations (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (p : ProjectiveSpace.Presentation X.hom)
    (Z : Set (ComplexPoint X))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z)
    (i : Fin (p.ambientDimension + 1)) (w : Fin p.ambientDimension → ℂ)
    (hw : ∃ hn : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
      ∃ x ∈ Z, x.left ≫ p.immersion =
        ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hn) :
    ∃ U : Set (Fin p.ambientDimension → ℂ), IsOpen U ∧ w ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin p.ambientDimension → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ v ∈ U,
          ((∃ hn : (i.insertNth (1 : ℂ) v : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
            ∃ x ∈ Z, x.left ≫ p.immersion =
              ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) v) hn) ↔
            ∀ j, f j v = 0) :=
  chowG_embedding_local_equations_aux X p Z hZ i w hw

/-- Local equations at a normalized representative of the identity of the cubic curve.
Source: nonzero homogeneous representatives and normalization in a nonzero coordinate. -/
example : ∃ (p : ProjectiveSpace.Presentation Curves.E.hom)
    (i : Fin (p.ambientDimension + 1)) (w : Fin p.ambientDimension → ℂ),
    ∃ U : Set (Fin p.ambientDimension → ℂ), IsOpen U ∧ w ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin p.ambientDimension → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ v ∈ U,
          ((∃ hn : (i.insertNth (1 : ℂ) v : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
            ∃ x ∈ (univ : Set (ComplexPoint Curves.E)), x.left ≫ p.immersion =
              ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) v) hn) ↔
            ∀ j, f j v = 0) := by
  classical
  let p := Classical.choice
    (inferInstance : IsProjective Curves.E.hom).nonempty_presentation
  let x := abelianExp Curves.E 0
  obtain ⟨z, hz⟩ := ComplexProjectiveSpace.surjective_vectorToComplexPoint
    (p.analyticImmersion x)
  obtain ⟨i, hi⟩ : ∃ i, z.val i ≠ 0 := by
    by_contra h
    apply z.property
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  let w : Fin p.ambientDimension → ℂ := fun j ↦ z.val (i.succAbove j) / z.val i
  have hn : i.insertNth (1 : ℂ) w = (z.val i)⁻¹ • z.val := by
    apply Fin.insertNth_eq_iff.2
    constructor
    · simp [hi]
    · funext j
      simp [Fin.removeNth, w, div_eq_inv_mul]
  have hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0 := by
    rw [hn]
    exact smul_ne_zero (inv_ne_zero hi) z.property
  refine ⟨p, i, w, chowG_embedding_local_equations Curves.E p univ
    isClosedAnalytic_univ i w ⟨hw, x, mem_univ x, ?_⟩⟩
  have hbase : x.left ≫ p.immersion =
      ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property :=
    (congrArg (fun q ↦ q.left) hz).symm
  have hvec : (⟨i.insertNth (1 : ℂ) w, hw⟩ :
      {v : Fin (p.ambientDimension + 1) → ℂ // v ≠ 0}) =
      ⟨(z.val i)⁻¹ • z.val, smul_ne_zero (inv_ne_zero hi) z.property⟩ :=
    Subtype.ext hn
  have hproj := congrArg
    (fun v : {v : Fin (p.ambientDimension + 1) → ℂ // v ≠ 0} ↦
      ComplexProjectiveSpace.vectorToProjectiveSpace v.val v.property) hvec
  exact hbase.trans (hproj.trans
    (ComplexProjectiveSpace.vectorToProjectiveSpace_smul z.val z.property
      (z.val i)⁻¹ (inv_ne_zero hi))).symm

/-- Standard affine slices of the projective image of an analytic subset are analytic,
for any integral smooth complex scheme and any projective presentation.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
the projective cone construction; Serre, GAGA, §§1–2, analytification of closed
immersions; generalizes `chowEE2_embedding_slices`. -/
theorem chowG_embedding_slices (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (p : ProjectiveSpace.Presentation X.hom)
    (Z : Set (ComplexPoint X))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z)
    (i : Fin (p.ambientDimension + 1)) :
    IsClosedAnalytic (Fin p.ambientDimension → ℂ)
      {w : Fin p.ambientDimension → ℂ |
        ∃ hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
        ∃ x ∈ Z, x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw} :=
  chowG_embedding_slices_aux X p Z hZ i

/-- The whole threefold `E³` has analytic standard slices in its projective presentation.
Source: Segre projectivity for `g3_power E 3` and the empty family of analytic equations. -/
example : ∃ p : ProjectiveSpace.Presentation (g3_power E 3).hom,
    ∀ i : Fin (p.ambientDimension + 1),
    IsClosedAnalytic (Fin p.ambientDimension → ℂ)
      {w : Fin p.ambientDimension → ℂ |
        ∃ hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
        ∃ x ∈ (univ : Set (ComplexPoint (g3_power E 3))), x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw} := by
  let p := Classical.choice
    (inferInstance : IsProjective (g3_power E 3).hom).nonempty_presentation
  exact ⟨p, fun i ↦ chowG_embedding_slices _ p univ isClosedAnalytic_univ i⟩

/-- The cubic curve itself has analytic standard slices in its plane presentation.
Source: the plane cubic presentation of `Curves.E`. -/
example (i : Fin 3) :
    IsClosedAnalytic (Fin 2 → ℂ)
      {w : Fin 2 → ℂ |
        ∃ hw : (i.insertNth (1 : ℂ) w : Fin 3 → ℂ) ≠ 0,
        ∃ x ∈ (univ : Set (ComplexPoint Curves.E)), x.left ≫ cubicPresentation.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw} :=
  chowG_embedding_slices Curves.E cubicPresentation univ isClosedAnalytic_univ i

/-- The homogeneous-coordinate preimage of a closed set of complex points is closed off zero,
for any projective presentation.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
homogeneous coordinates; compact images in Hausdorff projective space;
generalizes `chowEE2_punctured_closed`. -/
theorem chowG_punctured_closed (X : Over (Spec ↧ℂ))
    (p : ProjectiveSpace.Presentation X.hom)
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
      ∃ x ∈ Z, x.left ≫ p.immersion =
        ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} :=
  chowG_punctured_closed_aux X p Z hZ

/-- ℙ¹ with its identity presentation: the punctured cone of the whole line is closed.
Source: Hartshorne, Algebraic Geometry, Chapter II §7, the identity closed immersion. -/
example : IsClosed {z : {z : Fin 2 → ℂ // z ≠ 0} |
    ∃ x ∈ (univ : Set (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))))),
      x.left ≫ 𝟙 _ = ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} :=
  chowG_punctured_closed (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))
    { ambientDimension := 1, immersion := 𝟙 _, immersion_toBase := by simp } univ isClosed_univ

/-- The identity of the cubic curve has a closed punctured cone.
Source: the plane cubic presentation of `Curves.E` and closed singletons. -/
example : IsClosed {z : {z : Fin 3 → ℂ // z ≠ 0} |
    ∃ x ∈ ({abelianExp Curves.E 0} : Set (ComplexPoint Curves.E)),
      x.left ≫ cubicPresentation.immersion =
        ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} :=
  chowG_punctured_closed Curves.E cubicPresentation _ isClosed_singleton

/-- Every closed analytic subset of an integral smooth projective complex scheme has a
closed scheme carrier.
Source: Chow, "On compact complex analytic varieties", Amer. J. Math. 71 (1949);
Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3, cone proof of Chow;
Serre, GAGA, §§1–2, analytification comparison; generalizes `chowEE3_setLevel`. -/
theorem chowG_setLevel (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ Z : Set (ComplexPoint X),
      IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
        ∃ C : Set X.left, IsClosed C ∧
          Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C :=
  chowG_setLevel_aux X

/-- The whole cubic curve has a closed carrier.
Source: the empty family of local analytic equations. -/
example : ∃ C : Set Curves.E.left, IsClosed C ∧
    (univ : Set (ComplexPoint Curves.E)) = Point.underlying ⁻¹' C :=
  chowG_setLevel Curves.E univ isClosedAnalytic_univ

/-- The empty subset of `E³` exercises the empty-carrier branch.
Source: empty analytic subsets. -/
example : ∃ C : Set (g3_power E 3).left, IsClosed C ∧
    (∅ : Set (ComplexPoint (g3_power E 3))) = Point.underlying ⁻¹' C :=
  chowG_setLevel (g3_power E 3) ∅ isClosedAnalytic_empty

/-- At `g3_power E 2` the general statement has the type of `chowEE3_setLevel`.
Source: `chowEE3_setLevel`. -/
example : ∀ Z : Set (ComplexPoint (g3_power E 2)),
    IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z →
      ∃ C : Set (g3_power E 2).left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint (g3_power E 2) →
          (g3_power E 2).left) ⁻¹' C :=
  chowG_setLevel (g3_power E 2)

/-- Lefschetz (1,1) for every complex abelian variety: an integral, smooth, projective
group object over `Spec ℂ`. Implication from set-level Chow through the existing bridge.
Source: Lefschetz (1,1) theorem as in Griffiths--Harris, Principles of Algebraic Geometry,
Chapter 1 §2; `bhg_lefschetzOneOne_of_chow` and `chowG_setLevel`. -/
theorem chowG_lefschetzOneOne_abelian (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    LefschetzOneOneFor X :=
  chowG_lefschetzOneOne_abelian_aux X

/-- The cubic curve.
Source: the cubic group structure of `Curves.E`. -/
example : LefschetzOneOneFor Curves.E :=
  chowG_lefschetzOneOne_abelian Curves.E

/-- Every positive power of the cubic curve.
Source: the abelian power `g3_power`. -/
example (n : ℕ) : LefschetzOneOneFor (g3_power E (n + 1)) :=
  chowG_lefschetzOneOne_abelian (g3_power E (n + 1))

/-- At `E²` the existing divisor-power consumer recovers `chowEE3_hdg_le_span_EE`.
Source: `ccm10_hdg_le_span_EE`. -/
example : ∀ p : ℕ, Hdg^p(g3_power E 2; ℚ) ≤ algebraicCycleClassSpan (g3_power E 2) p :=
  ccm10_hdg_le_span_EE (chowG_lefschetzOneOne_abelian (g3_power E 2))

end HodgeLean.Foundations
