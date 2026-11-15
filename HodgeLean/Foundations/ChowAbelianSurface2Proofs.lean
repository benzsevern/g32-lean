import HodgeLean.Foundations.ChowAbelianSurface
import HodgeLean.Foundations.ChowTheorem2
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8CurvatureProofs

/-! # Projective comparison obligations for E²

Implications from closed analyticity to embedding slices and from closedness to
punctured-cone closedness. Vertex extension and final Chow assembly are deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Curves
namespace HodgeLean.Foundations

open ComplexProjectiveSpace in
/-- Evaluation of a regular section is analytic in the normalized slice coordinates. -/
theorem chowEE2_analyticAt_evaluate_normalized {N : ℕ} (i : Fin (N + 1))
    (V : (ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ)).Opens)
    (r : Γ(ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ), V))
    (w : Fin N → ℂ)
    (hw : vectorToComplexPoint (i.insertNth 1 w)
      (by intro h; have := congrFun h i; simp at this) ∈ Point.overOpen V) :
    AnalyticAt ℂ (fun v : Fin N → ℂ ↦ Point.evaluate V r
      (vectorToComplexPoint (i.insertNth 1 v)
        (by intro h; have := congrFun h i; simp at this))) w := by
  have hins : AnalyticAt ℂ (fun v : Fin N → ℂ ↦ (i.insertNth (1 : ℂ) v : Fin (N + 1) → ℂ)) w := by
    apply AnalyticAt.pi
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simpa only [Fin.insertNth_apply_same] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : Fin N → ℂ ↦ (1 : ℂ)) w)
    · simp only [Fin.insertNth_apply_succAbove]
      convert (ContinuousLinearMap.proj k : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt w using 1
      rfl
  have he (v : Fin N → ℂ) := bh8_chartAffine_normalized i (i.insertNth 1 v)
    (by simp only [Fin.insertNth_apply_same])
    (by intro h; have := congrFun h i; simp at this)
  have ha := bh8_analyticAt_evaluate_projective_chart i V r (i.insertNth 1 w)
    (by rw [he]; exact hw)
  simpa only [Function.comp_def, he] using ha.comp hins

/-- The normalized standard projective chart, with its distinguished coordinate equal to one. -/
def chowEE2_normalizedPoint {N : ℕ} (i : Fin (N + 1)) (w : Fin N → ℂ) :
    ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))) :=
  ComplexProjectiveSpace.vectorToComplexPoint (i.insertNth 1 w)
    (by intro h; have := congrFun h i; simp at this)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalized standard projective coordinates vary continuously. -/
theorem chowEE2_continuous_normalizedPoint {N : ℕ} (i : Fin (N + 1)) :
    Continuous (chowEE2_normalizedPoint i) := by
  have hv : Continuous (fun w : Fin N → ℂ ↦
      (i.insertNth (1 : ℂ) w : Fin (N + 1) → ℂ)) := by
    apply continuous_pi
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simpa only [Fin.insertNth_apply_same] using
        (continuous_const : Continuous (fun _ : Fin N → ℂ ↦ (1 : ℂ)))
    · simpa only [Fin.insertNth_apply_succAbove] using
        (continuous_apply k : Continuous (fun v : Fin N → ℂ ↦ v k))
  let f : (Fin N → ℂ) → {v : Fin (N + 1) → ℂ // v ≠ 0} :=
    fun w ↦ ⟨i.insertNth 1 w, by intro h; have := congrFun h i; simp at this⟩
  have hf : Continuous f := hv.subtype_mk _
  convert (ComplexProjectiveSpace.continuous_vectorToComplexPoint (n := N)).comp hf using 1
  rfl

open Filter Topology in
/-- Lifted intrinsic coordinate sections give an analytic coordinate recovery map on a
normalized ambient neighborhood. -/
theorem chowEE2_exists_normalized_coordinate_recovery
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ProjectiveSpace.Presentation X.hom)
    (x : ComplexPoint X) (i : Fin (p.ambientDimension + 1))
    (w : Fin p.ambientDimension → ℂ)
    (hw : chowEE2_normalizedPoint i w = Point.map p.overImmersion x) :
    ∃ (U : Set (Fin p.ambientDimension → ℂ))
      (L : (Fin p.ambientDimension → ℂ) → (Fin d → ℂ)),
      IsOpen U ∧ w ∈ U ∧ AnalyticOnNhd ℂ L U ∧
      ∀ v ∈ U, ∀ y ∈ (localChart X d x).source,
        chowEE2_normalizedPoint i v = Point.map p.overImmersion y →
          L v = localChart X d x y := by
  let D := localEtaleCoordinates X d x
  have hxD : x.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      Point.overOpen, Set.mem_ofPred_eq] using mem_localEtaleCoordinates X d x
  let : IsClosedImmersion p.immersion := p.isClosedImmersion
  obtain ⟨V, _, hVD, hxV, r, hr⟩ := p.immersion.exists_affine_local_section_lifts
    D.ambientCoordinateOpen D.ambientCoordinateSection x.underlying hxD
  let U := chowEE2_normalizedPoint i ⁻¹' Point.overOpen V
  let L : (Fin p.ambientDimension → ℂ) → (Fin d → ℂ) :=
    fun v j ↦ Point.evaluate V (r j) (chowEE2_normalizedPoint i v)
  refine ⟨U, L, (Point.isOpen_overOpen V).preimage
    (chowEE2_continuous_normalizedPoint i), ?_, ?_, ?_⟩
  · change chowEE2_normalizedPoint i w ∈ Point.overOpen V
    rw [hw]
    exact hxV
  · intro v hv
    exact AnalyticAt.pi fun j ↦ chowEE2_analyticAt_evaluate_normalized i V (r j) v hv
  · intro v hv y hy he
    funext j
    change Point.evaluate V (r j) (chowEE2_normalizedPoint i v) = _
    rw [he, Point.evaluate_map]
    change Point.evaluate (p.immersion ⁻¹ᵁ V) (p.immersion.app V (r j)) y = _
    rw [hr]
    have hyV : y ∈ Point.overOpen (p.immersion ⁻¹ᵁ V) := by
      apply (Point.mem_overOpen_map_iff p.overImmersion y V).mp
      rw [← he]
      exact hv
    rw [← Point.evaluate_res hVD (D.ambientCoordinateSection j) y hyV]
    exact (localChart_apply_component_eq_evaluate X d x y hy j).symm

/-- The closed embedding excludes preimages outside the chosen intrinsic chart after shrinking. -/
theorem chowEE2_exists_normalized_retraction
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ProjectiveSpace.Presentation X.hom)
    (x : ComplexPoint X) (i : Fin (p.ambientDimension + 1))
    (w : Fin p.ambientDimension → ℂ)
    (hw : chowEE2_normalizedPoint i w = Point.map p.overImmersion x) :
    ∃ (U : Set (Fin p.ambientDimension → ℂ))
      (L : (Fin p.ambientDimension → ℂ) → (Fin d → ℂ)),
      IsOpen U ∧ w ∈ U ∧ AnalyticOnNhd ℂ L U ∧
      L w = localChart X d x x ∧
      ∀ v ∈ U, ∀ y : ComplexPoint X,
        chowEE2_normalizedPoint i v = Point.map p.overImmersion y →
          y ∈ (localChart X d x).source ∧ L v = localChart X d x y := by
  obtain ⟨U, L, hU, hwU, hL, hrec⟩ :=
    chowEE2_exists_normalized_coordinate_recovery X d p x i w hw
  obtain ⟨W, hW, he⟩ := p.analyticImmersion_isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp
    (localChart X d x).open_source
  have hxW : Point.map p.overImmersion x ∈ W := by
    change x ∈ p.analyticImmersion ⁻¹' W
    rw [he]
    exact mem_localChart_source X d x
  refine ⟨U ∩ chowEE2_normalizedPoint i ⁻¹' W, L,
    hU.inter (hW.preimage (chowEE2_continuous_normalizedPoint i)),
    ⟨hwU, ?_⟩, hL.mono inter_subset_left,
    hrec w hwU x (mem_localChart_source X d x) hw, ?_⟩
  · change chowEE2_normalizedPoint i w ∈ W
    rw [hw]
    exact hxW
  · intro v hv y hy
    have hys : y ∈ (localChart X d x).source := by
      rw [← he]
      change Point.map p.overImmersion y ∈ W
      rw [← hy]
      exact hv.2
    exact ⟨hys, hrec v hv.1 y hys hy⟩

/-- Two normalized vectors in a fixed standard projective chart represent different points. -/
theorem chowEE2_normalizedPoint_injective {N : ℕ} (i : Fin (N + 1)) :
    Function.Injective (chowEE2_normalizedPoint i) := by
  intro v w h
  obtain ⟨c, hc⟩ := bh8_projective_coordinates_proportional
    (i.insertNth 1 v) (i.insertNth 1 w)
    (by intro h; have := congrFun h i; simp at this)
    (by intro h; have := congrFun h i; simp at this) h
  have hc1 : c = 1 := by
    have hi := congrFun hc i
    simpa only [Fin.insertNth_apply_same, Pi.smul_apply, smul_eq_mul, mul_one] using hi.symm
  rw [hc1, one_smul] at hc
  funext j
  have hj := congrFun hc (i.succAbove j)
  simpa only [Fin.insertNth_apply_succAbove] using hj.symm

attribute [local instance] MvPolynomial.gradedAlgebra in
open ComplexProjectiveSpace Filter Topology in
/-- An intrinsic smooth chart has an analytic lift into any normalized projective chart
containing its center. -/
theorem chowEE2_exists_normalized_chart_lift
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ProjectiveSpace.Presentation X.hom)
    (x : ComplexPoint X) (i : Fin (p.ambientDimension + 1))
    (w : Fin p.ambientDimension → ℂ)
    (hw : chowEE2_normalizedPoint i w = Point.map p.overImmersion x) :
    ∃ F : (Fin d → ℂ) → (Fin p.ambientDimension → ℂ),
      AnalyticAt ℂ F (localChart X d x x) ∧ F (localChart X d x x) = w ∧
      ∀ᶠ u in 𝓝 (localChart X d x x),
        chowEE2_normalizedPoint i (F u) =
          Point.map p.overImmersion ((localChart X d x).symm u) := by
  let q := p.immersion ≫ Limits.pullback.snd
    (Limits.terminal.from (Spec ↧ℂ))
    (Limits.terminal.from (Proj (UniversalGrading p.ambientDimension)))
  let V := Proj.basicOpen (UniversalGrading p.ambientDimension) (MvPolynomial.X i)
  let e := localChart X d x
  have hx : x ∈ e.source := mem_localChart_source X d x
  have hxt : e x ∈ e.target := e.map_source hx
  have hxV : x ∈ Point.overOpen (q ⁻¹ᵁ V) := by
    have h := vectorToComplexPoint_mem_projectiveSpaceBasicOpen
      (i.insertNth 1 w)
      (show (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0 from
        by intro h; have := congrFun h i; simp at this)
      (MvPolynomial.X i) zero_lt_one (MvPolynomial.isHomogeneous_X _ _)
      (by simp only [coordinateEvaluationHom_X, Fin.insertNth_apply_same, ne_eq,
        one_ne_zero, not_false_eq_true])
    change chowEE2_normalizedPoint i w ∈ Point.overOpen _ at h
    rw [hw] at h
    exact h
  let s : (Fin d → ℂ) → CoordinateSpace p.ambientDimension := fun u j ↦
    Point.evaluate (q ⁻¹ᵁ V)
      (q.app V ((Proj.awayToSection (UniversalGrading p.ambientDimension) (MvPolynomial.X i))
        (chartCoordinate i j))) (e.symm u)
  have hs : AnalyticAt ℂ s (e x) := by
    apply AnalyticAt.pi
    intro j
    apply analyticAt_localChart_symm_evaluate X d x hxt
    change e.symm (e x) ∈ Point.overOpen (q ⁻¹ᵁ V)
    rw [e.left_inv hx]
    exact hxV
  have hV : ∀ᶠ u in 𝓝 (e x), e.symm u ∈ Point.overOpen (q ⁻¹ᵁ V) := by
    apply (e.continuousAt_symm hxt) ((Point.isOpen_overOpen _).mem_nhds _)
    rw [e.left_inv hx]
    exact hxV
  have hsi (u) (hu : e.symm u ∈ Point.overOpen (q ⁻¹ᵁ V)) : s u i = 1 := by
    dsimp only [s]
    rw [chartCoordinate_self, map_one, map_one]
    rw [Point.evaluate, dite_eq_left (show (e.symm u).underlying ∈ q ⁻¹ᵁ V from hu),
      map_one, map_one]
  let F : (Fin d → ℂ) → (Fin p.ambientDimension → ℂ) := fun u ↦ i.removeNth (s u)
  have hF : AnalyticAt ℂ F (e x) := by
    apply AnalyticAt.pi
    intro j
    exact analyticAt_pi_iff.mp hs (i.succAbove j)
  have he : ∀ᶠ u in 𝓝 (e x), chowEE2_normalizedPoint i (F u) =
      Point.map p.overImmersion (e.symm u) := by
    filter_upwards [hV] with u hu
    obtain ⟨hne, hrepr⟩ := bh8_pullback_projective_coordinates_represent X q i (e.symm u) hu
    have hins : i.insertNth (1 : ℂ) (F u) = s u := by
      change i.insertNth (1 : ℂ) (i.removeNth (s u)) = s u
      rw [Fin.insertNth_removeNth, ← hsi u hu, Function.update_eq_self]
    have hp : vectorToComplexPoint (s u) hne = Point.map p.overImmersion (e.symm u) := by
      apply Over.OverMorphism.ext
      apply Limits.pullback.hom_ext
      · exact (vectorToProjectiveSpace_toBase (s u) hne).trans
          (Over.w (Point.map p.overImmersion (e.symm u))).symm
      · exact (vectorToProjectiveSpace_toProj (s u) hne).trans hrepr
    unfold chowEE2_normalizedPoint
    simpa only [hins] using hp
  refine ⟨F, hF, ?_, he⟩
  apply chowEE2_normalizedPoint_injective i
  rw [he.self_of_nhds, e.left_inv hx, hw]

open Filter Topology in
/-- Local equations for the projective image, anchored at a specified normalized point.
Source: Serre, GAGA, §§1–2, analytification of closed immersions;
Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3, analytic subsets. -/
theorem chowEE2_embedding_local_equations_aux
    (p : ProjectiveSpace.Presentation (g3_power E 2).hom)
    (Z : Set (ComplexPoint (g3_power E 2)))
    (hZ : IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z)
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
            ∀ j, f j v = 0) := by
  classical
  obtain ⟨hn, x, hx, hxw⟩ := hw
  let X := g3_power E 2
  let d := dim X.left
  let e := localChart X d x
  have hw' : chowEE2_normalizedPoint i w = Point.map p.overImmersion x := by
    apply Over.OverMorphism.ext
    exact hxw.symm
  obtain ⟨U₀, L, hU₀, hwU₀, hL, hLw, hrec⟩ :=
    chowEE2_exists_normalized_retraction X d p x i w hw'
  obtain ⟨F, hF, _, hFe⟩ := chowEE2_exists_normalized_chart_lift X d p x i w hw'
  obtain ⟨V, hV, hxV, hVt, m, f, hf, hZf⟩ := hZ.2 x hx
  have hxV' : e x ∈ V := hxV
  have hnear : ∀ᶠ v in nhds w, v ∈ U₀ ∧ L v ∈ V ∧
      AnalyticAt ℂ F (L v) ∧
      chowEE2_normalizedPoint i (F (L v)) = Point.map p.overImmersion (e.symm (L v)) := by
    have hc := (hL w hwU₀).continuousAt
    have h₁ : ∀ᶠ v in nhds w, L v ∈ V :=
      hc (by rw [hLw]; exact hV.mem_nhds hxV')
    have h₂ : ∀ᶠ v in nhds w, AnalyticAt ℂ F (L v) :=
      hc (by rw [hLw]; exact hF.eventually_analyticAt)
    have h₃ : ∀ᶠ v in nhds w,
        chowEE2_normalizedPoint i (F (L v)) = Point.map p.overImmersion (e.symm (L v)) :=
      hc (by rw [hLw]; exact hFe)
    filter_upwards [hU₀.mem_nhds hwU₀, h₁, h₂, h₃] with v hv hv₁ hv₂ hv₃
    exact ⟨hv, hv₁, hv₂, hv₃⟩
  obtain ⟨U, hUprops, hU, hwU⟩ := eventually_nhds_iff.mp hnear
  let g : Fin (p.ambientDimension + m) → (Fin p.ambientDimension → ℂ) → ℂ :=
    Fin.addCases (fun j v ↦ F (L v) j - v j) (fun j v ↦ f j (L v))
  have hg (j : Fin (p.ambientDimension + m)) : AnalyticOnNhd ℂ (g j) U := by
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · intro v hv
      simp only [g, Fin.addCases_left]
      change AnalyticAt ℂ (fun v ↦ F (L v) k - v k) v
      have hc := (hUprops v hv).2.2.1.comp (hL v (hUprops v hv).1)
      exact (analyticAt_pi_iff.mp hc k).sub (analyticAt_pi_iff.mp analyticAt_id k)
    · intro v hv
      simp only [g, Fin.addCases_right]
      change AnalyticAt ℂ (fun v ↦ f k (L v)) v
      exact (hf k (L v) (hUprops v hv).2.1).comp (hL v (hUprops v hv).1)
  refine ⟨U, hU, hwU, p.ambientDimension + m, g, hg, ?_⟩
  intro v hv
  have hgv : (∀ j, g j v = 0) ↔ F (L v) = v ∧ ∀ j, f j (L v) = 0 := by
    simp only [g, Fin.forall_fin_add, Fin.addCases_left, Fin.addCases_right, sub_eq_zero]
    exact and_congr (funext_iff.symm) Iff.rfl
  rw [hgv]
  constructor
  · rintro ⟨hnv, y, hy, hyv⟩
    have hev : chowEE2_normalizedPoint i v = Point.map p.overImmersion y := by
      apply Over.OverMorphism.ext
      exact hyv.symm
    obtain ⟨hys, hLy⟩ := hrec v (hUprops v hv).1 y hev
    have hsymm : e.symm (L v) = y := by
      rw [hLy]
      exact e.left_inv hys
    refine ⟨?_, ?_⟩
    · apply chowEE2_normalizedPoint_injective i
      rw [(hUprops v hv).2.2.2, hsymm, hev]
    · apply (hZf (L v) (hUprops v hv).2.1).mp
      change e.symm (L v) ∈ Z
      rw [hsymm]
      exact hy
  · rintro ⟨hfixed, hzero⟩
    have hyZ := (hZf (L v) (hUprops v hv).2.1).mpr hzero
    have he := (hUprops v hv).2.2.2
    rw [hfixed] at he
    refine ⟨?_, e.symm (L v), hyZ, ?_⟩
    · intro h
      have := congrFun h i
      simp at this
    · exact (congrArg (fun q ↦ q.left) he).symm

/-- Standard affine slices of the projective image of an analytic subset of E² are analytic.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
local analytic submanifolds and the projective cone construction;
Serre, GAGA, §§1–2, analytification of closed immersions. -/
theorem chowEE2_embedding_slices_aux
    (p : ProjectiveSpace.Presentation (g3_power E 2).hom)
    (Z : Set (ComplexPoint (g3_power E 2)))
    (hZ : IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z)
    (i : Fin (p.ambientDimension + 1)) :
    IsClosedAnalytic (Fin p.ambientDimension → ℂ)
      {w : Fin p.ambientDimension → ℂ |
        ∃ hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
        ∃ x ∈ Z, x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw} := by
  classical
  let S : Set (Fin p.ambientDimension → ℂ) :=
    {w | ∃ hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
      ∃ x ∈ Z, x.left ≫ p.immersion =
        ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw}
  have hne (w : Fin p.ambientDimension → ℂ) :
      (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0 := by
    intro h
    have := congrFun h i
    simp at this
  let F : (Fin p.ambientDimension → ℂ) →
      {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} :=
    fun w ↦ ⟨i.insertNth (1 : ℂ) w, hne w⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    fun_prop
  have hclosed : IsClosed S := by
    have hImage : IsClosed (p.analyticImmersion '' Z) :=
      p.analyticImmersion_isClosedEmbedding.isClosedMap Z hZ.isClosed
    have hp := hImage.preimage
      (ComplexProjectiveSpace.continuous_vectorToComplexPoint
        (n := p.ambientDimension))
    have hp' : IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
        ∃ x ∈ Z, x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} := by
      convert hp using 1
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨x, hx, heq⟩
        exact ⟨x, hx, Over.OverMorphism.ext heq⟩
      · rintro ⟨x, hx, heq⟩
        exact ⟨x, hx, congrArg (fun q ↦ q.left) heq⟩
    have hpre := hp'.preimage hF
    convert hpre using 1
    ext w
    simp only [S, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hw, x, hx, heq⟩
      exact ⟨x, hx, heq⟩
    · rintro ⟨x, hx, heq⟩
      exact ⟨hne w, x, hx, heq⟩
  refine ⟨hclosed, ?_⟩
  intro w hw
  obtain ⟨U, hU, hwU, m, f, hf, hiff⟩ :=
    chowEE2_embedding_local_equations_aux p Z hZ i w hw
  refine ⟨U, hU, hwU, Set.subset_univ U, m, f, hf, ?_⟩
  intro v hv
  rw [chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
  change (v ∈ S ↔ ∀ j, f j v = 0)
  exact hiff v hv

/-- The homogeneous-coordinate preimage of a closed subset of E² is closed off zero.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
homogeneous coordinates; compact images in Hausdorff projective space. -/
theorem chowEE2_punctured_closed_aux
    (p : ProjectiveSpace.Presentation (g3_power E 2).hom)
    (Z : Set (ComplexPoint (g3_power E 2))) (hZ : IsClosed Z) :
    IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
      ∃ x ∈ Z, x.left ≫ p.immersion =
        ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} := by
  have hImage : IsClosed (p.analyticImmersion '' Z) :=
    p.analyticImmersion_isClosedEmbedding.isClosedMap Z hZ
  have hPreimage := hImage.preimage
    (ComplexProjectiveSpace.continuous_vectorToComplexPoint
      (n := p.ambientDimension))
  convert hPreimage using 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, hx, Over.OverMorphism.ext heq⟩
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, hx, congrArg (fun q ↦ q.left) heq⟩

end HodgeLean.Foundations
