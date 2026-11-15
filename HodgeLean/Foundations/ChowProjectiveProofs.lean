import HodgeLean.Foundations.ChowAbelianSurface3

/-! # Proof obligations for set-level Chow on complex projective varieties

The E² arguments, with `g3_power E 2` replaced by an arbitrary complex scheme
carrying the displayed scope instances. Point extension stays the single open
transitive obligation, through `chowEE3_vertex_extension_of_point`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

/-- Source: closed complex points over an algebraically closed field;
Mathlib `pointEquivClosedPoint` and `ext_of_apply_closedPoint_eq`. -/
theorem chowG_finite_algebraic_aux (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (Z : Set (ComplexPoint X)) (hZ : Z.Finite) :
    IsClosed ((Point.underlying : ComplexPoint X → X.left) '' Z) ∧
      Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹'
        ((Point.underlying : ComplexPoint X → X.left) '' Z) := by
  constructor
  · rw [show Point.underlying '' Z = ⋃ z : Z, ({z.1.underlying} : Set X.left) by
      ext y
      simp]
    have : Finite Z := hZ
    apply isClosed_iUnion_of_finite
    intro z
    exact ((pointEquivClosedPoint X.hom) ⟨z.1.left, Over.w z.1⟩).2
  · apply Set.Subset.antisymm
    · intro z hz
      exact ⟨z, hz, rfl⟩
    · rintro z ⟨w, hw, hzw⟩
      have : z = w := by
        apply Over.OverMorphism.ext
        exact ext_of_apply_closedPoint_eq X.hom (Over.w z) (Over.w w) hzw.symm
      simpa [this] using hw

/-- Source: Serre, GAGA, §§1–2, analytification of closed immersions;
the E² argument `chowEE2_embedding_local_equations_aux`. -/
theorem chowG_embedding_local_equations_aux (X : Over (Spec ↧ℂ))
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
            ∀ j, f j v = 0) := by
  classical
  obtain ⟨hn, x, hx, hxw⟩ := hw
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
      have hc := (hUprops v hv).2.2.1.comp (hL v (hUprops v hv).1)
      exact (analyticAt_pi_iff.mp hc k).sub (analyticAt_pi_iff.mp analyticAt_id k)
    · intro v hv
      simp only [g, Fin.addCases_right]
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

/-- Source: compact images in Hausdorff projective space;
the E² argument `chowEE2_punctured_closed_aux`. -/
theorem chowG_punctured_closed_aux (X : Over (Spec ↧ℂ))
    (p : ProjectiveSpace.Presentation X.hom)
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
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
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, hx, Over.OverMorphism.ext heq⟩
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, hx, congrArg (fun q ↦ q.left) heq⟩

/-- Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3;
the E² argument `chowEE2_embedding_slices_aux`. -/
theorem chowG_embedding_slices_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom]
    (p : ProjectiveSpace.Presentation X.hom)
    (Z : Set (ComplexPoint X))
    (hZ : IsClosedAnalytic (Fin (dim X.left) → ℂ) Z)
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
    have hpre := (chowG_punctured_closed_aux X p Z hZ.isClosed).preimage hF
    convert hpre using 1
    ext w
    simp only [S, F, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hw, x, hx, heq⟩
      exact ⟨x, hx, heq⟩
    · rintro ⟨x, hx, heq⟩
      exact ⟨hne w, x, hx, heq⟩
  refine ⟨hclosed, ?_⟩
  intro w hw
  obtain ⟨U, hU, hwU, m, f, hf, hiff⟩ :=
    chowG_embedding_local_equations_aux X p Z hZ i w hw
  refine ⟨U, hU, hwU, Set.subset_univ U, m, f, hf, ?_⟩
  intro v hv
  rw [chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
  change (v ∈ S ↔ ∀ j, f j v = 0)
  exact hiff v hv

/-- Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
cone proof of Chow; the E² assembly `chowEE3_setLevel_aux`. -/
theorem chowG_setLevel_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∀ Z : Set (ComplexPoint X),
      IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
        ∃ C : Set X.left, IsClosed C ∧
          Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C := by
  classical
  intro Z hZ
  by_cases hne : Z.Nonempty
  swap
  · exact ⟨∅, isClosed_empty, by simp [not_nonempty_iff_eq_empty.mp hne]⟩
  let p := Classical.choice
    (inferInstance : IsProjective X.hom).nonempty_presentation
  let K : Set (Fin (p.ambientDimension + 1) → ℂ) :=
    {z | ∃ hz : z ≠ 0, ∃ x ∈ Z, x.left ≫ p.immersion =
      ComplexProjectiveSpace.vectorToProjectiveSpace z hz}
  have hkzero : (0 : Fin (p.ambientDimension + 1) → ℂ) ∉ K :=
    fun ⟨hz, _⟩ ↦ hz rfl
  have hkne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨z, hz⟩ := ComplexProjectiveSpace.surjective_vectorToComplexPoint
      (p.analyticImmersion x)
    exact ⟨z.val, z.property, x, hx, (congrArg (fun q ↦ q.left) hz).symm⟩
  have hkclosed : IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
      z.val ∈ K} := by
    convert chowG_punctured_closed_aux X p Z hZ.isClosed using 1
    ext z
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨z.property, h⟩⟩
  have hkscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ K, t • z ∈ K := by
    rintro t ht z ⟨hz, x, hx, he⟩
    exact ⟨smul_ne_zero ht hz, x, hx, he.trans
      (ComplexProjectiveSpace.vectorToProjectiveSpace_smul z hz t ht).symm⟩
  have hkloc : ∀ x ∈ K, ∃ U : Set (Fin (p.ambientDimension + 1) → ℂ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ {z | z ≠ 0} ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (p.ambientDimension + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ K ↔ ∀ j, f j z = 0) := by
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hx.1 (funext fun i ↦ not_ne_iff.mp (not_exists.mp h i))
    obtain ⟨U, hU, hxU, hUi, hrest⟩ :=
      chow2_chart_cone p.ambientDimension K hkscale i
        (chowG_embedding_slices_aux X p Z hZ i) x hx hi
    refine ⟨U, hU, hxU, ?_, hrest⟩
    intro z hz he
    exact hUi hz (congrFun he i)
  have hD := chowEE3_vertex_extension_of_point p.ambientDimension K
    hkzero hkne hkclosed hkscale hkloc
  have hDscale : ∀ (t : ℂ) (z : Fin (p.ambientDimension + 1) → ℂ),
      z ∈ insert 0 K → t • z ∈ insert 0 K := by
    intro t z hz
    by_cases ht : t = 0
    · simp only [ht, zero_smul, mem_insert_iff, true_or]
    rcases hz with rfl | hz
    · exact Or.inl (smul_zero t)
    · exact Or.inr (hkscale t ht z hz)
  obtain ⟨m, d, P, hP, hDP⟩ :=
    chow_cone_algebraic (p.ambientDimension + 1) (insert 0 K) hD hDscale
  let B := chowEE_projectiveCarrier p.ambientDimension m P
  refine ⟨p.immersion ⁻¹' B, isClosed_closure.preimage p.immersion.continuous, ?_⟩
  ext x
  obtain ⟨z, hz⟩ := ComplexProjectiveSpace.surjective_vectorToComplexPoint
    (p.analyticImmersion x)
  have hund : (ComplexProjectiveSpace.vectorToComplexPoint z.val z.property).underlying =
      p.immersion x.underlying :=
    (congrArg (fun q ↦ q.underlying) hz).trans
      (Point.underlying_map p.overImmersion x)
  change x ∈ Z ↔ p.immersion x.underlying ∈ B
  rw [← hund, chowEE_projectiveCarrier_mem p.ambientDimension m d P hP]
  change x ∈ Z ↔ z.val ∈ {z | ∀ j, MvPolynomial.eval z (P j) = 0}
  rw [← hDP]
  constructor
  · intro hx
    exact Or.inr ⟨z.property, x, hx, (congrArg (fun q ↦ q.left) hz).symm⟩
  · intro hzK
    rcases hzK with hz0 | ⟨_, y, hy, he⟩
    · exact (z.property hz0).elim
    · have hyx : p.analyticImmersion y = p.analyticImmersion x :=
        (Over.OverMorphism.ext he).trans hz
      exact p.analyticImmersion_isClosedEmbedding.injective hyx ▸ hy

/-- Source: the Chow-to-Lefschetz bridge `bhg_lefschetzOneOne_of_chow`. -/
theorem chowG_lefschetzOneOne_abelian_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    LefschetzOneOneFor X :=
  bhg_lefschetzOneOne_of_chow X (chowG_setLevel_aux X)

end HodgeLean.Foundations
