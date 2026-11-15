import HodgeLean.RealDefs.ComplexFundamentalClass
import HodgeLean.RealDefs.OrientationConstant
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import HodgeLean.Foundations.ComplexSheafSingular
import HodgeLean.Foundations.Curves.CurveCycleClass
import HodgeLean.RealDefs.DimensionThree
import HodgeLean.RealDefs.FundamentalClass.Point

/-! # Proof obligations for the frozen top-degree rank spec (J5d)

One `_aux` theorem per statement of `TopDegreeRank.lean`; all twelve are proved, by four parallel
provers (statements 1-3 and 8; 4; 5-7; 9-12). The route for each is in
`docs/specs/TopDegreeRank.md`, section "Route".
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

theorem j5d_eq_smul_of_pointValues_aux {M E : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {n : ℕ} (hn : Module.finrank ℝ E = n)
    (v w : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens M) : Set M)ᶜ : Set (TopCat.of M))) n) (q : ℚ)
    (h : ∀ y : M,
      relativeHomologyMap ℚ n
          (supportInclusionPairMap (TopCat.of M)
            (Set.singleton_subset_iff.mpr (Opens.mem_top y))) v =
        q • relativeHomologyMap ℚ n
          (supportInclusionPairMap (TopCat.of M)
            (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w) :
    v = q • w := by
  have hdet := (j5c_compact_manifold hn (isCompact_univ (X := M))).2
  refine sub_eq_zero.mp (hdet (v - q • w) fun y _ => ?_)
  rw [map_sub, map_smul]
  exact sub_eq_zero.mpr (h y)

theorem j5d_eq_smul_of_complexFundamentalClass_aux (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (w : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))) (2 * d))
    (hw : ∀ y : ComplexPoint X,
      relativeHomologyMap ℚ (2 * d)
          (supportInclusionPairMap (TopCat.of (ComplexPoint X))
            (Set.singleton_subset_iff.mpr (Opens.mem_top y))) w =
        complexLocalOrientation X d y)
    (v : RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))) (2 * d)) :
    ∃ q : ℚ, v = q • w := by
  have := hconn.preconnected X
  obtain ⟨q, hq⟩ := exists_relativeHomologyMap_eq_smul_complexLocalOrientation X d v
  refine ⟨q, j5d_eq_smul_of_pointValues_aux (E := Fin d → ℂ)
    (by rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm])
    v w q fun y => ?_⟩
  rw [hq y, hw y]

theorem j5d_finrank_complexTopHomology_aux (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    Module.finrank ℚ (RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))) (2 * d)) = 1 := by
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass X d
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : ConnectedSpace (ComplexPoint X) := AlgebraicGeometry.ComplexPoint.connectedSpace X
  obtain ⟨y⟩ := (inferInstance : Nonempty (ComplexPoint X))
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 := analyticPointLocalCoclass_apply_complexLocalOrientation X d y
    rw [← hw y, h0, map_zero, map_zero] at h1
    exact zero_ne_one h1
  refine (finrank_eq_one_iff_of_nonzero' w hw0).mpr fun v => ?_
  obtain ⟨q, hq⟩ := j5d_eq_smul_of_complexFundamentalClass_aux hconn X d w hw v
  exact ⟨q, hq.symm⟩

/-- The empty subspace has no singular simplices (ported from upstream's
`isEmpty_emptySubspacePair_simplices`, in `Other`). -/
lemma j5d_isEmpty_emptyPair_simplices (Y : TopCat.{0}) (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj (TopPair.ofSubset (X := Y) (∅ : Set Y)).snd).obj
      (Opposite.op (SimplexCategory.mk n))) := by
  constructor
  intro σ
  let f := ((TopPair.ofSubset (X := Y) (∅ : Set Y)).snd.toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n))) σ
  exact (f Convexity.StdSimplex.barycenter).2

/-- The chain map induced by `∅ ⊆ Y` is zero (ported from upstream's
`emptySubspacePair_chainMap_eq_zero`, in `Other`). -/
lemma j5d_emptyPair_chainMap_eq_zero (Y : TopCat.{0}) :
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := Y) (∅ : Set Y))).hom = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.ofSubset (X := Y) (∅ : Set Y)).map)
    (ModuleCat.of ℚ ℚ)).f n = 0
  apply SSet.chainComplex_hom_ext
  intro σ
  exact (j5d_isEmpty_emptyPair_simplices Y n).false σ |>.elim

theorem j5d_finrank_cohomology_eq_finrank_homology_aux (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of Y) n) =
      Module.finrank ℚ (RelativeHomology ℚ (TopPair.ofSubset
        (((⊤ : Opens Y) : Set Y)ᶜ : Set (TopCat.of Y))) n) := by
  have hP : (((⊤ : Opens Y) : Set Y)ᶜ : Set (TopCat.of Y)) = ∅ := by
    rw [Opens.coe_top, Set.compl_univ]
  rw [hP, (cohomologyEquivDualHomology ℚ (TopCat.of Y) n).finrank_eq, Subspace.dual_finrank_eq]
  have : IsIso (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of Y) (∅ : Set Y))) :=
    CategoryTheory.Limits.cokernel.π_of_zero (j5d_emptyPair_chainMap_eq_zero (TopCat.of Y))
  exact (HomologicalComplex.homologyMapIso
    (asIso (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of Y) (∅ : Set Y)))) n
    ).toLinearEquiv.finrank_eq

theorem j5d_finrank_HQ_top_aux (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    Module.finrank ℚ (HQ X (2 * d)) = 1 := by
  have (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  obtain ⟨e⟩ := HodgeLean.Foundations.spec_fieldCohomology_linearEquiv_singular ℚ X (2 * d)
  exact e.finrank_eq.trans ((j5d_finrank_cohomology_eq_finrank_homology_aux _ _).trans
    (j5d_finrank_complexTopHomology_aux hconn X d))

theorem j5d_finrank_HQ_two_aux (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] :
    Module.finrank ℚ (HQ X 2) = 1 :=
  j5d_finrank_HQ_top_aux hconn X 1

theorem j5d_algebraicCycleClassSpan_one_eq_top_aux (hconn : ComplexPointsPreconnected)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] :
    algebraicCycleClassSpan X 1 = ⊤ :=
  HodgeLean.Foundations.Curves.algebraicCycleClassSpan_one_eq_top X (j5d_finrank_HQ_two_aux hconn X)

theorem j5d_exists_linearIndependent_of_isClopen_aux {M E : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {n : ℕ} (hn : Module.finrank ℝ E = n)
    (μ : ∀ x : M, RelativeHomology ℚ (pointComplementPair x) n)
    (hμ : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) n,
        ∀ (y : M) (hy : y ∈ U),
          relativeHomologyMap ℚ n
            (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c = μ y)
    {S : Set M} (hS : IsClopen S) {x x' : M} (hx : x ∈ S) (hx' : x' ∉ S)
    (hμx : μ x ≠ 0) (hμx' : μ x' ≠ 0) :
    ∃ w₁ w₂ : RelativeHomology ℚ (TopPair.ofSubset
        (((⊤ : Opens M) : Set M)ᶜ : Set (TopCat.of M))) n,
      LinearIndependent ℚ ![w₁, w₂] := by
  classical
  have hcoh : ∀ T : Set M, IsClopen T → ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) (U : Set M)ᶜ) n,
        ∀ (y : M) (hy : y ∈ U),
          relativeHomologyMap ℚ n
            (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy)) c =
            if y ∈ T then μ y else 0 := by
    intro T hT x
    by_cases hxT : x ∈ T
    · obtain ⟨U, hxU, c, hc⟩ := hμ x
      let V : Opens M := U ⊓ ⟨T, hT.isOpen⟩
      have hVU : (V : Set M) ⊆ U := Set.inter_subset_left
      refine ⟨V, ⟨hxU, hxT⟩, relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of M) hVU) c, fun y hy => ?_⟩
      simp only [show y ∈ T from hy.2, ↓reduceIte]
      rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, ← supportInclusionPairMap_trans]
      exact hc y hy.1
    · refine ⟨⟨Tᶜ, hT.isClosed.isOpen_compl⟩, hxT, 0, fun y hy => ?_⟩
      simp only [map_zero, show y ∉ T from hy, ↓reduceIte]
  obtain ⟨w₁, hw₁⟩ := j5c_exists_fundamentalClass hn _ (hcoh S hS)
  obtain ⟨w₂, hw₂⟩ := j5c_exists_fundamentalClass hn _ (hcoh Sᶜ hS.compl)
  refine ⟨w₁, w₂, LinearIndependent.pair_iff.mpr fun s t hst => ?_⟩
  have hval := fun y : M => congrArg (relativeHomologyMap ℚ n
    (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr (Opens.mem_top y)))) hst
  have h1 := hval x
  have h2 := hval x'
  simp only [map_add, map_smul, map_zero, hw₁, hw₂, hx, hx', Set.mem_compl_iff, not_true_eq_false,
    not_false_eq_true, ↓reduceIte, smul_zero, add_zero, zero_add] at h1 h2
  exact ⟨(smul_eq_zero.mp h1).resolve_right hμx, (smul_eq_zero.mp h2).resolve_right hμx'⟩

/-- On the two-point space, the image of the standard class of `(ℝ⁰, ∅)` under the map of pairs
sending the point to `x` is nonzero in `H_0(M, M \ x; ℚ)`: excision to `({x}, ∅)` is injective, and
there the augmentation of the image is `1`. -/
theorem j5d_twoPoints_pointClass_ne_zero (x : (Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)) :
    relativeHomologyMap ℚ 0
      (TopPair.ofSubsetHom (X := TopCat.of (Fin 0 → ℝ)) (Y := TopCat.of ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))
        (A := ({0}ᶜ : Set (Fin 0 → ℝ))) (B := ({x}ᶜ : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))))
        (TopCat.ofHom ⟨fun _ => x, continuous_const⟩)
        (fun a ha => (ha (Subsingleton.elim a 0)).elim))
      (standardLocalClass ℚ 0) ≠ 0 := by
  have hexc := (j5c_excision (isOpen_discrete ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))))
    (isClosed_discrete ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))) subset_rfl 0).1
  let f : puncturedPair ℝ 0 ⟶ TopPair.ofSubset (X := TopCat.of ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))))
      {u : ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))) | u.1 ∉ ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))} :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨fun _ => ⟨x, rfl⟩, continuous_const⟩)
      (fun a ha => (ha (Subsingleton.elim a 0)).elim)
  have : IsIso (relativeChainProjection ℚ (TopPair.ofSubset (X := TopCat.of ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))))
      {u : ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))) | u.1 ∉ ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))})) :=
    isIso_relativeChainProjection _ ⟨fun u => u.2 u.1.2⟩
  have h1 : augmentationFunctional _ (relativeHomologyMap ℚ 0 f (standardLocalClass ℚ 0)) = 1 := by
    rw [augmentationFunctional_relativeHomologyMap]
    exact standardLocalClass_zero_epsilon
  intro h0
  rw [show relativeHomologyMap ℚ 0
      (TopPair.ofSubsetHom (X := TopCat.of (Fin 0 → ℝ)) (Y := TopCat.of ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))
        (A := ({0}ᶜ : Set (Fin 0 → ℝ))) (B := ({x}ᶜ : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))))
        (TopCat.ofHom ⟨fun _ => x, continuous_const⟩)
        (fun a ha => (ha (Subsingleton.elim a 0)).elim)) (standardLocalClass ℚ 0) =
      relativeHomologyMap ℚ 0
        (TopPair.ofSubsetHom (A := {u : ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))) | u.1 ∉ ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))})
          (B := ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))ᶜ)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
            TopCat.of ({x} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))) ⟶ TopCat.of ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))) (fun _ ha => ha))
        (relativeHomologyMap ℚ 0 f (standardLocalClass ℚ 0)) by
      rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]; rfl,
    ← map_zero (relativeHomologyMap ℚ 0 _)] at h0
  rw [hexc h0, map_zero] at h1
  exact zero_ne_one h1

theorem j5d_exists_locallyCoherent_ne_zero_twoPoints_aux :
    ∃ μ : ∀ x : (Fin 0 → ℝ) ⊕ (Fin 0 → ℝ), RelativeHomology ℚ (pointComplementPair x) 0,
      (∀ x : (Fin 0 → ℝ) ⊕ (Fin 0 → ℝ), ∃ U : Opens ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)), x ∈ U ∧
        ∃ c : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))
            (U : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))ᶜ) 0,
          ∀ (y : (Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)) (hy : y ∈ U),
            relativeHomologyMap ℚ 0
              (supportInclusionPairMap (TopCat.of ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))
                (Set.singleton_subset_iff.mpr hy)) c = μ y) ∧
      μ (Sum.inl 0) ≠ 0 ∧ μ (Sum.inr 0) ≠ 0 := by
  let μ : ∀ x : (Fin 0 → ℝ) ⊕ (Fin 0 → ℝ), RelativeHomology ℚ (pointComplementPair x) 0 := fun x =>
    relativeHomologyMap ℚ 0
      (TopPair.ofSubsetHom (X := TopCat.of (Fin 0 → ℝ)) (Y := TopCat.of ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ)))
        (A := ({0}ᶜ : Set (Fin 0 → ℝ))) (B := ({x}ᶜ : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))))
        (TopCat.ofHom ⟨fun _ => x, continuous_const⟩)
        (fun a ha => (ha (Subsingleton.elim a 0)).elim))
      (standardLocalClass ℚ 0)
  refine ⟨μ, fun x => ⟨⟨{x}, isOpen_discrete _⟩, rfl, μ x, fun y hy => ?_⟩,
    j5d_twoPoints_pointClass_ne_zero _, j5d_twoPoints_pointClass_ne_zero _⟩
  obtain rfl : y = x := hy
  change relativeHomologyMap ℚ 0
    (supportInclusionPairMap (TopCat.of ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))) (Set.Subset.rfl : ({y} : Set ((Fin 0 → ℝ) ⊕ (Fin 0 → ℝ))) ⊆ {y})) (μ y) =
      μ y
  rw [supportInclusionPairMap_rfl, relativeHomologyMap_id, LinearMap.id_apply]

theorem j5d_subsingleton_complexHomology_of_lt_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] {k : ℕ} (hk : 2 * d < k) :
    Subsingleton (RelativeHomology ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))) k) := by
  simpa [Opens.coe_top] using (j5c_compact_manifold (M := ComplexPoint X)
    (Foundations.finrank_real_complexCoordinates d) isCompact_univ).1 k hk

/-- The pair `(Y, Y \ Y)` has empty subspace, so its relative chain projection is an isomorphism. -/
theorem j5d_isIso_relativeChainProjection_compl_top (Y : Type) [TopologicalSpace Y] :
    IsIso (relativeChainProjection ℚ (TopPair.ofSubset
      (((⊤ : Opens Y) : Set Y)ᶜ : Set (TopCat.of Y)))) :=
  isIso_relativeChainProjection _ ⟨fun y => y.2 trivial⟩

theorem j5d_subsingleton_HQ_of_lt_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] {m : ℕ} (hm : 2 * d < m) :
    Subsingleton (HQ X m) := by
  have h10 := j5d_subsingleton_complexHomology_of_lt_aux X d hm
  have := j5d_isIso_relativeChainProjection_compl_top (ComplexPoint X)
  let e := (HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ (TopPair.ofSubset
      (((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ :
        Set (TopCat.of (ComplexPoint X)))))) m).toLinearEquiv
  have : Subsingleton (Homology ℚ (TopCat.of (ComplexPoint X)) m) :=
    e.toEquiv.subsingleton_congr.mpr h10
  have : Subsingleton (Cohomology ℚ (TopCat.of (ComplexPoint X)) m) :=
    (cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint X)) m).toEquiv.subsingleton
  have (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  obtain ⟨f⟩ := Foundations.spec_fieldCohomology_linearEquiv_singular ℚ X m
  rw [HQ_def]
  exact f.toEquiv.subsingleton

theorem j5d_vanishingAboveTop_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    VanishingAboveTop X :=
  ⟨fun _ hm => j5d_subsingleton_HQ_of_lt_aux X (dim X.left) hm⟩

end HodgeLean.RealDefs
