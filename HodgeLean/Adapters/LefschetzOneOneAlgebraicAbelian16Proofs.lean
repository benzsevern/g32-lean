import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian16Defs
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian15

/-! # Compatible cones and support vanishing

Implications from geometric sphere filling to compatible chains, and from a
codimension-two cover to support vanishing. Analytic singular restriction is a
frozen endpoint awaiting critical-cover integration. General nonnested
restriction requires additional local-support work.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology TopologicalSpace CategoryTheory AlgebraicTopology.Singular
open CategoryTheory.Limits
open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- Choose one path from the fixed vertex to every singular vertex.
Source: Hatcher, Algebraic Topology, §2.1; `bh14_simplex_extension` at dimension zero. -/
theorem bh16_vertex_cones_aux (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z) :
    ∃ s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1, ∀ σ,
      bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p := by
  let q : bh16_simplex (TopCat.of U) 0 → U := fun σ ↦
    (TopCat.toSSetObjEquiv (TopCat.of U) _ σ) default
  let B := {x : Convexity.StdSimplex ℝ (Fin 2) | ∃ i, x.weights i = 0}
  have hclopen : IsClopen {z : B | z.1.weights 0 = 0} := by
    constructor
    · exact isClosed_eq ((Convexity.StdSimplex.continuous_weights_apply ℝ 0).comp
        continuous_subtype_val) continuous_const
    · apply isClosed_compl_iff.mp
      have heq : ({z : B | z.1.weights 0 = 0} : Set B)ᶜ =
          {z : B | z.1.weights 1 = 0} := by
        ext z
        simp only [mem_compl_iff, mem_ofPred_eq]
        constructor
        · intro h
          obtain ⟨i, hi⟩ := z.2
          fin_cases i
          · exact (h hi).elim
          · exact hi
        · intro h1 h0
          have ht := Convexity.StdSimplex.total_fin_two z.1
          rw [h0, h1] at ht
          norm_num at ht
      rw [heq]
      exact isClosed_eq ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).comp
        continuous_subtype_val) continuous_const
  have hboundary (σ : bh16_simplex (TopCat.of U) 0) :
      Continuous (fun z : B ↦ if z.1.weights 0 = 0 then q σ else p) := by
    apply Continuous.if
    · intro z hz
      rw [hclopen.frontier_eq] at hz
      exact hz.elim
    · exact continuous_const
    · exact continuous_const
  choose v hv using fun σ ↦ bh14_simplex_extension n U ⟨p.1, p.2⟩ 0 (by omega)
    (hfill 0 (by omega))
    (⟨fun z : B ↦ if z.1.weights 0 = 0 then q σ else p, hboundary σ⟩ : C(B, U))
  refine ⟨fun σ ↦ (TopCat.toSSetObjEquiv (TopCat.of U) _).symm (v σ), ?_⟩
  intro σ
  constructor
  · apply (TopCat.toSSetObjEquiv (TopCat.of U) _).injective
    apply ContinuousMap.ext
    intro z
    unfold bh16_face
    rw [TopCat.toSSetObjEquiv_δ_apply]
    have hz : ∃ i, (Convexity.StdSimplex.map (0 : Fin 2).succAbove z).weights i = 0 := by
      refine ⟨0, ?_⟩
      simp [Finsupp.mapDomain_apply]
    rw [Equiv.apply_symm_apply, hv σ ⟨_, hz⟩]
    change (if (Convexity.StdSimplex.map (0 : Fin 2).succAbove z).weights 0 = 0
      then q σ else p) = _
    rw [Subsingleton.elim z (Convexity.StdSimplex.single 0),
      Convexity.StdSimplex.map_single]
    simp [q, show (default : Convexity.StdSimplex ℝ (Fin 1)) =
      Convexity.StdSimplex.single 0 from Subsingleton.elim _ _]
  · apply (TopCat.toSSetObjEquiv (TopCat.of U) _).injective
    apply ContinuousMap.ext
    intro z
    unfold bh16_face
    rw [TopCat.toSSetObjEquiv_δ_apply]
    have hz : ∃ i, (Convexity.StdSimplex.map (1 : Fin 2).succAbove z).weights i = 0 := by
      refine ⟨1, ?_⟩
      simp [Finsupp.mapDomain_apply]
    rw [Equiv.apply_symm_apply, hv σ ⟨_, hz⟩]
    change (if (Convexity.StdSimplex.map (1 : Fin 2).succAbove z).weights 0 = 0
      then q σ else p) = _
    rw [Subsingleton.elim z (Convexity.StdSimplex.single 0),
      Convexity.StdSimplex.map_single]
    simp [bh16_const]

private noncomputable def bh16_facePreimage {m : ℕ} (i : Fin (m + 1))
    (x : Convexity.StdSimplex ℝ (Fin (m + 1))) (hx : x.weights i = 0) :
    Convexity.StdSimplex ℝ (Fin m) where
  weights := x.weights.comapDomain i.succAboveEmb i.succAboveEmb.injective.injOn
  nonneg := by
    change ∀ j, 0 ≤ x.weights.comapDomain i.succAboveEmb _ j
    intro j
    simp only [Finsupp.comapDomain_apply]
    exact x.weights_nonneg _
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.comapDomain_apply]
    have h := x.total_of_fintype
    rw [Fin.sum_univ_succAbove x.weights i, hx, zero_add] at h
    exact h

private lemma bh16_map_facePreimage {m : ℕ} (i : Fin (m + 1))
    (x : Convexity.StdSimplex ℝ (Fin (m + 1))) (hx : x.weights i = 0) :
    Convexity.StdSimplex.map i.succAbove (bh16_facePreimage i x hx) = x := by
  ext j
  simp only [Convexity.StdSimplex.weights_map]
  change (Finsupp.mapDomain i.succAboveEmb (bh16_facePreimage i x hx).weights) j =
    x.weights j
  by_cases hji : j = i
  · subst j
    rw [Finsupp.mapDomain_of_notMem_image_support]
    · exact hx.symm
    · simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simpa only [Fin.coe_succAboveEmb, bh16_facePreimage, Finsupp.comapDomain_apply] using
      (Finsupp.mapDomain_apply_of_injective i.succAboveEmb.injective
        (bh16_facePreimage i x hx).weights k)

private lemma bh16_facePreimage_map {m : ℕ} (i : Fin (m + 1))
    (z : Convexity.StdSimplex ℝ (Fin m))
    (hz : (Convexity.StdSimplex.map i.succAbove z).weights i = 0) :
    bh16_facePreimage i (Convexity.StdSimplex.map i.succAbove z) hz = z := by
  ext k
  simp only [bh16_facePreimage, Finsupp.comapDomain_apply,
    Convexity.StdSimplex.weights_map, Fin.coe_succAboveEmb]
  simpa only [Fin.coe_succAboveEmb] using
    (Finsupp.mapDomain_apply_of_injective i.succAboveEmb.injective z.weights k)

private lemma bh16_continuous_facePreimage {m : ℕ} (i : Fin (m + 1)) :
    Continuous (fun x : {x : Convexity.StdSimplex ℝ (Fin (m + 1)) |
        x.weights i = 0} ↦ bh16_facePreimage i x.1 x.2) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin m)).eq_induced]
  apply continuous_induced_rng.mpr
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun x : {x : Convexity.StdSimplex ℝ (Fin (m + 1)) |
      x.weights i = 0} ↦ x.1.weights (i.succAbove j))
  exact Continuous.comp
    (g := fun t : Convexity.StdSimplex ℝ (Fin (m + 1)) ↦ t.weights (i.succAbove j))
    (f := Subtype.val)
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) (i.succAbove j))
    continuous_subtype_val

private lemma bh16_simplex_eval_single_eq_face (X : TopCat)
    (τ : bh16_simplex X 1) (i : Fin 2) :
    (X.toSSetObjEquiv _ τ) (Convexity.StdSimplex.single (i.succAbove 0)) =
      (X.toSSetObjEquiv _ (bh16_face X 0 i τ))
        (Convexity.StdSimplex.single (R := ℝ) 0) := by
  have hz : Convexity.StdSimplex.map i.succAbove
      (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1)) =
        Convexity.StdSimplex.single (i.succAbove 0) := by
    simp
  rw [← hz]
  exact (TopCat.toSSetObjEquiv_δ_apply τ i _).symm

private lemma bh16_simplex_eval_one_eq_face_zero (X : TopCat) (τ : bh16_simplex X 1) :
    (X.toSSetObjEquiv _ τ) (Convexity.StdSimplex.single (R := ℝ) (1 : Fin 2)) =
      (X.toSSetObjEquiv _ (bh16_face X 0 0 τ))
        (Convexity.StdSimplex.single (R := ℝ) 0) := by
  simpa [Fin.ext_iff, Fin.succAbove] using bh16_simplex_eval_single_eq_face X τ 0

private lemma bh16_simplex_eval_zero_eq_face_one (X : TopCat) (τ : bh16_simplex X 1) :
    (X.toSSetObjEquiv _ τ) (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 2)) =
      (X.toSSetObjEquiv _ (bh16_face X 0 1 τ))
        (Convexity.StdSimplex.single (R := ℝ) 0) := by
  simpa [Fin.ext_iff, Fin.succAbove] using bh16_simplex_eval_single_eq_face X τ 1

private lemma bh16_facePreimage_eq_single (i : Fin 3) (q : Fin 2)
    (x : Convexity.StdSimplex ℝ (Fin 3)) (hi : x.weights i = 0)
    (hq : x.weights (i.succAbove q) = 0) :
    bh16_facePreimage i x hi =
      Convexity.StdSimplex.single (q.succAbove (0 : Fin 1)) := by
  ext k
  fin_cases i <;> fin_cases q <;> fin_cases k <;>
    simp only [bh16_facePreimage, Finsupp.comapDomain_apply,
      Convexity.StdSimplex.weights_single, Finsupp.single_apply] at * <;>
    have ht := x.total_of_fintype <;>
    simp only [Fin.sum_univ_three] at ht <;>
    norm_num [Fin.ext_iff, Fin.succAbove] at * <;> linarith

/-- Extend the already chosen vertex paths over each triangular boundary.
Source: Hatcher, Algebraic Topology, §2.1; `bh14_simplex_extension` at dimension one. -/
theorem bh16_edge_cones_aux (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z)
    (s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1) (h₀ : ∀ σ, bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p) :
    ∃ s₁ : bh16_simplex (TopCat.of U) 1 → bh16_simplex (TopCat.of U) 2, ∀ σ,
      bh16_face (TopCat.of U) 1 0 (s₁ σ) = σ ∧
      ∀ i : Fin 2, bh16_face (TopCat.of U) 1 i.succ (s₁ σ) = s₀ (bh16_face (TopCat.of U) 0 i (σ)) := by
  let X := TopCat.of U
  have hne : (U : Set (Fin n → ℂ)).Nonempty := ⟨p.1, p.2⟩
  let edges : bh16_simplex X 1 → Fin 3 → bh16_simplex X 1 := fun σ i ↦
    Fin.cases σ (fun j ↦ s₀ (bh16_face X 0 j σ)) i
  let edgeMap : bh16_simplex X 1 → Fin 3 →
      C(Convexity.StdSimplex ℝ (Fin 2), U) := fun σ i ↦ X.toSSetObjEquiv _ (edges σ i)
  let faceMap : bh16_simplex X 1 → (i : Fin 3) →
      C({x : Convexity.StdSimplex ℝ (Fin 3) | x.weights i = 0}, U) := fun σ i ↦
    (edgeMap σ i).comp ⟨fun x ↦ bh16_facePreimage i x.1 x.2,
      bh16_continuous_facePreimage i⟩
  have hcompat (σ : bh16_simplex X 1) (i j : Fin 3)
      (x : Convexity.StdSimplex ℝ (Fin 3)) (hi : x.weights i = 0)
      (hj : x.weights j = 0) : faceMap σ i ⟨x, hi⟩ = faceMap σ j ⟨x, hj⟩ := by
    fin_cases i <;> fin_cases j
    · rfl
    · dsimp [faceMap, edgeMap, edges]
      rw [show bh16_facePreimage 0 x hi = Convexity.StdSimplex.single (1 : Fin 2) by
          exact bh16_facePreimage_eq_single 0 0 x hi hj,
        show bh16_facePreimage 1 x hj = Convexity.StdSimplex.single (1 : Fin 2) by
          exact bh16_facePreimage_eq_single 1 0 x hj hi]
      change (X.toSSetObjEquiv _ σ) _ = (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 0 σ))) _
      rw [bh16_simplex_eval_one_eq_face_zero X σ,
        bh16_simplex_eval_one_eq_face_zero X (s₀ (bh16_face X 0 0 σ)),
        (h₀ (bh16_face X 0 0 σ)).1]
    · dsimp [faceMap, edgeMap, edges]
      rw [show bh16_facePreimage 0 x hi = Convexity.StdSimplex.single (0 : Fin 2) by
          exact bh16_facePreimage_eq_single 0 1 x hi hj,
        show bh16_facePreimage 2 x hj = Convexity.StdSimplex.single (1 : Fin 2) by
          exact bh16_facePreimage_eq_single 2 0 x hj hi]
      change (X.toSSetObjEquiv _ σ) _ = (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 1 σ))) _
      rw [bh16_simplex_eval_zero_eq_face_one X σ,
        bh16_simplex_eval_one_eq_face_zero X (s₀ (bh16_face X 0 1 σ)),
        (h₀ (bh16_face X 0 1 σ)).1]
    · symm
      dsimp [faceMap, edgeMap, edges]
      rw [show bh16_facePreimage 0 x hj = Convexity.StdSimplex.single (1 : Fin 2) by
          exact bh16_facePreimage_eq_single 0 0 x hj hi,
        show bh16_facePreimage 1 x hi = Convexity.StdSimplex.single (1 : Fin 2) by
          exact bh16_facePreimage_eq_single 1 0 x hi hj]
      change (X.toSSetObjEquiv _ σ) _ = (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 0 σ))) _
      rw [bh16_simplex_eval_one_eq_face_zero X σ,
        bh16_simplex_eval_one_eq_face_zero X (s₀ (bh16_face X 0 0 σ)),
        (h₀ (bh16_face X 0 0 σ)).1]
    · rfl
    · dsimp [faceMap, edgeMap, edges]
      rw [show bh16_facePreimage 1 x hi = Convexity.StdSimplex.single (0 : Fin 2) by
          exact bh16_facePreimage_eq_single 1 1 x hi hj,
        show bh16_facePreimage 2 x hj = Convexity.StdSimplex.single (0 : Fin 2) by
          exact bh16_facePreimage_eq_single 2 1 x hj hi]
      change (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 0 σ))) _ =
        (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 1 σ))) _
      rw [bh16_simplex_eval_zero_eq_face_one X (s₀ (bh16_face X 0 0 σ)),
        bh16_simplex_eval_zero_eq_face_one X (s₀ (bh16_face X 0 1 σ)),
        (h₀ (bh16_face X 0 0 σ)).2, (h₀ (bh16_face X 0 1 σ)).2]
    · symm
      dsimp [faceMap, edgeMap, edges]
      rw [show bh16_facePreimage 0 x hj = Convexity.StdSimplex.single (0 : Fin 2) by
          exact bh16_facePreimage_eq_single 0 1 x hj hi,
        show bh16_facePreimage 2 x hi = Convexity.StdSimplex.single (1 : Fin 2) by
          exact bh16_facePreimage_eq_single 2 0 x hi hj]
      change (X.toSSetObjEquiv _ σ) _ = (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 1 σ))) _
      rw [bh16_simplex_eval_zero_eq_face_one X σ,
        bh16_simplex_eval_one_eq_face_zero X (s₀ (bh16_face X 0 1 σ)),
        (h₀ (bh16_face X 0 1 σ)).1]
    · symm
      dsimp [faceMap, edgeMap, edges]
      rw [show bh16_facePreimage 1 x hj = Convexity.StdSimplex.single (0 : Fin 2) by
          exact bh16_facePreimage_eq_single 1 1 x hj hi,
        show bh16_facePreimage 2 x hi = Convexity.StdSimplex.single (0 : Fin 2) by
          exact bh16_facePreimage_eq_single 2 1 x hi hj]
      change (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 0 σ))) _ =
        (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 1 σ))) _
      rw [bh16_simplex_eval_zero_eq_face_one X (s₀ (bh16_face X 0 0 σ)),
        bh16_simplex_eval_zero_eq_face_one X (s₀ (bh16_face X 0 1 σ)),
        (h₀ (bh16_face X 0 0 σ)).2, (h₀ (bh16_face X 0 1 σ)).2]
    · rfl
  let boundary : Set (Convexity.StdSimplex ℝ (Fin 3)) :=
    {x | ∃ i, x.weights i = 0}
  let faceSet (i : Fin 3) : Set boundary := {z | z.1.weights i = 0}
  let chosenFace (z : boundary) : Fin 3 := Classical.choose z.2
  have chosenFace_spec (z : boundary) : z.1.weights (chosenFace z) = 0 :=
    Classical.choose_spec z.2
  let boundaryMap (σ : bh16_simplex X 1) (z : boundary) : U :=
    faceMap σ (chosenFace z) ⟨z.1, chosenFace_spec z⟩
  have boundaryMap_eq (σ : bh16_simplex X 1) (i : Fin 3) (z : boundary)
      (hz : z ∈ faceSet i) : boundaryMap σ z = faceMap σ i ⟨z.1, hz⟩ :=
    hcompat σ (chosenFace z) i z.1 (chosenFace_spec z) hz
  have boundaryMap_continuous (σ : bh16_simplex X 1) : Continuous (boundaryMap σ) := by
    apply (locallyFinite_of_finite faceSet).continuous
    · ext z
      simp only [mem_iUnion, mem_univ, iff_true, faceSet]
      exact z.2
    · intro i
      exact isClosed_singleton.preimage
        ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp continuous_subtype_val)
    · intro i
      rw [continuousOn_iff_continuous_restrict]
      have hc : Continuous (fun z : faceSet i ↦ faceMap σ i ⟨z.1.1, z.2⟩) := by fun_prop
      exact hc.congr (fun z ↦ (boundaryMap_eq σ i z.1 z.2).symm)
  choose filler hfiller using fun σ ↦ bh14_simplex_extension n U hne 1 (by omega)
    (hfill 1 (by omega)) ⟨boundaryMap σ, boundaryMap_continuous σ⟩
  refine ⟨fun σ ↦ (X.toSSetObjEquiv _).symm (filler σ), fun σ ↦ ?_⟩
  constructor
  · apply (X.toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro z
    change (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ 0
      ((X.toSSetObjEquiv _).symm (filler σ)))) z = (X.toSSetObjEquiv _ σ) z
    rw [TopCat.toSSetObjEquiv_δ_apply, Equiv.apply_symm_apply]
    have hz0 : (Convexity.StdSimplex.map (0 : Fin 3).succAbove z).weights 0 = 0 := by
      rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_image_support]
      simp [Fin.range_succAbove]
    let w : boundary := ⟨Convexity.StdSimplex.map (0 : Fin 3).succAbove z, ⟨0, hz0⟩⟩
    rw [show (filler σ) w.1 = boundaryMap σ w by exact hfiller σ w]
    rw [boundaryMap_eq σ 0 w (by exact hz0)]
    dsimp [faceMap, edgeMap, edges, w]
    congr 1
    exact bh16_facePreimage_map 0 z _
  · intro i
    apply (X.toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro z
    change (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i.succ
      ((X.toSSetObjEquiv _).symm (filler σ)))) z =
        (X.toSSetObjEquiv _ (s₀ (bh16_face X 0 i σ))) z
    rw [TopCat.toSSetObjEquiv_δ_apply, Equiv.apply_symm_apply]
    have hz0 : (Convexity.StdSimplex.map i.succ.succAbove z).weights i.succ = 0 := by
      rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_of_notMem_image_support]
      simp [Fin.range_succAbove]
    let w : boundary :=
      ⟨Convexity.StdSimplex.map i.succ.succAbove z, ⟨i.succ, hz0⟩⟩
    rw [show (filler σ) w.1 = boundaryMap σ w by exact hfiller σ w]
    rw [boundaryMap_eq σ i.succ w (by exact hz0)]
    dsimp [faceMap, edgeMap, edges, w]
    congr 1
    exact bh16_facePreimage_map i.succ z _

private noncomputable def bh16_deleteZero {m : ℕ} (i : Fin (m + 1))
    (z : Convexity.StdSimplex ℝ (Fin (m + 1))) (hz : z.weights i = 0) :
    Convexity.StdSimplex ℝ (Fin m) where
  weights := Finsupp.equivFunOnFinite.symm (fun j ↦ z.weights (i.succAbove j))
  nonneg := fun j ↦ z.nonneg _
  total := by
    rw [Finsupp.sum_fintype]
    simp_rw [Finsupp.coe_equivFunOnFinite_symm]
    have h := Fin.sum_univ_succAbove (fun j ↦ z.weights j) i
    have htotal : (∑ j, z.weights j) = 1 := by
      simpa [Finsupp.sum_fintype] using z.total
    rw [htotal, hz, zero_add] at h
    exact h.symm
    all_goals simp

private lemma bh16_map_deleteZero {m : ℕ} (i : Fin (m + 1))
    (z : Convexity.StdSimplex ℝ (Fin (m + 1))) (hz : z.weights i = 0) :
    Convexity.StdSimplex.map i.succAbove (bh16_deleteZero i z hz) = z := by
  ext j
  rw [Convexity.StdSimplex.weights_map]
  by_cases hj : j = i
  · subst j
    rw [hz]
    simp [Finsupp.mapDomain_apply, Fin.exists_succAbove_eq_iff]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [Finsupp.mapDomain_apply, bh16_deleteZero, Fin.succAbove_right_injective]

private lemma bh16_deleteZero_map {m : ℕ} (i : Fin (m + 1))
    (z : Convexity.StdSimplex ℝ (Fin m))
    (hz : (Convexity.StdSimplex.map i.succAbove z).weights i = 0) :
    bh16_deleteZero i (Convexity.StdSimplex.map i.succAbove z) hz = z := by
  ext j
  simp only [bh16_deleteZero, Finsupp.coe_equivFunOnFinite_symm,
    Convexity.StdSimplex.weights_map]
  rw [Finsupp.mapDomain_apply_of_injective (f := i.succAbove)
    (fun _ _ h ↦ Fin.succAbove_right_injective h)]

private noncomputable def bh16_triangleFace {X : TopCat.{0}}
    (s₁ : bh16_simplex X 1 → bh16_simplex X 2)
    (σ : bh16_simplex X 2) (i : Fin 4) : bh16_simplex X 2 :=
  if hi : i = 0 then σ else s₁ (bh16_face X 1 (i.pred hi) σ)

private lemma bh16_triangleFace_zero {X : TopCat.{0}}
    (s₁ : bh16_simplex X 1 → bh16_simplex X 2) (σ : bh16_simplex X 2) :
    bh16_triangleFace s₁ σ 0 = σ := by simp [bh16_triangleFace]

private lemma bh16_triangleFace_succ {X : TopCat.{0}}
    (s₁ : bh16_simplex X 1 → bh16_simplex X 2) (σ : bh16_simplex X 2) (i : Fin 3) :
    bh16_triangleFace s₁ σ i.succ = s₁ (bh16_face X 1 i σ) := by
  simp [bh16_triangleFace]

private lemma bh16_triangleFace_overlap {X : TopCat.{0}}
    (p : X)
    (s₀ : bh16_simplex X 0 → bh16_simplex X 1)
    (s₁ : bh16_simplex X 1 → bh16_simplex X 2)
    (h₀ : ∀ τ, bh16_face X 0 0 (s₀ τ) = τ ∧
      bh16_face X 0 1 (s₀ τ) = bh16_const X 0 p)
    (h₁ : ∀ τ, bh16_face X 1 0 (s₁ τ) = τ ∧
      ∀ i : Fin 2, bh16_face X 1 i.succ (s₁ τ) = s₀ (bh16_face X 0 i τ))
    (σ : bh16_simplex X 2) (i j : Fin 4) (hij : i < j) :
    bh16_face X 1 (j.pred hij.ne_zero) (bh16_triangleFace s₁ σ i) =
      bh16_face X 1 (i.castPred (Fin.ne_last_of_lt hij)) (bh16_triangleFace s₁ σ j) := by
  fin_cases i <;> fin_cases j
  all_goals first | omega | norm_num at hij
  all_goals simp_all [bh16_triangleFace, bh16_face]
  case «1».«2» =>
    exact congrArg s₀ ((TopCat.toSSet.obj X).δ_comp_δ_self_apply (i := (0 : Fin 2)) σ)
  case «1».«3» =>
    exact congrArg s₀ ((TopCat.toSSet.obj X).δ_comp_δ_apply (i := (0 : Fin 2))
      (j := (1 : Fin 2)) (by decide) σ).symm
  case «2».«3» =>
    rw [show Fin.castPred (2 : Fin 4) (by decide) = (2 : Fin 3) by rfl, (h₁ _).2.2]
    exact congrArg s₀ ((TopCat.toSSet.obj X).δ_comp_δ_self_apply (i := (1 : Fin 2)) σ)

set_option maxHeartbeats 400000 in
private lemma bh16_triangleFace_value_overlap {X : TopCat.{0}}
    (p : X) (s₀ : bh16_simplex X 0 → bh16_simplex X 1)
    (s₁ : bh16_simplex X 1 → bh16_simplex X 2)
    (h₀ : ∀ τ, bh16_face X 0 0 (s₀ τ) = τ ∧
      bh16_face X 0 1 (s₀ τ) = bh16_const X 0 p)
    (h₁ : ∀ τ, bh16_face X 1 0 (s₁ τ) = τ ∧
      ∀ i : Fin 2, bh16_face X 1 i.succ (s₁ τ) = s₀ (bh16_face X 0 i τ))
    (σ : bh16_simplex X 2) (z : Convexity.StdSimplex ℝ (Fin 4))
    (i j : Fin 4) (hi : z.weights i = 0) (hj : z.weights j = 0) :
    (TopCat.toSSetObjEquiv X _ (bh16_triangleFace s₁ σ i)) (bh16_deleteZero i z hi) =
      (TopCat.toSSetObjEquiv X _ (bh16_triangleFace s₁ σ j)) (bh16_deleteZero j z hj) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · let zi := bh16_deleteZero i z hi
    have hzij : zi.weights (j.pred hij.ne_zero) = 0 := by
      simp only [zi, bh16_deleteZero, Finsupp.coe_equivFunOnFinite_symm]
      rw [Fin.succAbove_pred_of_lt i j hij, hj]
    let w := bh16_deleteZero (j.pred hij.ne_zero) zi hzij
    have hleft : Convexity.StdSimplex.map (j.pred hij.ne_zero).succAbove w = zi :=
      bh16_map_deleteZero _ _ _
    have hright : Convexity.StdSimplex.map (i.castPred (Fin.ne_last_of_lt hij)).succAbove w =
        bh16_deleteZero j z hj := by
      ext k
      by_cases hk : k = i.castPred (Fin.ne_last_of_lt hij)
      · subst k
        simp [Convexity.StdSimplex.weights_map, w, zi, bh16_deleteZero,
          Finsupp.mapDomain_apply, Fin.succAbove_castPred_of_lt _ _ hij, hi]
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
        simp only [Convexity.StdSimplex.weights_map]
        rw [Finsupp.mapDomain_apply_of_injective
          (f := (i.castPred (Fin.ne_last_of_lt hij)).succAbove)
          (fun _ _ h ↦ Fin.succAbove_right_injective h)]
        simp only [w, zi, bh16_deleteZero, Finsupp.coe_equivFunOnFinite_symm]
        have hh : Fin.castSucc (i.castPred (Fin.ne_last_of_lt hij)) < j := by
          simpa using hij
        exact congrArg z.weights (SimplexCategory.congr_toOrderHom_apply
          (SimplexCategory.δ_comp_δ' hh) l).symm
    have he := congrArg (fun τ ↦ (TopCat.toSSetObjEquiv X _ τ) w)
      (bh16_triangleFace_overlap p s₀ s₁ h₀ h₁ σ i j hij)
    change (TopCat.toSSetObjEquiv X _ (bh16_triangleFace s₁ σ i)) zi =
      (TopCat.toSSetObjEquiv X _ (bh16_triangleFace s₁ σ j)) (bh16_deleteZero j z hj)
    rw [← hleft, ← hright]
    simpa only [bh16_face, TopCat.toSSetObjEquiv_δ_apply] using he
  · rfl
  · let zj := bh16_deleteZero j z hj
    have hzji : zj.weights (i.pred hji.ne_zero) = 0 := by
      simp only [zj, bh16_deleteZero, Finsupp.coe_equivFunOnFinite_symm]
      rw [Fin.succAbove_pred_of_lt j i hji, hi]
    let w := bh16_deleteZero (i.pred hji.ne_zero) zj hzji
    have hleft : Convexity.StdSimplex.map (j.castPred (Fin.ne_last_of_lt hji)).succAbove w =
        bh16_deleteZero i z hi := by
      ext k
      by_cases hk : k = j.castPred (Fin.ne_last_of_lt hji)
      · subst k
        simp [Convexity.StdSimplex.weights_map, w, zj, bh16_deleteZero,
          Finsupp.mapDomain_apply, Fin.succAbove_castPred_of_lt _ _ hji, hj]
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
        simp only [Convexity.StdSimplex.weights_map]
        rw [Finsupp.mapDomain_apply_of_injective
          (f := (j.castPred (Fin.ne_last_of_lt hji)).succAbove)
          (fun _ _ h ↦ Fin.succAbove_right_injective h)]
        simp only [w, zj, bh16_deleteZero, Finsupp.coe_equivFunOnFinite_symm]
        have hh : Fin.castSucc (j.castPred (Fin.ne_last_of_lt hji)) < i := by
          simpa using hji
        exact congrArg z.weights (SimplexCategory.congr_toOrderHom_apply
          (SimplexCategory.δ_comp_δ' hh) l).symm
    have hright : Convexity.StdSimplex.map (i.pred hji.ne_zero).succAbove w = zj :=
      bh16_map_deleteZero _ _ _
    have he := congrArg (fun τ ↦ (TopCat.toSSetObjEquiv X _ τ) w)
      (bh16_triangleFace_overlap p s₀ s₁ h₀ h₁ σ j i hji)
    change (TopCat.toSSetObjEquiv X _ (bh16_triangleFace s₁ σ i))
      (bh16_deleteZero i z hi) = (TopCat.toSSetObjEquiv X _ (bh16_triangleFace s₁ σ j)) zj
    rw [← hleft, ← hright]
    simpa only [bh16_face, TopCat.toSSetObjEquiv_δ_apply] using he.symm

private lemma bh16_continuous_deleteZero (i : Fin 4) :
    Continuous (fun z : {z : Convexity.StdSimplex ℝ (Fin 4) | z.weights i = 0} ↦
      bh16_deleteZero i z.1 z.2) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  apply continuous_pi
  intro j
  change Continuous (fun z : {z : Convexity.StdSimplex ℝ (Fin 4) | z.weights i = 0} ↦
    z.1.weights (i.succAbove j))
  exact (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 4)
    (i.succAbove j)).comp continuous_subtype_val

/-- Extend the compatible edge cones over each tetrahedral boundary.
Source: Hatcher, Algebraic Topology, §2.1; `bh14_simplex_extension` at dimension two. -/
theorem bh16_triangle_cones_aux (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z)
    (s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1) (h₀ : ∀ σ, bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p)
    (s₁ : bh16_simplex (TopCat.of U) 1 → bh16_simplex (TopCat.of U) 2) (h₁ : ∀ σ, bh16_face (TopCat.of U) 1 0 (s₁ σ) = σ ∧
      ∀ i : Fin 2, bh16_face (TopCat.of U) 1 i.succ (s₁ σ) = s₀ (bh16_face (TopCat.of U) 0 i (σ))) :
    ∃ s₂ : bh16_simplex (TopCat.of U) 2 → bh16_simplex (TopCat.of U) 3, ∀ σ,
      bh16_face (TopCat.of U) 2 0 (s₂ σ) = σ ∧
      ∀ i : Fin 3, bh16_face (TopCat.of U) 2 i.succ (s₂ σ) = s₁ (bh16_face (TopCat.of U) 1 i (σ)) := by
  classical
  let B := {x : Convexity.StdSimplex ℝ (Fin 4) | ∃ i, x.weights i = 0}
  let A : Fin 4 → Set B := fun i ↦ {z | z.1.weights i = 0}
  let q : B → Fin 4 := fun z ↦ z.property.choose
  have hq (z : B) : z.1.weights (q z) = 0 := z.property.choose_spec
  let faceValue (σ : bh16_simplex (TopCat.of U) 2) (i : Fin 4) (z : B)
      (hz : z.1.weights i = 0) : U :=
    (TopCat.toSSetObjEquiv (TopCat.of U) _ (bh16_triangleFace s₁ σ i))
      (bh16_deleteZero i z.1 hz)
  let boundaryValue (σ : bh16_simplex (TopCat.of U) 2) : B → U :=
    fun z ↦ faceValue σ (q z) z (hq z)
  have hface (σ : bh16_simplex (TopCat.of U) 2) (i : Fin 4) (z : B) (hz : z ∈ A i) :
      boundaryValue σ z = faceValue σ i z hz := by
    exact bh16_triangleFace_value_overlap p s₀ s₁ h₀ h₁ σ z.1
      (q z) i (hq z) hz
  have hAclosed (i : Fin 4) : IsClosed (A i) := by
    dsimp only [A]
    exact isClosed_eq
      (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) (M := Fin 4) i |>.comp
        continuous_subtype_val) continuous_const
  have hpiece (σ : bh16_simplex (TopCat.of U) 2) (i : Fin 4) :
      Continuous (fun z : A i ↦ faceValue σ i z.1 z.2) := by
    dsimp only [faceValue]
    have hc : Continuous (fun z : A i ↦
        (⟨z.1.1, z.2⟩ : {x : Convexity.StdSimplex ℝ (Fin 4) | x.weights i = 0})) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (TopCat.toSSetObjEquiv (TopCat.of U) _ (bh16_triangleFace s₁ σ i)).continuous.comp
      (bh16_continuous_deleteZero i |>.comp hc)
  have hboundary (σ : bh16_simplex (TopCat.of U) 2) : Continuous (boundaryValue σ) := by
    apply (locallyFinite_of_finite A).continuous
    · ext z
      simp only [mem_iUnion, mem_univ, iff_true]
      exact ⟨q z, hq z⟩
    · exact hAclosed
    · intro i
      rw [continuousOn_iff_continuous_restrict]
      convert hpiece σ i using 1
      funext z
      exact hface σ i z.1 z.2
  let boundary (σ : bh16_simplex (TopCat.of U) 2) : C(B, U) :=
    ⟨boundaryValue σ, hboundary σ⟩
  have hne : (U : Set (Fin n → ℂ)).Nonempty := ⟨p, p.2⟩
  choose fill hfill_boundary using fun σ : bh16_simplex (TopCat.of U) 2 ↦
    bh14_simplex_extension n U hne 2 (by omega) (hfill 2 (by omega))
      (by simpa only [B] using boundary σ)
  let s₂ : bh16_simplex (TopCat.of U) 2 → bh16_simplex (TopCat.of U) 3 :=
    fun σ ↦ (TopCat.toSSetObjEquiv (TopCat.of U) _).symm (fill σ)
  refine ⟨s₂, fun σ ↦ ⟨?_, ?_⟩⟩
  · apply (TopCat.toSSetObjEquiv (TopCat.of U) _).injective
    apply ContinuousMap.ext
    intro z
    have hz : (Convexity.StdSimplex.map (0 : Fin 4).succAbove z).weights 0 = 0 := by
      simp [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_apply]
    let bz : B := ⟨Convexity.StdSimplex.map (0 : Fin 4).succAbove z, 0, hz⟩
    calc
      _ = fill σ (Convexity.StdSimplex.map (0 : Fin 4).succAbove z) := rfl
      _ = boundaryValue σ bz := hfill_boundary σ bz
      _ = faceValue σ 0 bz hz := hface σ 0 bz hz
      _ = _ := by
        simp only [faceValue, bz, bh16_triangleFace_zero]
        rw [bh16_deleteZero_map]
  · intro i
    apply (TopCat.toSSetObjEquiv (TopCat.of U) _).injective
    apply ContinuousMap.ext
    intro z
    have hz : (Convexity.StdSimplex.map i.succ.succAbove z).weights i.succ = 0 := by
      simp [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_apply]
    let bz : B := ⟨Convexity.StdSimplex.map i.succ.succAbove z, i.succ, hz⟩
    calc
      _ = fill σ (Convexity.StdSimplex.map i.succ.succAbove z) := rfl
      _ = boundaryValue σ bz := hfill_boundary σ bz
      _ = faceValue σ i.succ bz hz := hface σ i.succ bz hz
      _ = _ := by simp [faceValue, bz, bh16_triangleFace, bh16_deleteZero_map]

/-- Linear extension of coherent simplex cones satisfies the chain homotopy identity.
Source: Hatcher, Algebraic Topology, §2.1 and §2.A; `SSet.ιChainComplex_d`. -/
theorem bh16_cone_identity_aux (n : ℕ) (U : Opens (Fin n → ℂ))
    (p : U) (s₀ : bh16_simplex (TopCat.of U) 0 → bh16_simplex (TopCat.of U) 1) (h₀ : ∀ σ, bh16_face (TopCat.of U) 0 0 (s₀ σ) = σ ∧
      bh16_face (TopCat.of U) 0 1 (s₀ σ) = bh16_const (TopCat.of U) 0 p) (s₁ : bh16_simplex (TopCat.of U) 1 → bh16_simplex (TopCat.of U) 2) (h₁ : ∀ σ, bh16_face (TopCat.of U) 1 0 (s₁ σ) = σ ∧
      ∀ i : Fin 2, bh16_face (TopCat.of U) 1 i.succ (s₁ σ) = s₀ (bh16_face (TopCat.of U) 0 i (σ))) (s₂ : bh16_simplex (TopCat.of U) 2 → bh16_simplex (TopCat.of U) 3) (h₂ : ∀ σ, bh16_face (TopCat.of U) 2 0 (s₂ σ) = σ ∧
      ∀ i : Fin 3, bh16_face (TopCat.of U) 2 i.succ (s₂ σ) = s₁ (bh16_face (TopCat.of U) 1 i (σ))) :
    (∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 0, ((SingularChainComplex ℚ (TopCat.of U)).d 1 0).hom (bh16_linearCone (TopCat.of U) 0 s₀ c) +
      bh16_generator (TopCat.of U) 0 (bh16_const (TopCat.of U) 0 p) (bh16_augmentation (TopCat.of U) c) = c) ∧
    (∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 1,
      ((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom (bh16_linearCone (TopCat.of U) 1 s₁ c) +
        bh16_linearCone (TopCat.of U) 0 s₀ (((SingularChainComplex ℚ (TopCat.of U)).d 1 0).hom c) = c) ∧
    (∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 2,
      ((SingularChainComplex ℚ (TopCat.of U)).d 3 2).hom (bh16_linearCone (TopCat.of U) 2 s₂ c) +
        bh16_linearCone (TopCat.of U) 1 s₁ (((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom c) = c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    let f := ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 0 s₀) ≫
        (SingularChainComplex ℚ (TopCat.of U)).d 1 0 +
      ModuleCat.ofHom (bh16_augmentation (TopCat.of U)) ≫
        ModuleCat.ofHom (bh16_generator (TopCat.of U) 0 (bh16_const (TopCat.of U) 0 p))
    have hf : f = 𝟙 _ := by
      apply SSet.chainComplex_hom_ext
      intro σ
      dsimp [f]
      erw [CategoryTheory.Preadditive.comp_add]
      have hs : (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
          ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 0 s₀) =
          (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s₀ σ) := by
        change (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
          CategoryTheory.Limits.Sigma.desc (fun τ ↦
            (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s₀ τ)) = _
        simp [CategoryTheory.Limits.Sigma.desc, CategoryTheory.Limits.Sigma.ι,
          SSet.ιChainComplex]
      erw [← Category.assoc, hs, SSet.ιChainComplex_d]
      have h00 := (h₀ σ).1
      have h01 := (h₀ σ).2
      simp only [bh16_face] at h00 h01
      have ha : (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
          ModuleCat.ofHom (bh16_augmentation (TopCat.of U)) = 𝟙 _ := by
        change (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex σ ≫
          CategoryTheory.Limits.Sigma.desc (fun _ ↦ 𝟙 (ModuleCat.of ℚ ℚ)) = _
        simp [CategoryTheory.Limits.Sigma.desc, CategoryTheory.Limits.Sigma.ι,
          SSet.ιChainComplex]
      simp only [Fin.sum_univ_succ]
      simp [h00, h01]
      erw [← Category.assoc, ha]
      dsimp [bh16_generator]
      erw [ModuleCat.ofHom_hom, Category.comp_id]
      erw [Category.id_comp]
      abel
    change f.hom c = c
    simpa using ConcreteCategory.congr_hom hf c
  · intro c
    let f := ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 1 s₁) ≫
        (SingularChainComplex ℚ (TopCat.of U)).d 2 1 +
      (SingularChainComplex ℚ (TopCat.of U)).d 1 0 ≫
        ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 0 s₀)
    have hf : f = 𝟙 _ := by
      apply SSet.chainComplex_hom_ext
      intro σ
      dsimp [f]
      erw [CategoryTheory.Preadditive.comp_add]
      have hs (k : ℕ) (s : bh16_simplex (TopCat.of U) k →
          bh16_simplex (TopCat.of U) (k + 1)) (τ : bh16_simplex (TopCat.of U) k) :
          (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex τ ≫
            ModuleCat.ofHom (bh16_linearCone (TopCat.of U) k s) =
            (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s τ) := by
        change (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex τ ≫
          CategoryTheory.Limits.Sigma.desc (fun x ↦
            (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s x)) = _
        simp [CategoryTheory.Limits.Sigma.desc, CategoryTheory.Limits.Sigma.ι,
          SSet.ιChainComplex]
      erw [← Category.assoc, hs, SSet.ιChainComplex_d, ← Category.assoc,
        SSet.ιChainComplex_d, CategoryTheory.Preadditive.sum_comp]
      have h10 := (h₁ σ).1
      have h11 := (h₁ σ).2 (0 : Fin 2)
      have h12 := (h₁ σ).2 (1 : Fin 2)
      simp only [bh16_face] at h10 h11 h12
      norm_num at h10 h11 h12
      have hsa (τ : bh16_simplex (TopCat.of U) 0) := hs 0 s₀ τ
      have hsn (τ : bh16_simplex (TopCat.of U) 0) :
          (-(TopCat.toSSet.obj (TopCat.of U)).ιChainComplex τ) ≫
              ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 0 s₀) =
            -(TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s₀ τ) := by
        rw [CategoryTheory.Preadditive.neg_comp, hs]
        rfl
      simp [Fin.sum_univ_succ, h10, h11, h12]
      erw [hsa, hsn]
      erw [Category.comp_id]
      abel
    change f.hom c = c
    simpa using ConcreteCategory.congr_hom hf c
  · intro c
    let f := ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 2 s₂) ≫
        (SingularChainComplex ℚ (TopCat.of U)).d 3 2 +
      (SingularChainComplex ℚ (TopCat.of U)).d 2 1 ≫
        ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 1 s₁)
    have hf : f = 𝟙 _ := by
      apply SSet.chainComplex_hom_ext
      intro σ
      dsimp [f]
      erw [CategoryTheory.Preadditive.comp_add]
      have hs (k : ℕ) (s : bh16_simplex (TopCat.of U) k →
          bh16_simplex (TopCat.of U) (k + 1)) (τ : bh16_simplex (TopCat.of U) k) :
          (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex τ ≫
            ModuleCat.ofHom (bh16_linearCone (TopCat.of U) k s) =
            (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s τ) := by
        change (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex τ ≫
          CategoryTheory.Limits.Sigma.desc (fun x ↦
            (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s x)) = _
        simp [CategoryTheory.Limits.Sigma.desc, CategoryTheory.Limits.Sigma.ι,
          SSet.ιChainComplex]
      erw [← Category.assoc, hs, SSet.ιChainComplex_d, ← Category.assoc,
        SSet.ιChainComplex_d, CategoryTheory.Preadditive.sum_comp]
      have h20 := (h₂ σ).1
      have h21 := (h₂ σ).2 (0 : Fin 3)
      have h22 := (h₂ σ).2 (1 : Fin 3)
      have h23 := (h₂ σ).2 (2 : Fin 3)
      simp only [bh16_face] at h20 h21 h22 h23
      norm_num at h20 h21 h22 h23
      have hsa (τ : bh16_simplex (TopCat.of U) 1) := hs 1 s₁ τ
      have hsn (τ : bh16_simplex (TopCat.of U) 1) :
          (-(TopCat.toSSet.obj (TopCat.of U)).ιChainComplex τ) ≫
              ModuleCat.ofHom (bh16_linearCone (TopCat.of U) 1 s₁) =
            -(TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (s₁ τ) := by
        rw [CategoryTheory.Preadditive.neg_comp, hs]
        rfl
      simp [Fin.sum_univ_succ, h20, h21, h22, h23]
      erw [hsa, hsn, hsa]
      erw [Category.comp_id]
      abel
    change f.hom c = c
    simpa using ConcreteCategory.congr_hom hf c

/-- The two chain identities kill positive homology and hence its rational dual.
Source: Hatcher, Algebraic Topology, §2.A and §3.1; `cohomologyEquivDualHomology`. -/
theorem bh16_cone_cohomology_aux (n : ℕ) (U : Opens (Fin n → ℂ))
    (s₀ : (SingularChainComplex ℚ (TopCat.of U)).X 0 →ₗ[ℚ] (SingularChainComplex ℚ (TopCat.of U)).X 1) (s₁ : (SingularChainComplex ℚ (TopCat.of U)).X 1 →ₗ[ℚ] (SingularChainComplex ℚ (TopCat.of U)).X 2) (s₂ : (SingularChainComplex ℚ (TopCat.of U)).X 2 →ₗ[ℚ] (SingularChainComplex ℚ (TopCat.of U)).X 3)
    (h₁ : ∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 1,
      ((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom (s₁ c) + s₀ (((SingularChainComplex ℚ (TopCat.of U)).d 1 0).hom c) = c)
    (h₂ : ∀ c : (SingularChainComplex ℚ (TopCat.of U)).X 2,
      ((SingularChainComplex ℚ (TopCat.of U)).d 3 2).hom (s₂ c) + s₁ (((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom c) = c) (j : ℕ) (hj : 0 < j ∧ j ≤ 2) :
    Subsingleton (Cohomology ℚ (TopCat.of U) j) := by
  let K := SingularChainComplex ℚ (TopCat.of U)
  have hexact₁ : K.ExactAt 1 := by
    rw [K.exactAt_iff' 2 1 0 (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
    intro c hc
    refine ⟨s₁ c, ?_⟩
    change ((SingularChainComplex ℚ (TopCat.of U)).d 1 0).hom c = 0 at hc
    change ((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom (s₁ c) = c
    simpa only [hc, map_zero, add_zero] using h₁ c
  have hexact₂ : K.ExactAt 2 := by
    rw [K.exactAt_iff' 3 2 1 (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
    intro c hc
    refine ⟨s₂ c, ?_⟩
    change ((SingularChainComplex ℚ (TopCat.of U)).d 2 1).hom c = 0 at hc
    change ((SingularChainComplex ℚ (TopCat.of U)).d 3 2).hom (s₂ c) = c
    simpa only [hc, map_zero, add_zero] using h₂ c
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · have hhom : Subsingleton (Homology ℚ (TopCat.of U) 1) :=
      ModuleCat.subsingleton_of_isZero hexact₁.isZero_homology
    exact (cohomologyEquivDualHomology ℚ (TopCat.of U) 1).toEquiv.subsingleton
  · have hhom : Subsingleton (Homology ℚ (TopCat.of U) 2) :=
      ModuleCat.subsingleton_of_isZero hexact₂.isZero_homology
    exact (cohomologyEquivDualHomology ℚ (TopCat.of U) 2).toEquiv.subsingleton

/-- Sphere fillings imply rational cohomology vanishing in degrees one and two.
Source: the compatible cone construction and Hatcher, Algebraic Topology, §2.A and §3.1. -/
theorem bh16_filling_cohomology_aux (n : ℕ) (U : Opens (Fin n → ℂ))
    (hne : (U : Set (Fin n → ℂ)).Nonempty)
    (hfill : ∀ (k : ℕ), k ≤ 2 →
      ∀ u : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
        ContinuousOn u (Metric.sphere 0 1) →
        MapsTo u (Metric.sphere 0 1) (U : Set (Fin n → ℂ)) →
        ∃ v : (Fin (k + 1) → ℝ) → (Fin n → ℂ),
          ContinuousOn v (Metric.closedBall 0 1) ∧
          MapsTo v (Metric.closedBall 0 1) (U : Set (Fin n → ℂ)) ∧
          ∀ z ∈ Metric.sphere 0 1, v z = u z) (j : ℕ) (hj : 0 < j ∧ j ≤ 2) :
    Subsingleton (Cohomology ℚ (TopCat.of U) j) := by
  let p : U := ⟨hne.choose, hne.choose_spec⟩
  obtain ⟨s₀, h₀⟩ := bh16_vertex_cones_aux n U p hfill
  obtain ⟨s₁, h₁⟩ := bh16_edge_cones_aux n U p hfill s₀ h₀
  obtain ⟨s₂, h₂⟩ := bh16_triangle_cones_aux n U p hfill s₀ h₀ s₁ h₁
  obtain ⟨_e₀, e₁, e₂⟩ := bh16_cone_identity_aux n U p s₀ h₀ s₁ h₁ s₂ h₂
  exact bh16_cone_cohomology_aux n U
    (bh16_linearCone (TopCat.of U) 0 s₀) (bh16_linearCone (TopCat.of U) 1 s₁)
    (bh16_linearCone (TopCat.of U) 2 s₂) e₁ e₂ j hj

/-- The cover has a nonempty path-connected complement.
Source: `bh14_small_translation` and `bh14_cover_sphere_filling` at dimension zero. -/
theorem bh16_cover_connected_aux (n : ℕ) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j) :
    PathConnectedSpace O := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  rw [isPathConnected_iff]
  constructor
  · have hdim : ∀ j, (U j).Nonempty → 2 * d j + 0 < 2 * n := by
      intro j hj
      have := hd j hj
      omega
    obtain ⟨a, _ha, havoid⟩ := bh14_small_translation n 0 d U g hU hg hdim
      (fun _ ↦ 0) contDiff_const 1 (by norm_num)
    refine ⟨a, ?_⟩
    by_contra haO
    exact havoid 0 (by simp) (hcover ▸ (by simpa only [Set.mem_compl_iff, zero_add] using haO))
  · intro x hx y hy
    let u : (Fin 1 → ℝ) → (Fin n → ℂ) := fun z ↦
      ((1 - z 0) / 2) • x + ((1 + z 0) / 2) • y
    have hu : Continuous u := by
      fun_prop
    have huO : MapsTo u (Metric.sphere 0 1) O := by
      intro z hz
      have hz' : |z 0| = 1 := by
        simpa [Real.norm_eq_abs, Pi.norm_def, Finset.univ_unique] using hz
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hz' with hneg | hpos
      · simpa [u, hneg] using hy
      · simpa [u, hpos] using hx
    obtain ⟨w, hwc, hwO, hwbdry⟩ :=
      bh14_cover_sphere_filling n O hO d U g hU hg hd hcover 0 (by omega)
        u hu.continuousOn huO
    refine JoinedIn.ofLine (f := fun t : ℝ ↦ w (fun _ ↦ 2 * t - 1)) ?_ ?_ ?_ ?_
    · apply hwc.comp
      · fun_prop
      · intro t ht
        rw [mem_closedBall_zero_iff]
        simpa [Pi.norm_def] using
          (show ‖2 * t - 1‖ ≤ (1 : ℝ) by
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [ht.1, ht.2])
    · calc
        w (fun _ ↦ 2 * 0 - 1) = w (fun _ ↦ -1) := by congr 1; funext i; norm_num
        _ = u (fun _ ↦ -1) := hwbdry _ (by simp)
        _ = x := by simp [u]
    · calc
        w (fun _ ↦ 2 * 1 - 1) = w (fun _ ↦ 1) := by congr 1; funext i; norm_num
        _ = u (fun _ ↦ 1) := hwbdry _ (by simp)
        _ = y := by simp [u]
    · rintro _ ⟨t, ht, rfl⟩
      apply hwO
      rw [mem_closedBall_zero_iff]
      simpa [Pi.norm_def] using
        (show ‖2 * t - 1‖ ≤ (1 : ℝ) by
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [ht.1, ht.2])

private noncomputable def ambE (n : ℕ) (O : Set (Fin n → ℂ)) (k : ℕ) :
    ((relativeDualCochainShortComplexInt ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).X₂.homology (k : ℤ)) ≃ₗ[ℚ]
      Cohomology ℚ (TopCat.of (Fin n → ℂ)) k :=
  (((chainPairFunctor ℚ).obj
    (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).right.linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := k) (j' := (k : ℤ)) rfl).toLinearEquiv

private noncomputable def subE (n : ℕ) (O : Set (Fin n → ℂ)) (k : ℕ) :
    ((relativeDualCochainShortComplexInt ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).X₃.homology (k : ℤ)) ≃ₗ[ℚ]
      Cohomology ℚ (TopCat.of O) k :=
  (((chainPairFunctor ℚ).obj
    (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).left.linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := k) (j' := (k : ℤ)) rfl).toLinearEquiv

private lemma unit_natural {X Y : TopCat.{0}} [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) :
    cohomologyMap ℚ 0 f (cohomologyUnitZero ℚ Y) = cohomologyUnitZero ℚ X := by
  apply (cohomologyEquivDualHomology ℚ X 0).injective
  ext z
  rw [cohomologyEquivDualHomology_cohomologyMap,
    cohomologyEquivDualHomology_cohomologyUnitZero,
    cohomologyEquivDualHomology_cohomologyUnitZero]
  exact ConcreteCategory.congr_hom (TopCat.singularHomology₀ε_naturality f (ModuleCat.of ℚ ℚ)) z

private lemma cohomologyMap_zero_surjective {X Y : TopCat.{0}}
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y) :
    Function.Surjective (cohomologyMap ℚ 0 f) := by
  intro b
  obtain ⟨r, rfl⟩ := exists_smul_cohomologyUnitZero ℚ X b
  refine ⟨r • cohomologyUnitZero ℚ Y, ?_⟩
  rw [map_smul, unit_natural f]

private lemma cohomologyMap_zero_injective {X Y : TopCat.{0}}
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y) :
    Function.Injective (cohomologyMap ℚ 0 f) := by
  intro a b hab
  obtain ⟨r, hr⟩ := exists_smul_cohomologyUnitZero ℚ Y a
  obtain ⟨s, hs⟩ := exists_smul_cohomologyUnitZero ℚ Y b
  rw [← hr, ← hs, map_smul, map_smul, unit_natural f] at hab
  have hrs : r = s := by
    by_contra hne
    have : (r - s) • cohomologyUnitZero ℚ X = 0 := by
      rw [sub_smul, hab, sub_self]
    exact cohomologyUnitZero_ne_zero ℚ X (smul_eq_zero.mp this |>.resolve_left (sub_ne_zero.mpr hne))
  calc
    a = r • cohomologyUnitZero ℚ Y := hr.symm
    _ = s • cohomologyUnitZero ℚ Y := by rw [hrs]
    _ = b := hs

private lemma ext_restriction_zero_natural (n : ℕ) (O : Set (Fin n → ℂ))
    (a : (relativeDualCochainShortComplexInt ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).X₂.homology (0 : ℤ)) :
    (subE n O 0) ((HomologicalComplex.homologyMap
      (relativeDualCochainShortComplexInt ℚ
        (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).g (0 : ℤ)).hom a) =
      cohomologyMap ℚ 0 (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (ambE n O 0 a) := by
  let P := TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.extendHomologyIso_hom_naturality
      (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj P).hom)
      ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl) a
  change (subE n O 0)
      ((HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt ℚ P).g (0 : ℤ)).hom a) =
      (HomologicalComplex.homologyMap
        (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj P).hom) 0).hom
        (ambE n O 0 a) at h
  exact h.trans (by rfl)

private lemma ext_restriction_zero_surjective (n : ℕ) (O : Set (Fin n → ℂ))
    [PathConnectedSpace O] :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt ℚ
          (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).g (0 : ℤ)).hom := by
  let P := TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O
  let i : TopCat.of O ⟶ TopCat.of (Fin n → ℂ) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  intro b
  obtain ⟨a, ha⟩ := cohomologyMap_zero_surjective i (subE n O 0 b)
  refine ⟨(ambE n O 0).symm a, ?_⟩
  apply (subE n O 0).injective
  rw [← ha]
  change (subE n O 0)
      ((HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt ℚ P).g (0 : ℤ)).hom
        ((ambE n O 0).symm a)) = cohomologyMap ℚ 0 i a
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.extendHomologyIso_hom_naturality
      (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj P).hom)
      ComplexShape.embeddingUpNat (j := 0) (j' := (0 : ℤ)) rfl)
      ((ambE n O 0).symm a)
  change (subE n O 0)
      ((HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt ℚ P).g (0 : ℤ)).hom
        ((ambE n O 0).symm a)) =
      (HomologicalComplex.homologyMap
        (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj P).hom) 0).hom
        ((ambE n O 0) ((ambE n O 0).symm a)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  have h' : (subE n O 0)
      ((HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt ℚ P).g (0 : ℤ)).hom
        ((ambE n O 0).symm a)) =
      (HomologicalComplex.homologyMap
        (HomologicalComplex.linearDualMap ((chainPairFunctor ℚ).obj P).hom) 0).hom a := by
    simpa only [P, subE, ambE,
      relativeDualCochainShortComplexInt_g] using h
  exact h'.trans (by rfl)

private lemma ext_restriction_zero_injective (n : ℕ) (O : Set (Fin n → ℂ))
    [PathConnectedSpace O] :
    Function.Injective
      (HomologicalComplex.homologyMap
        (relativeDualCochainShortComplexInt ℚ
          (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O)).g (0 : ℤ)).hom := by
  let i : TopCat.of O ⟶ TopCat.of (Fin n → ℂ) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  intro a b hab
  apply (ambE n O 0).injective
  apply cohomologyMap_zero_injective i
  rw [← ext_restriction_zero_natural n O a, ← ext_restriction_zero_natural n O b, hab]

/-- Contractibility and the low-degree absolute calculation give relative vanishing.
Source: Hatcher, Algebraic Topology, §3.1; `relativeDualCochainShortComplexInt_shortExact`. -/
theorem bh16_pair_vanishing_aux (n : ℕ) (O : Set (Fin n → ℂ))
    (hc : PathConnectedSpace O)
    (hv : ∀ j : ℕ, 0 < j ∧ j ≤ 2 → Subsingleton (Cohomology ℚ (TopCat.of O) j))
    (k : ℕ) (hk : k ≤ 3) :
    Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O) k) := by
  letI : PathConnectedSpace O := hc
  let P := TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O
  let S := relativeDualCochainShortComplexInt ℚ P
  have hS : S.ShortExact := relativeDualCochainShortComplexInt_shortExact ℚ P
  have hA : ∀ q : ℕ, 0 < q → CategoryTheory.Limits.IsZero (S.X₂.homology (q : ℤ)) := by
    intro q hq
    have hz : CategoryTheory.Limits.IsZero
        (Cohomology ℚ (TopCat.of (Fin n → ℂ)) q) := by
      cases q with
      | zero => omega
      | succ r => exact (AlgebraicTopology.singularCochainComplex_exactAt_of_contractible ℚ
          (Fin n → ℂ) r).isZero_homology
    exact CategoryTheory.Limits.IsZero.of_iso hz (ambE n O q).toModuleIso
  have hO : ∀ q : ℕ, 0 < q → q ≤ 2 →
      CategoryTheory.Limits.IsZero (S.X₃.homology (q : ℤ)) := by
    intro q hq hq2
    have hz : CategoryTheory.Limits.IsZero (Cohomology ℚ (TopCat.of O) q) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hv q ⟨hq, hq2⟩)
    exact CategoryTheory.Limits.IsZero.of_iso hz (subE n O q).toModuleIso
  have hneg : CategoryTheory.Limits.IsZero (S.X₃.homology (-1 : ℤ)) := by
    apply ShortComplex.isZero_homology_of_isZero_X₂
    change CategoryTheory.Limits.IsZero
      (((relativeDualCochainShortComplexNat ℚ P).X₃.extend
        ComplexShape.embeddingUpNat).sc (-1 : ℤ)).X₂
    exact (relativeDualCochainShortComplexNat ℚ P).X₃.isZero_extend_X
      ComplexShape.embeddingUpNat (-1 : ℤ) (by intro i hi; norm_num at hi)
  have hg0 : Epi (HomologicalComplex.homologyMap S.g (0 : ℤ)) :=
    ConcreteCategory.epi_of_surjective _ (ext_restriction_zero_surjective n O)
  have hm0 : Mono (HomologicalComplex.homologyMap S.g (0 : ℤ)) :=
    ConcreteCategory.mono_of_injective _ (ext_restriction_zero_injective n O)
  have hz : CategoryTheory.Limits.IsZero (S.X₁.homology (k : ℤ)) := by
    interval_cases k
    · have hf0 : HomologicalComplex.homologyMap S.f (0 : ℤ) = 0 := by
        apply (cancel_mono (HomologicalComplex.homologyMap S.g (0 : ℤ))).1
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero]
        simp
      have hm : Mono (HomologicalComplex.homologyMap S.f (0 : ℤ)) :=
        (hS.homology_exact₁ (-1 : ℤ) 0 (by norm_num)).mono_g
          (hneg.eq_of_src _ _)
      exact CategoryTheory.Limits.IsZero.of_mono_eq_zero _ hf0
    · have hd0 : hS.δ (0 : ℤ) 1 (by norm_num) = 0 := by
        apply (cancel_epi (HomologicalComplex.homologyMap S.g (0 : ℤ))).1
        exact hS.comp_δ (0 : ℤ) 1 (by norm_num)
      exact (hS.homology_exact₁ (0 : ℤ) 1 (by norm_num)).isZero_X₂ hd0
        ((hA 1 (by omega)).eq_of_tgt _ _)
    · exact (hS.homology_exact₁ (1 : ℤ) 2 (by norm_num)).isZero_X₂
        ((hO 1 (by omega) (by omega)).eq_of_src _ _)
        ((hA 2 (by omega)).eq_of_tgt _ _)
    · exact (hS.homology_exact₁ (2 : ℤ) 3 (by norm_num)).isZero_X₂
        ((hO 2 (by omega) (by omega)).eq_of_src _ _)
        ((hA 3 (by omega)).eq_of_tgt _ _)
  letI := ModuleCat.subsingleton_of_isZero hz
  exact (relativeDualCochainCohomologyEquiv ℚ P k).symm.toEquiv.subsingleton

/-- Codimension-two covers imply support vanishing through degree three.
Source: Hatcher, Algebraic Topology, §3.1; the compatible cone and pair sequence. -/
theorem bh16_cover_support_vanishing_aux (n : ℕ) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j) (k : ℕ) (hk : k ≤ 3) :
    Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O) k) := by
  have hc := bh16_cover_connected_aux n O hO d U g hU hg hd hcover
  have hne : O.Nonempty := by
    obtain ⟨p⟩ := hc.nonempty
    exact ⟨p.1, p.2⟩
  apply bh16_pair_vanishing_aux n O hc _ k hk
  intro j hj
  exact bh16_filling_cohomology_aux n ⟨O, hO⟩ hne
    (bh14_cover_sphere_filling n O hO d U g hU hg hd hcover) j hj

/-- For nested subspaces the triple sequence gives restriction injectivity.
Source: Hatcher, Algebraic Topology, §3.1 (the triple long exact sequence). -/
theorem bh16_nested_restriction_aux (n : ℕ) (O Z : Set (Fin n → ℂ))
    (hsub : Zᶜ ⊆ O)
    (hv : Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) O) 2)) :
    Function.Injective
      (relativeCohomologyMap ℚ 2
        (TopPair.ofSubsetHom
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          (fun _ h ↦ h) :
          TopPair.ofSubset (X := TopCat.of O) {p | p.1 ∉ Z} ⟶
          TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) Zᶜ)) := by
  let X := TopCat.of (Fin n → ℂ)
  let W : Set O := {p | p.1 ∉ Z}
  let P₁ := TopPair.ofSubset (X := TopCat.of O) W
  let P₂ := TopPair.ofSubset (X := X) Zᶜ
  let P₃ := TopPair.ofSubset (X := X) O
  let q : P₁ ⟶ P₂ := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (fun _ h ↦ h)
  let r : P₂ ⟶ P₃ := TopPair.ofSubsetHom (𝟙 X) (fun p hp ↦ hsub hp)
  let F : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
    (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)
  let f : TopCat.of W ⟶ TopCat.of O := P₁.map
  let g : TopCat.of O ⟶ X := P₃.map
  let j : TopCat.of (Zᶜ : Set (Fin n → ℂ)) ⟶ X := P₂.map
  let uh : TopCat.of W ⟶ TopCat.of (Zᶜ : Set (Fin n → ℂ)) := TopCat.ofHom
    ⟨fun p ↦ ⟨p.1.1, p.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let ui : TopCat.of (Zᶜ : Set (Fin n → ℂ)) ⟶ TopCat.of W := TopCat.ofHom
    ⟨fun p ↦ ⟨⟨p.1, hsub p.2⟩, p.2⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  let u : TopCat.of W ≅ TopCat.of (Zᶜ : Set (Fin n → ℂ)) := {
    hom := uh
    inv := ui
    hom_inv_id := by ext p; rfl
    inv_hom_id := by ext p; rfl }
  have hfg : F.map f ≫ F.map g = (F.mapIso u).hom ≫ F.map j := by
    change F.map f ≫ F.map g = F.map u.hom ≫ F.map j
    rw [← F.map_comp, ← F.map_comp]
    congr 1
  let A := ((chainPairFunctor ℚ).obj P₁).hom
  let B : ((chainPairFunctor ℚ).obj P₁).right ⟶ F.obj X := F.map g
  let J : ((chainPairFunctor ℚ).obj P₂).left ⟶ F.obj X :=
    ((chainPairFunctor ℚ).obj P₂).hom
  let V : ((chainPairFunctor ℚ).obj P₁).left ≅
      ((chainPairFunctor ℚ).obj P₂).left := F.mapIso u
  have hAB : A ≫ B = V.hom ≫ J := by
    exact hfg
  have hAB' : (A ≫ B) ≫ (Iso.refl (F.obj X)).hom = V.hom ≫ J := by
    simpa using hAB
  letI : Mono A := relativeChainMap_mono ℚ P₁
  haveI : Mono g := (TopCat.mono_iff_injective g).2 Subtype.val_injective
  letI : Mono B := by
    exact relativeChainMap_mono ℚ P₃
  let T : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) := ShortComplex.mk
    (cokernel.map A (A ≫ B) (𝟙 _) B (by simp only [Category.id_comp]))
    (cokernel.map (A ≫ B) B A (𝟙 _) (by simp only [Category.comp_id]))
    (by
      apply (cancel_epi (cokernel.π A)).1
      dsimp [cokernel.map]
      simp [Category.assoc])
  have hT : T.ShortExact := by
    have hmono : Mono T.f := by
      dsimp [T]
      apply Abelian.mono_cokernel_map_of_isPullback
      refine IsPullback.of_vert_isIso_mono (fst := A) (snd := 𝟙 _)
        (f := B) (g := A ≫ B) ?_
      exact ⟨rfl⟩
    have hepi : Epi T.g := by
      dsimp [T, cokernel.map]
      apply cokernel.desc_epi
    exact
      { exact := (kernelCokernelCompSequence_exact A B).exact 3 (by omega)
        mono_f := hmono
        epi_g := hepi }
  let eJ : cokernel J ≅ (relativeChainFunctor ℚ).obj P₂ := Iso.refl _
  let m : T.X₂ ≅ cokernel J :=
    cokernel.mapIso (f := A ≫ B) J V (Iso.refl _) hAB'
  let e₂ : T.X₂ ≅ (relativeChainFunctor ℚ).obj P₂ :=
    m.trans eJ
  have hq : (relativeChainFunctor ℚ).map q = T.f ≫ e₂.hom := by
    have hu : V.hom = ((chainPairFunctor ℚ).map q).left := by rfl
    have wq : A ≫ B = ((chainPairFunctor ℚ).map q).left ≫ J := by
      rw [← hu]
      exact hAB
    have wT : A ≫ B = (𝟙 _) ≫ (A ≫ B) := by simp
    have h0 : cokernel.map A J ((chainPairFunctor ℚ).map q).left B wq =
        cokernel.map A (A ≫ B) (𝟙 _) B wT ≫ m.hom := by
      apply (cancel_epi (cokernel.π A)).1
      simp only [m, cokernel.mapIso, cokernel.map, cokernel.π_desc]
      rw [cokernel.π_desc_assoc]
      rw [Category.assoc, cokernel.π_desc, Iso.refl_hom, Category.id_comp]
    change cokernel.map A J ((chainPairFunctor ℚ).map q).left B wq ≫ eJ.hom =
      cokernel.map A (A ≫ B) (𝟙 _) B wT ≫ e₂.hom
    rw [h0]
    rfl
  have hsurj : Function.Surjective (relativeHomologyMap ℚ 2 q) := by
    have hzero : Subsingleton (T.X₃.homology 2) := by
      change Subsingleton (RelativeHomology ℚ P₃ 2)
      have hdual : Subsingleton (Module.Dual ℚ (RelativeHomology ℚ P₃ 2)) :=
        (relativeCohomologyEquivDualHomology ℚ P₃ 2).toEquiv.subsingleton_congr.mp hv
      exact (Module.subsingleton_dual_iff ℚ).mp hdual
    have hTsurj : Function.Surjective (HomologicalComplex.homologyMap T.f 2).hom := by
      intro y
      have hex := hT.homology_exact₂ 2
      have hy : (HomologicalComplex.homologyMap T.g 2).hom y = 0 := Subsingleton.elim _ _
      have hex' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hex
      obtain ⟨x, hx⟩ := (hex' y).mp hy
      exact ⟨x, hx⟩
    intro y
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap e₂.hom 2)).2 y
    obtain ⟨x, hx⟩ := hTsurj z
    refine ⟨x, ?_⟩
    have hqh := congrArg (fun k ↦ HomologicalComplex.homologyMap k 2) hq
    have hqx := ConcreteCategory.congr_hom hqh x
    have hcomp := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyMap_comp (φ := T.f) (ψ := e₂.hom) (i := 2)) x
    exact hqx.trans (hcomp.trans ((congrArg _ hx).trans hz))
  intro a b hab
  apply (relativeCohomologyEquivDualHomology ℚ P₂ 2).injective
  ext y
  obtain ⟨x, rfl⟩ := hsurj y
  have he := congrArg
    (fun c ↦ relativeCohomologyEquivDualHomology ℚ P₁ 2 c x) hab
  simpa only [relativeCohomologyEquivDualHomology_relativeCohomologyMap] using he

/-- Codimension-two removal inside the support preserves degree-two supported classes.
Source: Hatcher, Algebraic Topology, §3.1; support vanishing and the nested triple. -/
theorem bh16_cover_nested_restriction_aux (n : ℕ) (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ))
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, DifferentiableOn ℂ (g j) (U j))
    (hd : ∀ j, (U j).Nonempty → d j + 2 ≤ n)
    (hcover : Oᶜ = ⋃ j, g j '' U j) (Z : Set (Fin n → ℂ)) (hsub : Zᶜ ⊆ O) :
    Function.Injective
      (relativeCohomologyMap ℚ 2
        (TopPair.ofSubsetHom
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          (fun _ h ↦ h) :
          TopPair.ofSubset (X := TopCat.of O) {p | p.1 ∉ Z} ⟶
          TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) Zᶜ)) := by
  exact bh16_nested_restriction_aux n O Z hsub
    (bh16_cover_support_vanishing_aux n O hO d U g hU hg hd hcover 2 (by omega))

/-- Removing the critical zeros of a reduced analytic equation preserves degree-two classes.
Source: Hatcher, Algebraic Topology, §3.1; Gunning--Rossi, Analytic Functions of Several Complex Variables, Chapter III. -/
theorem bh16_singular_restriction_aux (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p)) :
    Function.Injective (relativeCohomologyMap ℚ 2 (bh8_regularInclusion n f)) := by
  obtain ⟨d, U, g, hd, hU, hg, hcover⟩ := bh15_critical_stratification n f hf hred
  have hfc : Continuous f :=
    continuous_iff_continuousAt.2 fun p => (hf p (mem_univ p)).continuousAt
  have hdfc : Continuous (fderiv ℂ f) :=
    continuous_iff_continuousAt.2 fun p => (hf.fderiv p (mem_univ p)).continuousAt
  have hO : IsOpen (bh8_regularDomain n f) := by
    exact (isOpen_ne_fun hfc continuous_const).union
      (isOpen_ne_fun hdfc continuous_const)
  have hcompl : (bh8_regularDomain n f)ᶜ =
      {p | f p = 0 ∧ fderiv ℂ f p = 0} := by
    ext p
    simp [bh8_regularDomain]
  let Z := {p | f p = 0}
  have hsub : Zᶜ ⊆ bh8_regularDomain n f := by
    intro p hp
    exact Or.inl hp
  have H := bh16_cover_nested_restriction_aux n (bh8_regularDomain n f) hO d U g hU hg hd
    (hcompl.trans hcover) Z hsub
  dsimp [Z, bh8_regularInclusion, bh8_regularPair, bh8_equationPair] at H ⊢
  exact H

end HodgeLean.Adapters
