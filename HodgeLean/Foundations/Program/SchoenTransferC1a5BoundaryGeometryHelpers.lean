import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import HodgeLean.Foundations.Program.SchoenTransferC1a5RealizationMonoHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5SimplexGeometryHelpers

/-! Coordinate intersection checks for the actual realized boundary.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Two ordered face representatives with the same ambient point give the same boundary point.
Source: Mathlib facePairComplIso_hom_ι and simplex probability coordinates. -/
lemma c1a5_boundary_face_glue {n : ℕ} (i j : Fin (n + 3)) (h : i < j)
    (s t : SSet.toTop.obj (Δ[n + 1] : SSet.{0}))
    (he : SSet.toTop.map (SSet.stdSimplex.δ i) s =
      SSet.toTop.map (SSet.stdSimplex.δ j) t) :
    SSet.toTop.map (SSet.boundary.ι i) s = SSet.toTop.map (SSet.boundary.ι j) t := by
  let a := i.castPred (Fin.ne_last_of_lt h)
  let b := j.pred (Fin.ne_zero_of_lt h)
  let q := SSet.stdSimplex.δ a ≫ SSet.stdSimplex.δ j
  have hi : (⦋n + 2⦌.toTopHomeo (SSet.toTop.map (SSet.stdSimplex.δ j) t)).weights i = 0 := by
    rw [← he]
    exact (congrArg (fun v ↦ v.weights i)
      (SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) s)).trans
        (c1a5_coface_weight_zero _ _)
  have hj : (⦋n + 2⦌.toTopHomeo (SSet.toTop.map (SSet.stdSimplex.δ j) t)).weights j = 0 := by
    exact (congrArg (fun v ↦ v.weights j)
      (SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ j) t)).trans
        (c1a5_coface_weight_zero _ _)
  obtain ⟨z, hz⟩ := c1a5_pair_face_lift i j h _ hi hj
  let u := ⦋n⦌.toTopHomeo.symm z
  have hq : SSet.toTop.map q u = SSet.toTop.map (SSet.stdSimplex.δ j) t := by
    apply ⦋n + 2⦌.toTopHomeo.injective
    change ⦋n + 2⦌.toTopHomeo
      (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ a ≫ SimplexCategory.δ j)) u) = _
    rw [SimplexCategory.toTopHomeo_naturality_apply]
    simpa only [u, Homeomorph.apply_symm_apply] using hz
  have hw : SSet.stdSimplex.δ b ≫ SSet.stdSimplex.δ i = q :=
    (SSet.stdSimplex.facePairComplIso_hom_ι' i j h).symm.trans
      (SSet.stdSimplex.facePairComplIso_hom_ι i j h)
  have hs : SSet.toTop.map (SSet.stdSimplex.δ b) u = s := by
    apply c1a5_realized_simplex_map_injective (SimplexCategory.δ i)
    change (SSet.toTop.map (SSet.stdSimplex.δ b) ≫
      SSet.toTop.map (SSet.stdSimplex.δ i)) u = _
    rw [← SSet.toTop.map_comp, hw]
    exact hq.trans he.symm
  have ht : SSet.toTop.map (SSet.stdSimplex.δ a) u = t := by
    apply c1a5_realized_simplex_map_injective (SimplexCategory.δ j)
    change (SSet.toTop.map (SSet.stdSimplex.δ a) ≫
      SSet.toTop.map (SSet.stdSimplex.δ j)) u = _
    rw [← SSet.toTop.map_comp]
    exact hq
  have hb : SSet.stdSimplex.δ b ≫ SSet.boundary.ι i =
      SSet.stdSimplex.δ a ≫ SSet.boundary.ι j := by
    apply (cancel_mono (SSet.boundary.{0} (n + 2)).ι).1
    simpa only [Category.assoc, SSet.boundary.ι_ι] using hw
  rw [← hs, ← ht]
  change (SSet.toTop.map (SSet.stdSimplex.δ b) ≫ SSet.toTop.map (SSet.boundary.ι i)) u =
    (SSet.toTop.map (SSet.stdSimplex.δ a) ≫ SSet.toTop.map (SSet.boundary.ι j)) u
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, hb]

/-- The two realized faces of an edge have distinct ambient images.
Source: Mathlib StdSimplex.weights_ne_zero and omitted-vertex coordinates. -/
lemma c1a5_edge_faces_disjoint (i j : Fin 2) (h : i ≠ j)
    (s t : SSet.toTop.obj (Δ[0] : SSet.{0})) :
    SSet.toTop.map (SSet.stdSimplex.δ i) s ≠
      SSet.toTop.map (SSet.stdSimplex.δ j) t := by
  intro he
  let w := ⦋1⦌.toTopHomeo (SSet.toTop.map (SSet.stdSimplex.δ j) t)
  have hi : w.weights i = 0 := by
    dsimp only [w]
    rw [← he]
    exact (congrArg (fun v ↦ v.weights i)
      (SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) s)).trans
        (c1a5_coface_weight_zero _ _)
  have hj : w.weights j = 0 :=
    (congrArg (fun v ↦ v.weights j)
      (SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ j) t)).trans
        (c1a5_coface_weight_zero _ _)
  apply StdSimplex.weights_ne_zero w
  ext k
  have hi2 : i.val < 2 := i.isLt
  have hj2 : j.val < 2 := j.isLt
  have hk2 : k.val < 2 := k.isLt
  have hij : i.val ≠ j.val := fun e ↦ h (Fin.ext e)
  have hk : k = i ∨ k = j := by omega
  rcases hk with rfl | rfl
  · exact hi
  · exact hj

/-- A boundary face followed by its ambient inclusion is the specified realized coface.
Source: Mathlib SSet.boundary.ι_ι and Functor.map_comp. -/
lemma c1a5_boundary_coface_comp {n : ℕ} (i : Fin (n + 2))
    (s : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι
      (SSet.toTop.map (SSet.boundary.ι i) s) =
        SSet.toTop.map (SSet.stdSimplex.δ i) s := by
  change (SSet.toTop.map (SSet.boundary.ι i) ≫
    SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι) s = _
  rw [← SSet.toTop.map_comp, SSet.boundary.ι_ι]

/-- The actual realized standard boundary inclusion is monomorphic in every dimension.
Source: Mathlib boundary face representatives and common-face coordinate lifting. -/
lemma c1a5_boundary_realization_mono (n : ℕ) :
    Mono (SSet.toTop.{0}.map (SSet.boundary.{0} n).ι) := by
  rw [TopCat.mono_iff_injective]
  cases n with
  | zero =>
    rw [SSet.boundary_zero]
    have ht := (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{0}))).isInitialObj SSet.toTop _
    have : IsEmpty (SSet.toTop.obj ((⊥ : (Δ[0] : SSet.{0}).Subcomplex) : SSet)) :=
      Function.isEmpty (ht.to (TopCat.of PEmpty))
    intro x
    exact isEmptyElim x
  | succ n =>
    intro x y he
    obtain ⟨i, s, hx⟩ := c1a5_boundary_realization_exists_face n x
    obtain ⟨j, t, hy⟩ := c1a5_boundary_realization_exists_face n y
    have he' : SSet.toTop.map (SSet.stdSimplex.δ i) s =
        SSet.toTop.map (SSet.stdSimplex.δ j) t :=
      (c1a5_boundary_coface_comp i s).symm.trans
        (((congrArg (SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι) hx).trans
          (he.trans (congrArg (SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι) hy).symm)).trans
            (c1a5_boundary_coface_comp j t))
    rw [← hx, ← hy]
    by_cases hij : i = j
    · subst j
      have hst := c1a5_realized_simplex_map_injective (SimplexCategory.δ i) he'
      rw [hst]
    · cases n with
      | zero => exact (c1a5_edge_faces_disjoint i j hij s t he').elim
      | succ n =>
        rcases lt_or_gt_of_ne hij with h | h
        · exact c1a5_boundary_face_glue i j h s t he'
        · exact (c1a5_boundary_face_glue j i h t s he'.symm).symm

/-- Realization preserves arbitrary simplicial monomorphisms.
Source: Mathlib SSet.relativeCellComplexOfMono and realized boundary monomorphy. -/
lemma c1a5_realization_map_mono {A B : SSet.{0}} (f : A ⟶ B) [Mono f] :
    Mono (SSet.toTop.map f) := by
  let G := SSet.toTop.{0} ⋙ forget TopCat
  have hb (n : ℕ) : Mono (G.map (SSet.boundary.{0} n).ι) := by
    rw [mono_iff_injective]
    exact (TopCat.mono_iff_injective _).1 (c1a5_boundary_realization_mono n)
  have hm := c1a5_map_mono_of_boundary_mono G hb f
  exact (TopCat.mono_iff_injective _).2 ((mono_iff_injective _).1 hm)

/-- The realized standard boundary is compact, including the empty boundary.
Source: Mathlib CompactSpace for standard topological simplices and finite face representatives. -/
lemma c1a5_boundary_realization_compact (n : ℕ) :
    CompactSpace (SSet.toTop.obj (SSet.boundary.{0} n : SSet)) := by
  cases n with
  | zero =>
    rw [SSet.boundary_zero]
    have ht := (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{0}))).isInitialObj SSet.toTop _
    have : IsEmpty (SSet.toTop.obj ((⊥ : (Δ[0] : SSet.{0}).Subcomplex) : SSet)) :=
      Function.isEmpty (ht.to (TopCat.of PEmpty))
    infer_instance
  | succ n =>
    have : CompactSpace (SSet.toTop.obj (Δ[n] : SSet.{0})) :=
      (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
    let g : (Σ _ : Fin (n + 2), SSet.toTop.obj (Δ[n] : SSet.{0})) →
        SSet.toTop.obj (SSet.boundary.{0} (n + 1) : SSet) :=
      fun p ↦ SSet.toTop.map (SSet.boundary.ι p.1) p.2
    have hg : Continuous g := continuous_sigma (fun i ↦ (SSet.toTop.map (SSet.boundary.ι i)).hom.continuous)
    exact Function.Surjective.compactSpace hg (fun x ↦ by
      obtain ⟨i, y, hy⟩ := c1a5_boundary_realization_exists_face n x
      exact ⟨⟨i, y⟩, hy⟩)

/-- The realized boundary inclusion embeds its compact source as a topological subspace.
Source: Mathlib Continuous.isClosedEmbedding and realized boundary monomorphy. -/
lemma c1a5_boundary_realization_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (SSet.toTop.{0}.map (SSet.boundary.{0} n).ι) := by
  have := c1a5_boundary_realization_compact n
  have : T2Space (StdSimplex ℝ (Fin (⦋n⦌.len + 1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  have : T2Space (SSet.toTop.obj (Δ[n] : SSet.{0})) :=
    (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  exact (SSet.toTop.map (SSet.boundary.{0} n).ι).hom.continuous.isClosedEmbedding
    ((TopCat.mono_iff_injective _).1 (c1a5_boundary_realization_mono n))

end HodgeLean.Foundations.Program
