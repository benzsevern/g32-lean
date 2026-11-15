import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! Coordinate facts for realization of simplex faces.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Injective vertex maps act injectively on probability coordinates.
Source: Mathlib Finsupp.mapDomain_injective and StdSimplex.map. -/
lemma c1a5_simplex_map_injective {A B : Type} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (StdSimplex.map (R := ℝ) f) := by
  intro x y h
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hf (congrArg StdSimplex.weights h)

/-- A coface has zero weight at its omitted vertex.
Source: Mathlib StdSimplex.mem_range_map_iff and Fin.succAbove_ne. -/
lemma c1a5_coface_weight_zero {n : ℕ} (i : Fin (n + 2))
    (x : StdSimplex ℝ (Fin (n + 1))) :
    (StdSimplex.map (SimplexCategory.δ i) x).weights i = 0 := by
  apply (StdSimplex.mem_range_map_iff (SimplexCategory.δ i) _).1 ⟨x, rfl⟩ i
  rintro ⟨k, hk⟩
  exact Fin.succAbove_ne i k hk

/-- Two ordered cofaces omit exactly the two specified vertices.
Source: Mathlib SSet.stdSimplex.finOrderIsoPairCompl. -/
lemma c1a5_pair_vertex_range {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    Set.range ((SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt h)) ≫
      SimplexCategory.δ j) : ⦋n⦌ ⟶ ⦋n + 2⦌) = {k | k ≠ i ∧ k ≠ j} := by
  let e := SSet.stdSimplex.finOrderIsoPairCompl i j h
  change Set.range (fun k ↦ (e k).val) = _
  ext k
  constructor
  · rintro ⟨l, rfl⟩
    simpa only [Set.mem_setOf_eq, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] using
      (e l).property
  · intro hk
    let t : ({i, j}ᶜ : Finset (Fin (n + 3))) :=
      ⟨k, by simpa only [Set.mem_setOf_eq, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] using hk⟩
    exact ⟨e.symm t, congrArg Subtype.val (e.apply_symm_apply t)⟩

/-- A probability coordinate vector vanishing at two vertices lifts to their common face.
Source: Mathlib StdSimplex.mem_range_map_iff and finOrderIsoPairCompl. -/
lemma c1a5_pair_face_lift {n : ℕ} (i j : Fin (n + 3)) (h : i < j)
    (x : StdSimplex ℝ (Fin (n + 3))) (hi : x.weights i = 0) (hj : x.weights j = 0) :
    ∃ y : StdSimplex ℝ (Fin (n + 1)),
      StdSimplex.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt h)) ≫
        SimplexCategory.δ j) y = x := by
  apply (StdSimplex.mem_range_map_iff _ x).2
  intro k hk
  by_cases hki : k = i
  · simpa only [hki] using hi
  by_cases hkj : k = j
  · simpa only [hkj] using hj
  exact (hk (by rw [c1a5_pair_vertex_range i j h]; exact ⟨hki, hkj⟩)).elim

/-- A monomorphic ordinal map realizes to an injective simplex map.
Source: Mathlib SimplexCategory.toTopHomeo_naturality_apply and mono_iff_injective. -/
lemma c1a5_realized_simplex_map_injective {a b : SimplexCategory} (f : a ⟶ b) [Mono f] :
    Function.Injective (SSet.toTop.{0}.map (SSet.stdSimplex.map f)) := by
  intro x y h
  apply a.toTopHomeo.injective
  apply c1a5_simplex_map_injective f ((SimplexCategory.mono_iff_injective).1 inferInstance)
  calc
    StdSimplex.map f (a.toTopHomeo x) =
        b.toTopHomeo (SSet.toTop.map (SSet.stdSimplex.map f) x) :=
      (SimplexCategory.toTopHomeo_naturality_apply f x).symm
    _ = b.toTopHomeo (SSet.toTop.map (SSet.stdSimplex.map f) y) := congrArg b.toTopHomeo h
    _ = StdSimplex.map f (a.toTopHomeo y) :=
      SimplexCategory.toTopHomeo_naturality_apply f y

/-- A coordinate vector vanishing at one vertex lifts to its coface.
Source: Mathlib StdSimplex.mem_range_map_iff and Fin.range_succAbove. -/
lemma c1a5_coface_lift {n : ℕ} (i : Fin (n + 2))
    (x : StdSimplex ℝ (Fin (n + 2))) (hi : x.weights i = 0) :
    ∃ y : StdSimplex ℝ (Fin (n + 1)), StdSimplex.map (SimplexCategory.δ i) y = x := by
  apply (StdSimplex.mem_range_map_iff _ x).2
  intro k hk
  have hki : k = i := by
    have hr : Set.range (SimplexCategory.δ i : ⦋n⦌ ⟶ ⦋n + 1⦌) = {i}ᶜ :=
      Fin.range_succAbove i
    rw [hr] at hk
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hk
  simpa only [hki] using hi

end HodgeLean.Foundations.Program
