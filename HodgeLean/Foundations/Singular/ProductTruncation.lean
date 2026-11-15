import HodgeLean.Foundations.Singular.ProductFirstDegree

/-! Actual finite-degree comparison maps and their recursive extension. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Actual tensor-to-product chain maps through a finite degree, natural in both spaces.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models construction. -/
structure ProductChainTruncation (N : ℕ) where
  map : ∀ (k : ℕ), k ≤ N → ∀ X Y : TopCat.{0},
    (rationalTensorChains X Y).X k →ₗ[ℚ] (rationalChains (TopCat.of (X × Y))).X k
  naturality : ∀ (k : ℕ) (hk : k ≤ N) {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
    (map k hk X' Y').comp ((rationalTensorChainMap f g).f k).hom =
      (((rationalChainMap (topologicalProductMap f g)).f k).hom).comp (map k hk X Y)
  boundary : ∀ (k : ℕ) (hk : k + 1 ≤ N) (X Y : TopCat.{0}),
    (((rationalChains (TopCat.of (X × Y))).d (k + 1) k).hom).comp (map (k + 1) hk X Y) =
      (map k (Nat.le_trans (Nat.le_succ k) hk) X Y).comp
        ((rationalTensorChains X Y).d (k + 1) k).hom

/-- The actual degree-zero map and its constructed first-degree extension give the initial truncation.
Source: Hatcher, Algebraic Topology, §3.2, the augmented acyclic-models construction. -/
def productChainTruncationOne : ProductChainTruncation 1 := by
  let a := Classical.choose tensorProduct_first_degree_exists
  have ha := Classical.choose_spec tensorProduct_first_degree_exists
  refine
    { map := fun k hk X Y => ?_
      naturality := ?_
      boundary := ?_ }
  · cases k with
    | zero => exact tensorProductZero X Y
    | succ k =>
        have hk0 : k = 0 := by omega
        subst k
        exact a X Y
  · intro k hk X X' Y Y' f g
    cases k with
    | zero => exact tensorProductZero_naturality f g
    | succ k =>
        have hk0 : k = 0 := by omega
        subst k
        exact ha.1 f g
  · intro k hk X Y
    have hk0 : k = 0 := by omega
    subst k
    exact ha.2 X Y

/-- Extend actual finite-degree comparison maps by the checked positive-degree model construction.
Source: Hatcher, Algebraic Topology, §3.2, the acyclic-models induction. -/
def ProductChainTruncation.extend (n : ℕ) (T : ProductChainTruncation (n + 1)) :
    ProductChainTruncation (n + 2) := by
  classical
  let a := T.map (n + 1) (le_refl _)
  let b := T.map n (Nat.le_succ n)
  have ha : ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y'),
      (a X' Y').comp ((rationalTensorChainMap f g).f (n + 1)).hom =
        (((rationalChainMap (topologicalProductMap f g)).f (n + 1)).hom).comp (a X Y) :=
    fun f g => T.naturality (n + 1) (le_refl _) f g
  have hab := T.boundary n (le_refl _)
  let c := Classical.choose (productModel_extend_positive n a b ha hab)
  have hc := Classical.choose_spec (productModel_extend_positive n a b ha hab)
  let m (k : ℕ) (hk : k ≤ n + 2) (X Y : TopCat.{0}) :
      (rationalTensorChains X Y).X k →ₗ[ℚ] (rationalChains (TopCat.of (X × Y))).X k :=
    if h : k ≤ n + 1 then T.map k h X Y else by
      have he : k = n + 2 := by omega
      subst k
      exact c X Y
  refine { map := m, naturality := ?_, boundary := ?_ }
  · intro k hk X X' Y Y' f g
    by_cases hold : k ≤ n + 1
    · simpa only [m, dif_pos hold] using T.naturality k hold f g
    · have he : k = n + 2 := by omega
      subst k
      simpa only [m, dif_neg (by omega : ¬ n + 2 ≤ n + 1)] using hc.1 f g
  · intro k hk X Y
    by_cases hold : k + 1 ≤ n + 1
    · have hold0 : k ≤ n + 1 := by omega
      simpa only [m, dif_pos hold, dif_pos hold0] using T.boundary k hold X Y
    · have he : k = n + 1 := by omega
      subst k
      simpa only [m, dif_neg (by omega : ¬ n + 1 + 1 ≤ n + 1),
        dif_pos (le_refl (n + 1))] using hc.2 X Y

/-- The extension preserves every previously constructed actual degree map.
Source: Hatcher, Algebraic Topology, §3.2, induction of chain comparison maps. -/
theorem ProductChainTruncation.extend_map_le
    (n : ℕ) (T : ProductChainTruncation (n + 1)) (k : ℕ)
    (hk : k ≤ n + 1) (hk' : k ≤ n + 2) (X Y : TopCat.{0}) :
    (ProductChainTruncation.extend n T).map k hk' X Y = T.map k hk X Y := by
  classical
  dsimp only [ProductChainTruncation.extend]
  rw [dif_pos hk]

#print axioms ProductChainTruncation.extend_map_le
#print axioms ProductChainTruncation.extend
#print axioms productChainTruncationOne
end HodgeLean.Foundations.Singular
