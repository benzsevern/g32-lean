import HodgeLean.Foundations.Singular.TorusRing
import HodgeLean.Foundations.Singular.Exterior
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# The singular wedge map for the model torus

HC no distance; AV milestone no distance. This concerns rational singular
cohomology of the model torus only and retires no stated hypothesis.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular

/-- A degree-one class that already occurs among `w` cups `cupMulti (TopCat.of (UnitAddTorus (Fin n))) m w` to zero. -/
private theorem cup_cupMulti_eq_zero (n : ℕ) :
    ∀ (m : ℕ) (h : 1 + m = m + 1) (w : Fin m → Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) (k : Fin m),
      cup (TopCat.of (UnitAddTorus (Fin n))) h (w k) (cupMulti (TopCat.of (UnitAddTorus (Fin n))) m w) = 0
  | 0, _, _, k => k.elim0
  | m + 1, h, w, k => by
    rw [cupMulti_succ (TopCat.of (UnitAddTorus (Fin n))) m (Nat.add_comm 1 m),
      ← cup_assoc (TopCat.of (UnitAddTorus (Fin n))) (rfl : 1 + 1 = 2) (Nat.add_comm 1 m) (by omega) h]
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [torus_cup_self_eq_zero n, map_zero, LinearMap.zero_apply]
    · rw [torus_cup_comm_one n, map_neg, LinearMap.neg_apply,
        cup_assoc (TopCat.of (UnitAddTorus (Fin n))) (rfl : 1 + 1 = 2) (Nat.add_comm 1 m) (by omega) h]
      have := cup_cupMulti_eq_zero n m (Nat.add_comm 1 m) (Fin.tail w) k'
      rw [Fin.tail] at this
      rw [this, map_zero, neg_zero]

/-- `cupMulti (TopCat.of (UnitAddTorus (Fin n))) m` vanishes on families with a repeated entry. -/
private theorem cupMulti_eq_zero_of_eq (n : ℕ) :
    ∀ (m : ℕ) (v : Fin m → Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) (i j : Fin m), v i = v j → i ≠ j → cupMulti (TopCat.of (UnitAddTorus (Fin n))) m v = 0
  | 0, _, i, _, _, _ => i.elim0
  | m + 1, v, i, j, hv, hij => by
    rw [cupMulti_succ (TopCat.of (UnitAddTorus (Fin n))) m (Nat.add_comm 1 m)]
    have key : ∀ (i j : Fin (m + 1)), v i = v j → i ≠ j → i = 0 →
        cup (TopCat.of (UnitAddTorus (Fin n))) (Nat.add_comm 1 m) (v 0) (cupMulti (TopCat.of (UnitAddTorus (Fin n))) m (Fin.tail v)) = 0 := by
      intro i j hv hij hi
      subst hi
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hij.symm
      rw [hv]
      exact cup_cupMulti_eq_zero n m _ (Fin.tail v) j'
    by_cases hi : i = 0
    · exact key i j hv hij hi
    by_cases hj : j = 0
    · exact key j i hv.symm hij.symm hj
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    rw [cupMulti_eq_zero_of_eq n m (Fin.tail v) i' j' hv (fun h => hij (by rw [h])), map_zero]

/-- The alternating map `(a₁, …, a_m) ↦ a₁ ∪ ⋯ ∪ a_m`.
Source: constructed here from degree-one anticommutation on the model torus;
Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15.
-/
def cupAlternating (n : ℕ) (m : ℕ) :
    Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1 [⋀^Fin m]→ₗ[ℚ] Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m where
  toMultilinearMap := cupMulti (TopCat.of (UnitAddTorus (Fin n))) m
  map_eq_zero_of_eq' v i j hv hij := cupMulti_eq_zero_of_eq n m v i j hv hij

/-- **The wedge map (C6)** `⋀^m H¹(Tⁿ; ℚ) → H^m(Tⁿ; ℚ)`, `a₁ ∧ ⋯ ∧ a_m ↦ a₁ ∪ ⋯ ∪ a_m`.
Source: constructed here from degree-one anticommutation on the model torus;
Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15.
-/
def wedgeToCohomology (n : ℕ) (m : ℕ) : ⋀[ℚ]^m (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) →ₗ[ℚ] Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m :=
  exteriorPower.alternatingMapLinearEquiv (cupAlternating n m)

/-- The wedge map evaluates on a decomposable vector as the iterated cup product.
Source: constructed here using the universal property of the exterior power.
-/
theorem wedgeToCohomology_ιMulti (n : ℕ) (m : ℕ) (v : Fin m → Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) :
    wedgeToCohomology n m (exteriorPower.ιMulti ℚ m v) = cupMulti (TopCat.of (UnitAddTorus (Fin n))) m v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _


/-- `cupMulti` turns concatenation into the cup product, with the target degree given by an
equation.
Source: constructed here by associativity of singular cup products.
-/
theorem cupMulti_append (Y : TopCat.{0}) (n : ℕ) (b : Fin n → Cohomology ℚ Y 1) :
    ∀ (m : ℕ) (a : Fin m → Cohomology ℚ Y 1) (k : ℕ) (h : m + n = k) (c : Fin k → Cohomology ℚ Y 1),
      (∀ i : Fin m, c (Fin.cast h (Fin.castAdd n i)) = a i) →
      (∀ j : Fin n, c (Fin.cast h (Fin.natAdd m j)) = b j) →
      cupMulti Y k c = cup Y h (cupMulti Y m a) (cupMulti Y n b)
  | 0, a, k, h, c, _, hc2 => by
    obtain rfl : k = n := by omega
    rw [cupMulti_zero, one_cup Y]
    congr 1
    funext j
    rw [← hc2 j]
    congr 1
    ext
    simp
  | m + 1, a, k, h, c, hc1, hc2 => by
    obtain rfl : k = m + n + 1 := by omega
    rw [cupMulti_succ Y (m + n) (Nat.add_comm 1 _), cupMulti_succ Y m (Nat.add_comm 1 m),
      cup_assoc Y (Nat.add_comm 1 m) rfl h (Nat.add_comm 1 _)]
    have h0 : c 0 = a 0 := by
      rw [← hc1 0]
      congr 1
    rw [h0, cupMulti_append Y n b m (Fin.tail a) (m + n) rfl (Fin.tail c)
      (fun i => by
        change c _ = a i.succ
        rw [← hc1 i.succ]
        congr 1)
      (fun j => by
        change c _ = b j
        rw [← hc2 j]
        congr 1
        ext
        simp
        omega)]

/-- The wedge of two decomposable vectors is the decomposable vector of the concatenation. -/
private theorem wedge_ιMulti {M : Type*} [AddCommGroup M] [Module ℚ M] (m n : ℕ) (a : Fin m → M)
    (b : Fin n → M) :
    exteriorPower.wedge ℚ M m n (exteriorPower.ιMulti ℚ m a) (exteriorPower.ιMulti ℚ n b) =
      exteriorPower.ιMulti ℚ (m + n) (Fin.append a b) := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti ℚ m a * ExteriorAlgebra.ιMulti ℚ n b = _
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  rfl

/-- **Multiplicativity of the wedge map**: it sends `v ∧ w` to `v ∪ w`.
Source: constructed here by associativity and the exterior-power universal property;
Hatcher, *Algebraic Topology*, Theorem 3.15.
-/
theorem wedgeToCohomology_wedge (d : ℕ) (m n : ℕ) (v : ⋀[ℚ]^m (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin d))) 1))
    (w : ⋀[ℚ]^n (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin d))) 1)) :
    wedgeToCohomology d (m + n) (exteriorPower.wedge ℚ _ m n v w) =
      cup (TopCat.of (UnitAddTorus (Fin d))) rfl (wedgeToCohomology d m v) (wedgeToCohomology d n w) := by
  have key : (exteriorPower.wedge ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin d))) 1) m n).compr₂ (wedgeToCohomology d (m + n)) =
      (cup (TopCat.of (UnitAddTorus (Fin d))) rfl).compl₁₂ (wedgeToCohomology d m) (wedgeToCohomology d n) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun a => ?_)
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun b => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply]
    rw [wedge_ιMulti, wedgeToCohomology_ιMulti, wedgeToCohomology_ιMulti, wedgeToCohomology_ιMulti]
    exact cupMulti_append (TopCat.of (UnitAddTorus (Fin d))) n b m a (m + n) rfl _ (fun i => Fin.append_left a b i)
      (fun j => Fin.append_right a b j)
  exact LinearMap.congr_fun₂ key v w


/-- The singular iterated cup product is natural under continuous pullback.
Source: constructed here by induction from cup-product naturality.
-/
theorem cohomologyMap_cupMulti {Y Z : TopCat.{0}} (f : Z ⟶ Y) (m : ℕ)
    (a : Fin m → Cohomology ℚ Y 1) :
    cohomologyMap ℚ m f (cupMulti Y m a) =
      cupMulti Z m (fun i => cohomologyMap ℚ 1 f (a i)) := by
  induction m with
  | zero => simp only [cupMulti_zero, cohomologyMap_unit]
  | succ m ih =>
    rw [cupMulti_succ Y m (Nat.add_comm 1 m), cohomologyMap_cup,
      cupMulti_succ Z m (Nat.add_comm 1 m), ih]
    rfl

/-- Pullback between model tori intertwines exterior powers and the wedge map.
Source: constructed here using naturality of the iterated singular cup product.
-/
theorem wedgeToCohomology_naturality {n l : ℕ}
    (f : TopCat.of (UnitAddTorus (Fin n)) ⟶ TopCat.of (UnitAddTorus (Fin l)))
    (m : ℕ) (v : ⋀[ℚ]^m (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin l))) 1)) :
    wedgeToCohomology n m (exteriorPower.map m (cohomologyMap ℚ 1 f) v) =
      cohomologyMap ℚ m f (wedgeToCohomology l m v) := by
  have he : (wedgeToCohomology n m).comp (exteriorPower.map m (cohomologyMap ℚ 1 f)) =
      (cohomologyMap ℚ m f).comp (wedgeToCohomology l m) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun a => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, wedgeToCohomology_ιMulti, cohomologyMap_cupMulti]
    rfl
  exact LinearMap.congr_fun he v

/-- In degree zero the wedge map preserves the unit.
Source: constructed here from the empty iterated cup product.
-/
theorem wedgeToCohomology_zero (n : ℕ) :
    wedgeToCohomology n 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) =
      unit (R := ℚ) (TopCat.of (UnitAddTorus (Fin n))) := by
  rw [wedgeToCohomology_ιMulti, cupMulti_zero]

/-- In degree one the wedge map sends a single vector to itself.
Source: constructed here from the right unit law for cup products.
-/
theorem wedgeToCohomology_single (n : ℕ)
    (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) :
    wedgeToCohomology n 1 (exteriorPower.ιMulti ℚ 1 (fun _ => a)) = a := by
  rw [wedgeToCohomology_ιMulti, cupMulti_succ, cupMulti_zero]
  exact cup_one _ a

example (n m : ℕ) (a : Fin m → Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) :
    cupAlternating n m a = cupMulti (TopCat.of (UnitAddTorus (Fin n))) m a := rfl

example (n : ℕ) : wedgeToCohomology n 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) =
    unit (R := ℚ) (TopCat.of (UnitAddTorus (Fin n))) := wedgeToCohomology_zero n

#print axioms cupMulti
#print axioms cupAlternating
#print axioms wedgeToCohomology
#print axioms wedgeToCohomology_wedge
#print axioms wedgeToCohomology_naturality
#print axioms wedgeToCohomology_zero
#print axioms wedgeToCohomology_single

end HodgeLean.Foundations.Singular
