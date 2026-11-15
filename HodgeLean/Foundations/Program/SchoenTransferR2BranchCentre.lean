import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! # Branch loss occurs over a centre of the retained tower

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- If a compatible point starts on a branch and finishes off its strict transform,
it meets one of the actual blowup centres.
Source: Hartshorne, Algebraic Geometry, II.7, definition of strict transform.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_branch_or_centre
    {r : ℕ} (X : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (D : ∀ i, (X i).IdealSheafData)
    (I : ∀ i : Fin r, (X i.castSucc).IdealSheafData)
    (hD : ∀ i : Fin r, D i.succ = s2c_strictTransform (b i) (D i.castSucc) (I i))
    (x : ∀ i, X i) (hx : ∀ i : Fin r, b i (x i.succ) = x i.castSucc)
    (hinit : x 0 ∈ (D 0).support)
    (hfinal : x (Fin.last r) ∉ (D (Fin.last r)).support) :
    ∃ i : Fin r, x i.castSucc ∈ (I i).support := by
  classical
  by_contra hnone
  have hn : ∀ i : Fin r, x i.castSucc ∉ (I i).support := not_exists.mp hnone
  have hbranch : ∀ i, x i ∈ (D i).support := by
    intro i
    induction i using Fin.induction with
    | zero => exact hinit
    | succ j ih =>
      rw [hD j]
      change x j.succ ∈ ((s2c_strictTransform (b j) (D j.castSucc) (I j)).support : Set (X j.succ))
      rw [s2e_strictTransform_support_eq_removed_pullback,
        Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
      apply subset_closure
      change b j (x j.succ) ∈ (D j.castSucc).support ∧
        b j (x j.succ) ∉ (I j).support
      rw [hx j]
      exact ⟨ih, hn j⟩
  exact hfinal (hbranch (Fin.last r))

/-- The retained transition maps from the final stage to an intermediate stage.
Source: Hartshorne, Algebraic Geometry, II.7, successive blowup projections.
HC no distance; AV milestone no distance. -/
def s4_assembly_towerSuffixMap
    {C : Type*} [Category C] {r : ℕ} (X : Fin (r + 1) → C)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) : ∀ i, X (Fin.last r) ⟶ X i :=
  Fin.reverseInduction (𝟙 _) (fun i g => g ≫ b i)

/-- The final-stage suffix map is the identity.
Source: the defining recursion of `s4_assembly_towerSuffixMap`.
HC no distance; AV milestone no distance. -/
@[simp] theorem s4_assembly_towerSuffixMap_last
    {C : Type*} [Category C] {r : ℕ} (X : Fin (r + 1) → C)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) :
    s4_assembly_towerSuffixMap X b (Fin.last r) = 𝟙 _ :=
  Fin.reverseInduction_last

/-- Suffix maps retain the actual transition at every intermediate stage.
Source: the defining recursion of `s4_assembly_towerSuffixMap`.
HC no distance; AV milestone no distance. -/
@[simp] theorem s4_assembly_towerSuffixMap_castSucc
    {C : Type*} [Category C] {r : ℕ} (X : Fin (r + 1) → C)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) (i : Fin r) :
    s4_assembly_towerSuffixMap X b i.castSucc =
      s4_assembly_towerSuffixMap X b i.succ ≫ b i :=
  Fin.reverseInduction_castSucc i

/-- Every suffix followed by the retained initial map is the same final total map.
Source: Hartshorne, Algebraic Geometry, II.7, composition of the retained projections.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_towerSuffixMap_comp_total
    {C : Type*} [Category C] {r : ℕ} (X : Fin (r + 1) → C)
    {Y : C} (e : X 0 ⟶ Y) (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) :
    ∀ i, s4_assembly_towerSuffixMap X b i ≫ s2e_towerTotalMap X e b i =
      s2e_towerTotalMap X e b (Fin.last r) := by
  intro i
  refine Fin.reverseInduction ?_ (fun j ih => ?_) i
  · rw [s4_assembly_towerSuffixMap_last, Category.id_comp]
  · rw [s4_assembly_towerSuffixMap_castSucc, Category.assoc,
      ← s2e_towerTotalMap_succ, ih]

#print axioms s4_assembly_towerSuffixMap_comp_total
#print axioms s4_assembly_branch_or_centre
end HodgeLean.Foundations.Program
