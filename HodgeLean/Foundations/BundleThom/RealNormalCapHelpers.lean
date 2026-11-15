import HodgeLean.Foundations.BundleThom.RealProductNormalHelpers

/-! # Two actual caps of punctured real normal space

HC no distance; AV milestone no distance. -/

noncomputable section
open TopologicalSpace
namespace HodgeLean.Foundations.BundleThom

/-- The cap retains every vector with nonzero tail and the indicated head half-axis.
Source: Hatcher, Algebraic Topology, §2.2, the two-hemisphere cover of a sphere. -/
def i1_realNormalCap (d : ℕ) (positive : Bool) : Set (Fin (d + 1) → ℝ) :=
  {x | Fin.tail x ≠ 0 ∨ if positive then 0 < x 0 else x 0 < 0}

/-- A vector with zero head and zero tail is zero.
Source: Hatcher, Algebraic Topology, §2.2, Euclidean coordinates. -/
theorem i1_realNormal_eq_zero_of_head_tail (d : ℕ) (x : Fin (d + 1) → ℝ)
    (hh : x 0 = 0) (ht : Fin.tail x = 0) : x = 0 := by
  funext i
  refine Fin.cases hh (fun j => ?_) i
  exact congrFun ht j

/-- The two caps cover exactly the punctured real normal space.
Source: Hatcher, Algebraic Topology, §2.2, the two-hemisphere cover of a sphere. -/
theorem i1_realNormalCap_union (d : ℕ) :
    i1_realNormalCap d true ∪ i1_realNormalCap d false =
      {x : Fin (d + 1) → ℝ | x ≠ 0} := by
  ext x
  simp only [Set.mem_union, i1_realNormalCap, Set.mem_setOf_eq,
    Bool.false_eq_true, ↓reduceIte]
  constructor
  · intro h hx
    subst x
    have hz : Fin.tail (0 : Fin (d + 1) → ℝ) = 0 := rfl
    simp [hz] at h
  · intro hx
    by_cases ht : Fin.tail x = 0
    · have hh : x 0 ≠ 0 := fun h => hx (i1_realNormal_eq_zero_of_head_tail d x h ht)
      rcases lt_or_gt_of_ne hh with hn | hp
      · exact Or.inr (Or.inr hn)
      · exact Or.inl (Or.inr hp)
    · exact Or.inl (Or.inl ht)

/-- The cap intersection retains precisely the nonzero tail coordinate.
Source: Hatcher, Algebraic Topology, §2.2, the equatorial intersection of hemispheres. -/
theorem i1_realNormalCap_inter (d : ℕ) :
    i1_realNormalCap d true ∩ i1_realNormalCap d false =
      {x : Fin (d + 1) → ℝ | Fin.tail x ≠ 0} := by
  ext x
  change ((Fin.tail x ≠ 0 ∨ 0 < x 0) ∧
    (Fin.tail x ≠ 0 ∨ x 0 < 0)) ↔ Fin.tail x ≠ 0
  constructor
  · rintro ⟨ht | hp, ht | hn⟩
    · exact ht
    · exact ht
    · exact ht
    · exact (lt_asymm hp hn).elim
  · intro ht
    exact ⟨Or.inl ht, Or.inl ht⟩

/-- Both actual normal caps are open in the real coordinate space.
Source: Hatcher, Algebraic Topology, §2.2, open hemisphere covers. -/
theorem i1_realNormalCap_isOpen (d : ℕ) (positive : Bool) :
    IsOpen (i1_realNormalCap d positive) := by
  have ht : Continuous (Fin.tail : (Fin (d + 1) → ℝ) → (Fin d → ℝ)) :=
    continuous_pi fun j => continuous_apply j.succ
  have ho : IsOpen {x : Fin (d + 1) → ℝ | Fin.tail x ≠ 0} :=
    isClosed_singleton.isOpen_compl.preimage ht
  cases positive
  · exact ho.union (isOpen_lt (continuous_apply 0) continuous_const)
  · exact ho.union (isOpen_lt continuous_const (continuous_apply 0))

end HodgeLean.Foundations.BundleThom
