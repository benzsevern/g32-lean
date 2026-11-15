import HodgeLean.Foundations.Program.G32SelectedRealizationProjector
import HodgeLean.Papers.PapersSupplyProofs

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32y_sum_map_filter_nonzero {A R : Type*} [Zero A] [DecidableEq A] [AddCommMonoid R]
    (s : Multiset A) (w : A → R) (hw : w 0 = 0) :
    ((s.filter (· ≠ 0)).map w).sum = (s.map w).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : a = 0
    · subst a
      simp [hw, ih]
    · simp [ha, ih]

theorem g32y_papers_local_exponent_weight {G : Type*} [Group G] [Finite G]
    {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (g : G) (w : ZMod m → ℝ) (hw : w 0 = 0) :
    letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
      Fintype.ofFinite _
    ((papersExps H χ g).map w).sum =
      ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
        w (Multiplicative.toAdd (χ (papersLocalMonodromy H g q))) := by
  classical
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  unfold papersExps
  rw [g32y_sum_map_filter_nonzero _ w hw, Multiset.map_map]
  rfl

theorem g32y_papers_exponent_list_weight {G : Type*} [Group G] [Finite G]
    {m : ℕ} [NeZero m] (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (gs : List G) (w : ZMod m → ℝ) :
    ((papersExpsList H χ gs).map fun a : ℕ ↦ w (a : ZMod m)).sum =
      (gs.map fun g ↦ ((papersExps H χ g).map w).sum).sum := by
  have hn : ((papersExpsList H χ gs).map fun a : ℕ ↦ w (a : ZMod m)).sum =
      ((papersExpsTuple H χ gs).map w).sum := by
    rw [papersExpsList, ← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Multiset.map_map]
    simp only [Function.comp_def, ZMod.natCast_zmod_val]
  rw [hn]
  clear hn
  induction gs with
  | nil => simp [papersExpsTuple]
  | cons g gs ih =>
    rw [papersExpsTuple_cons, Multiset.map_add, Multiset.sum_add, ih]
    rfl

end HodgeLean.Foundations.Program
