import HodgeLean.Foundations.Program.G32Native.PairedResidueOmission
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel

/-! # Coordinates on the full residue hyperplane with its last pair retained -/

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {K : Type*} [Field K] (s : ℕ)

/-- Keep both evaluations at each of the first s pairs and the first
last-pair evaluation. The other last-pair evaluation compensates the
sum of all retained evaluations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(i),
and proof of Lemma 2.4, the full residue hyperplane. -/
def pairedC3ResidueCoordinates :
    pencilResidueSpace K (s + 1) ≃ₗ[K]
      ((Fin s → K) × ((Fin s → K) × K)) where
  toFun v := (fun i => (v.val i.castSucc).1,
    (fun i => (v.val i.castSucc).2, (v.val (Fin.last s)).1))
  invFun a := ⟨Fin.snoc (α := fun _ => K × K) (fun i => (a.1 i, a.2.1 i))
    (a.2.2, -(∑ i, (a.1 i + a.2.1 i)) - a.2.2), by
      change (∑ i : Fin (s + 1), _) = 0
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact add_eq_zero_iff_eq_neg.mpr (by abel)⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      refine Prod.ext ?_ ?_
      · rfl
      · have h := v.property
        change (∑ i, ((v.val i).1 + (v.val i).2)) = 0 at h
        rw [Fin.sum_univ_castSucc] at h
        change -(∑ i : Fin s, ((v.val i.castSucc).1 + (v.val i.castSucc).2)) -
          (v.val (Fin.last s)).1 = (v.val (Fin.last s)).2
        linear_combination -h
    · simp only [Fin.snoc_castSucc]
  right_inv a := by
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  map_add' v w := rfl
  map_smul' c v := rfl

#print axioms pairedC3ResidueCoordinates
end HodgeLean.Foundations.Program.G32Native
