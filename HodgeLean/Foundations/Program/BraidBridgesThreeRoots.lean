import HodgeLean.Foundations.Program.BraidBridgesThreeLasso
import HodgeLean.Foundations.Program.BraidCertificate

/-! # Root witnesses in the isolating boxes

A root witness has one root in each certified box. The boxes are pairwise disjoint, so the
twelve roots are distinct and, with zero, they are all thirteen branch points. The boxes about
the real roots in boxes 0 and 6 are symmetric under conjugation, so those two roots are real, and
the rational normalization enclosures apply to the witness.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Complex
namespace HodgeLean.Foundations.Program

/-- Inverse of the box permutation. -/
def b65x_boxInv : Fin 12 → Fin 12 := ![7, 3, 8, 1, 9, 2, 5, 11, 10, 4, 0, 6]

theorem b65x_boxIndex_boxInv (j : Fin 12) : b65b_boxIndex (b65x_boxInv j) = j := by
  fin_cases j <;> rfl

theorem b65x_boxInv_boxIndex (k : Fin 12) : b65x_boxInv (b65b_boxIndex k) = k := by
  fin_cases k <;> rfl

/-- Distinct boxes have centres at least `2/10000` apart in one coordinate. -/
theorem b65x_box_sep_rat : ∀ k k' : Fin 12, k ≠ k' →
    (2/10000 : ℚ) ≤ |(b65b_boxCentre k).1 - (b65b_boxCentre k').1| ∨
      (2/10000 : ℚ) ≤ |(b65b_boxCentre k).2 - (b65b_boxCentre k').2| := by
  intro k k' h
  fin_cases k <;> fin_cases k' <;>
    first
    | exact absurd rfl h
    | (left; rw [le_abs]; norm_num [b65b_boxCentre]; done)
    | (right; rw [le_abs]; norm_num [b65b_boxCentre])

/-- Two points in two boxes coincide only when the boxes do. -/
theorem b65x_box_unique {k k' : Fin 12} {z : ℂ}
    (h1 : |z.re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ))
    (h2 : |z.im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ))
    (h1' : |z.re - ((b65b_boxCentre k').1 : ℝ)| < (1/10000 : ℝ))
    (h2' : |z.im - ((b65b_boxCentre k').2 : ℝ)| < (1/10000 : ℝ)) : k = k' := by
  by_contra hne
  rcases b65x_box_sep_rat k k' hne with h | h
  · have hR := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hR
    have := abs_sub_le ((b65b_boxCentre k).1 : ℝ) z.re ((b65b_boxCentre k').1 : ℝ)
    rw [abs_sub_comm] at h1
    linarith
  · have hR := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hR
    have := abs_sub_le ((b65b_boxCentre k).2 : ℝ) z.im ((b65b_boxCentre k').2 : ℝ)
    rw [abs_sub_comm] at h2
    linarith

theorem b65x_P_conj (ε : ℝ) (z : ℂ) :
    b65r_P (ε : ℂ) ((starRingEnd ℂ) z) = (starRingEnd ℂ) (b65r_P (ε : ℂ) z) := by
  simp [b65r_P, map_sub, map_mul, map_pow, map_add, Complex.conj_ofReal, map_ofNat]

section Witness

variable (p : Fin 12 → ℂ)
  (hp : ∀ k : Fin 12,
    |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)

include hp

theorem b65x_witness_box (j : Fin 12) :
    |(p j).re - ((b65b_boxCentre (b65x_boxInv j)).1 : ℝ)| < (1/10000 : ℝ) ∧
    |(p j).im - ((b65b_boxCentre (b65x_boxInv j)).2 : ℝ)| < (1/10000 : ℝ) ∧
    b65r_P (b65b_boxFibre (b65x_boxInv j)) (p j) = 0 := by
  have h := hp (b65x_boxInv j)
  rwa [b65x_boxIndex_boxInv] at h

theorem b65x_witness_injective : Function.Injective p := by
  intro i j hij
  have hi := b65x_witness_box p hp i
  have hj := b65x_witness_box p hp j
  rw [hij] at hi
  have := b65x_box_unique hi.1 hi.2.1 hj.1 hj.2.1
  have h2 := congrArg b65b_boxIndex this
  rwa [b65x_boxIndex_boxInv, b65x_boxIndex_boxInv] at h2

theorem b65x_witness_ne_zero (j : Fin 12) : p j ≠ 0 := by
  intro h
  have hb := (b65x_witness_box p hp j).2.2
  rw [h] at hb
  have hf : b65b_boxFibre (b65x_boxInv j) ≠ 0 := by
    generalize b65x_boxInv j = k
    fin_cases k <;> norm_num [b65b_boxFibre]
  apply b65s_fibre_ne_zero _ (by exact_mod_cast hf) hb

theorem b65x_witness_branch (j : Fin 12) : p j ∈ b65s_branchFinset := by
  rw [b65s_mem_branchFinset]
  have hb := (b65x_witness_box p hp j).2.2
  have hf : b65b_boxFibre (b65x_boxInv j) = 5 ∨ b65b_boxFibre (b65x_boxInv j) = -7 := by
    generalize b65x_boxInv j = k
    fin_cases k <;> norm_num [b65b_boxFibre]
  rcases hf with hf | hf
  · rw [hf] at hb; right; left; exact_mod_cast hb
  · rw [hf] at hb; right; right; exact_mod_cast hb

/-- Zero and the twelve witnesses are all of the branch points. -/
theorem b65x_witness_exhaust (z : ℂ) (hz : z = 0 ∨ b65r_P 5 z = 0 ∨ b65r_P (-7) z = 0) :
    z = 0 ∨ ∃ j, p j = z := by
  classical
  let T : Finset ℂ := insert 0 (Finset.univ.image p)
  have hsub : T ⊆ b65s_branchFinset := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rw [b65s_mem_branchFinset]; left; rfl
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
      exact b65x_witness_branch p hp j
  have hcard : T.card = 13 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _
      (b65x_witness_injective p hp)]
    · simp
    · intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact b65x_witness_ne_zero p hp j hj
  have heq : T = b65s_branchFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, b65s_branchFinset_card])
  have hzT : z ∈ T := by rw [heq, b65s_mem_branchFinset]; exact hz
  rcases Finset.mem_insert.mp hzT with h | h
  · exact Or.inl h
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨j, hj⟩

/-- A witness in a box centred on the real axis is real. -/
theorem b65x_witness_real (j : Fin 12) (hc : (b65b_boxCentre (b65x_boxInv j)).2 = 0) :
    (p j).im = 0 := by
  have hb := b65x_witness_box p hp j
  have hroot : b65r_P 5 ((starRingEnd ℂ) (p j)) = 0 ∨ b65r_P (-7) ((starRingEnd ℂ) (p j)) = 0 := by
    have hf : b65b_boxFibre (b65x_boxInv j) = 5 ∨ b65b_boxFibre (b65x_boxInv j) = -7 := by
      generalize b65x_boxInv j = k
      fin_cases k <;> norm_num [b65b_boxFibre]
    rcases hf with hf | hf
    · left
      have h := b65x_P_conj 5 (p j)
      rw [hf] at hb
      push_cast at h hb
      rw [h, hb.2.2, map_zero]
    · right
      have h := b65x_P_conj (-7) (p j)
      rw [hf] at hb
      push_cast at h hb
      rw [h, hb.2.2, map_zero]
  rcases b65x_witness_exhaust p hp _ (Or.inr hroot) with h0 | ⟨i, hi⟩
  · exact absurd (by simpa using h0) (b65x_witness_ne_zero p hp j)
  · have hbi := b65x_witness_box p hp i
    rw [hi] at hbi
    have hc' : ((b65b_boxCentre (b65x_boxInv j)).2 : ℝ) = 0 := by exact_mod_cast hc
    have hk := b65x_box_unique hbi.1 hbi.2.1
      (by simpa using hb.1) (by simpa [hc'] using hb.2.1)
    have hij : i = j := by
      have h2 := congrArg b65b_boxIndex hk
      rwa [b65x_boxIndex_boxInv, b65x_boxIndex_boxInv] at h2
    subst hij
    have := congrArg Complex.im hi
    simp at this
    linarith

theorem b65x_witness_real10 : p 10 = ((p 10).re : ℂ) := by
  apply Complex.ext <;> simp [b65x_witness_real p hp 10 (by norm_num [b65x_boxInv, b65b_boxCentre])]

theorem b65x_witness_real11 : p 11 = ((p 11).re : ℂ) := by
  apply Complex.ext <;> simp [b65x_witness_real p hp 11 (by norm_num [b65x_boxInv, b65b_boxCentre])]

/-- The normalized witnesses lie in the certified open lasso discs. -/
theorem b65x_witness_disc (j : Fin 12) :
    ‖b65s_normalize (p 10) (p 11) (p j) - b65b_track 0 j‖ < (b65b_radius j : ℝ) := by
  have hb := b65x_witness_box p hp j
  have h10 := b65x_witness_box p hp 10
  have h11 := b65x_witness_box p hp 11
  have e := b65b_normalization_enclosure (b65x_boxInv j) (p j) (p 10).re (p 11).re
    hb.1.le hb.2.1.le (by simpa [b65x_boxInv] using h10.1.le)
    (by simpa [b65x_boxInv] using h11.1.le)
  rw [b65x_boxIndex_boxInv, ← b65x_witness_real10 p hp, ← b65x_witness_real11 p hp] at e
  exact e.2.2.2

end Witness

end HodgeLean.Foundations.Program
