import HodgeLean.Foundations.Program.ParabolicCohomologyDefs

/-! # The G32 root over `K = ℚ(√−3)` as explicit matrices

The thirteen entries of `hp_rootTupleK`, their partial products and rank certificates, written as
explicit matrices over `K` (entries `⟨re, im⟩` for `re + im·√−3`), and the exact identities about
them, each checked by evaluation in the kernel (`decide +kernel`). Matrix inverses are replaced by
explicit inverses checked by `Matrix.inv_eq_left_inv`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Matrix

namespace HodgeLean.Foundations.Program

/-- The thirteen entries of `hp_rootTupleK` as explicit matrices over `K`, entries `⟨re, im⟩`
for `re + im·√−3`. -/
def hp_TKlit : Fin 13 → Matrix (Fin 4) (Fin 4) hp_K :=
  ![!![⟨1/2, 1/6⟩, ⟨0, 1/3⟩, 0, ⟨0, -1/3⟩;
    ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩;
    0, 0, 1, 0;
    ⟨1/2, 1/6⟩, ⟨1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩],
    !![⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩;
    ⟨0, -1/3⟩, ⟨1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩;
    0, 0, 1, 0;
    ⟨0, 1/3⟩, ⟨1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩],
    !![⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩, 0;
    ⟨0, -1/3⟩, ⟨1/2, 1/6⟩, ⟨-1/2, 1/6⟩, 0;
    ⟨0, -1/3⟩, ⟨-1/2, 1/6⟩, ⟨1/2, 1/6⟩, 0;
    0, 0, 0, 1],
    !![⟨1/2, -1/6⟩, ⟨0, 1/3⟩, ⟨0, 1/3⟩, 0;
    ⟨1/2, -1/6⟩, ⟨1/2, -1/6⟩, ⟨-1/2, -1/6⟩, 0;
    ⟨1/2, -1/6⟩, ⟨-1/2, -1/6⟩, ⟨1/2, -1/6⟩, 0;
    0, 0, 0, 1],
    !![⟨1/2, 1/6⟩, ⟨0, 1/3⟩, 0, ⟨1/2, 1/6⟩;
    ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, 0, ⟨0, 1/3⟩;
    0, 0, 1, 0;
    ⟨0, -1/3⟩, ⟨-1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩],
    !![⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩, 0, ⟨0, 1/3⟩;
    ⟨0, -1/3⟩, ⟨1/2, -1/6⟩, 0, ⟨-1/2, 1/6⟩;
    0, 0, 1, 0;
    ⟨1/2, -1/6⟩, ⟨0, -1/3⟩, 0, ⟨1/2, -1/6⟩],
    !![⟨1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩, ⟨-1/2, -1/6⟩;
    0, 1, 0, 0;
    ⟨1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩;
    ⟨0, 1/3⟩, 0, ⟨0, -1/3⟩, ⟨1/2, 1/6⟩],
    !![⟨1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩, ⟨0, -1/3⟩;
    0, 1, 0, 0;
    ⟨1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩, ⟨0, 1/3⟩;
    ⟨-1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩, ⟨1/2, -1/6⟩],
    !![1, 0, 0, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨-1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, ⟨-1/2, -1/6⟩;
    0, ⟨-1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨1/2, 1/6⟩],
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, ⟨-1/2, -1/2⟩],
    !![1, 0, 0, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩;
    0, ⟨0, -1/3⟩, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩],
    !![1, 0, 0, 0;
    0, ⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩, ⟨1/2, -1/6⟩;
    0, ⟨0, -1/3⟩, ⟨1/2, -1/6⟩, ⟨1/2, 1/6⟩;
    0, ⟨0, 1/3⟩, ⟨1/2, 1/6⟩, ⟨1/2, -1/6⟩],
    !![1, 0, 0, 0;
    0, 0, ⟨-1/2, 1/2⟩, 0;
    0, ⟨-1/2, -1/2⟩, 0, 0;
    0, 0, 0, ⟨-1, 0⟩]]

theorem hp_wordInv_2 :
    ((List.map (hp_genOver pc_zeta) [2]).prod)⁻¹ =
    !![⟨-1, 0⟩, 0, 0, 0;
    0, ⟨-1/2, 1/6⟩, ⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩;
    0, ⟨0, 1/3⟩, ⟨-1/2, 1/6⟩, ⟨-1/2, -1/6⟩;
    0, ⟨1/2, 1/6⟩, ⟨1/2, -1/6⟩, ⟨0, -1/3⟩] :=
  Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_reflK_2 :
    hp_reflOver pc_zeta [2] =
    !![⟨1/2, 1/6⟩, ⟨0, 1/3⟩, 0, ⟨1/2, 1/6⟩;
    ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, 0, ⟨0, 1/3⟩;
    0, 0, 1, 0;
    ⟨0, -1/3⟩, ⟨-1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩] := by
  simp only [hp_reflOver]
  rw [hp_wordInv_2]
  decide +kernel

theorem hp_wordInv_3 :
    ((List.map (hp_genOver pc_zeta) [3]).prod)⁻¹ =
    !![⟨-1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨-1/2, 1/6⟩, ⟨1/2, -1/6⟩;
    ⟨-1/2, 1/6⟩, ⟨1/2, 1/6⟩, ⟨-1/2, 1/6⟩, 0;
    ⟨-1/2, 1/6⟩, ⟨-1/2, -1/6⟩, 0, ⟨-1/2, 1/6⟩] :=
  Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_reflK_3 :
    hp_reflOver pc_zeta [3] =
    !![⟨1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩, ⟨-1/2, -1/6⟩;
    0, 1, 0, 0;
    ⟨1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩;
    ⟨0, 1/3⟩, 0, ⟨0, -1/3⟩, ⟨1/2, 1/6⟩] := by
  simp only [hp_reflOver]
  rw [hp_wordInv_3]
  decide +kernel

theorem hp_wordInv_131 :
    ((List.map (hp_genOver pc_zeta) [1, 3, 1]).prod)⁻¹ =
    !![0, ⟨0, -1/3⟩, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩;
    ⟨-1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩, ⟨1/2, -1/6⟩;
    ⟨-1/2, -1/6⟩, ⟨0, 1/3⟩, ⟨-1/2, -1/6⟩, 0;
    ⟨-1/2, 1/6⟩, ⟨-1/2, -1/6⟩, 0, ⟨-1/2, 1/6⟩] :=
  Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_reflK_131 :
    hp_reflOver pc_zeta [1, 3, 1] =
    !![1, 0, 0, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨-1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, ⟨-1/2, -1/6⟩;
    0, ⟨-1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨1/2, 1/6⟩] := by
  simp only [hp_reflOver]
  rw [hp_wordInv_131]
  decide +kernel

theorem hp_wordInv_002 :
    ((List.map (hp_genOver pc_zeta) [0, 0, 2]).prod)⁻¹ =
    !![⟨-1/2, -1/6⟩, ⟨0, -1/3⟩, 0, ⟨0, 1/3⟩;
    0, ⟨-1/2, 1/6⟩, ⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩;
    ⟨0, -1/3⟩, ⟨-1/2, 1/6⟩, ⟨-1/2, 1/6⟩, 0;
    ⟨0, -1/3⟩, 0, ⟨1/2, -1/6⟩, ⟨1/2, -1/6⟩] :=
  Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_reflK_002 :
    hp_reflOver pc_zeta [0, 0, 2] =
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, ⟨-1/2, 1/2⟩] := by
  simp only [hp_reflOver]
  rw [hp_wordInv_002]
  decide +kernel

theorem hp_wordInv_32 :
    ((List.map (hp_genOver pc_zeta) [3, 2]).prod)⁻¹ =
    !![⟨1/2, 1/6⟩, 0, ⟨-1/2, -1/6⟩, ⟨-1/2, -1/6⟩;
    0, 1, 0, 0;
    ⟨1/2, -1/6⟩, 0, ⟨0, -1/3⟩, ⟨1/2, 1/6⟩;
    ⟨0, 1/3⟩, 0, ⟨-1/2, 1/6⟩, ⟨1/2, 1/6⟩] :=
  Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_reflK_32 :
    hp_reflOver pc_zeta [3, 2] =
    !![1, 0, 0, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩;
    0, ⟨0, -1/3⟩, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩] := by
  simp only [hp_reflOver]
  rw [hp_wordInv_32]
  decide +kernel

theorem hp_wordInv_321 :
    ((List.map (hp_genOver pc_zeta) [3, 2, 1]).prod)⁻¹ =
    !![⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩, ⟨0, -1/3⟩, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨-1/2, 1/6⟩;
    ⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩, 0, ⟨0, 1/3⟩;
    ⟨0, 1/3⟩, 0, ⟨-1/2, 1/6⟩, ⟨1/2, 1/6⟩] :=
  Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_reflK_321 :
    hp_reflOver pc_zeta [3, 2, 1] =
    !![1, 0, 0, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨0, -1/3⟩;
    0, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, ⟨1/2, -1/6⟩;
    0, ⟨1/2, 1/6⟩, ⟨1/2, -1/6⟩, ⟨1/2, 1/6⟩] := by
  simp only [hp_reflOver]
  rw [hp_wordInv_321]
  decide +kernel

theorem hp_rootTupleK_eq_0 : hp_rootTupleK 0 = hp_TKlit 0 := by
  decide +kernel

theorem hp_rootTupleK_eq_1 : hp_rootTupleK 1 = hp_TKlit 1 := by
  change (HodgeLean.Papers.g32R1 pc_zeta)⁻¹ = _
  exact Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_rootTupleK_eq_2 : hp_rootTupleK 2 = hp_TKlit 2 := by
  change (HodgeLean.Papers.g32R2 pc_zeta)⁻¹ = _
  exact Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_rootTupleK_eq_3 : hp_rootTupleK 3 = hp_TKlit 3 := by
  decide +kernel

theorem hp_rootTupleK_eq_4 : hp_rootTupleK 4 = hp_TKlit 4 := by
  exact hp_reflK_2

theorem hp_rootTupleK_eq_5 : hp_rootTupleK 5 = hp_TKlit 5 := by
  change (hp_reflOver pc_zeta [2])⁻¹ = _
  rw [hp_reflK_2]
  exact Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_rootTupleK_eq_6 : hp_rootTupleK 6 = hp_TKlit 6 := by
  exact hp_reflK_3

theorem hp_rootTupleK_eq_7 : hp_rootTupleK 7 = hp_TKlit 7 := by
  change (hp_reflOver pc_zeta [3])⁻¹ = _
  rw [hp_reflK_3]
  exact Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_rootTupleK_eq_8 : hp_rootTupleK 8 = hp_TKlit 8 := by
  exact hp_reflK_131

theorem hp_rootTupleK_eq_9 : hp_rootTupleK 9 = hp_TKlit 9 := by
  change (hp_reflOver pc_zeta [0, 0, 2])⁻¹ = _
  rw [hp_reflK_002]
  exact Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_rootTupleK_eq_10 : hp_rootTupleK 10 = hp_TKlit 10 := by
  exact hp_reflK_32

theorem hp_rootTupleK_eq_11 : hp_rootTupleK 11 = hp_TKlit 11 := by
  change (hp_reflOver pc_zeta [3, 2, 1])⁻¹ = _
  rw [hp_reflK_321]
  exact Matrix.inv_eq_left_inv (by decide +kernel)

theorem hp_rootTupleK_eq_12 : hp_rootTupleK 12 = hp_TKlit 12 := by
  decide +kernel

theorem hp_rootTupleK_eq : hp_rootTupleK = hp_TKlit := by
  funext j
  fin_cases j
  · exact hp_rootTupleK_eq_0
  · exact hp_rootTupleK_eq_1
  · exact hp_rootTupleK_eq_2
  · exact hp_rootTupleK_eq_3
  · exact hp_rootTupleK_eq_4
  · exact hp_rootTupleK_eq_5
  · exact hp_rootTupleK_eq_6
  · exact hp_rootTupleK_eq_7
  · exact hp_rootTupleK_eq_8
  · exact hp_rootTupleK_eq_9
  · exact hp_rootTupleK_eq_10
  · exact hp_rootTupleK_eq_11
  · exact hp_rootTupleK_eq_12

/-- The partial products `Q_i` of `hp_TKlit` as explicit matrices. -/
def hp_QKlit : Fin 13 → Matrix (Fin 4) (Fin 4) hp_K :=
  ![!![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![⟨1/2, 1/6⟩, ⟨0, 1/3⟩, 0, ⟨0, -1/3⟩;
    ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩;
    0, 0, 1, 0;
    ⟨1/2, 1/6⟩, ⟨1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩],
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩, 0;
    ⟨0, -1/3⟩, ⟨1/2, 1/6⟩, ⟨-1/2, 1/6⟩, 0;
    ⟨0, -1/3⟩, ⟨-1/2, 1/6⟩, ⟨1/2, 1/6⟩, 0;
    0, 0, 0, 1],
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![⟨1/2, 1/6⟩, ⟨0, 1/3⟩, 0, ⟨1/2, 1/6⟩;
    ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, 0, ⟨0, 1/3⟩;
    0, 0, 1, 0;
    ⟨0, -1/3⟩, ⟨-1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩],
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![⟨1/2, 1/6⟩, 0, ⟨1/2, -1/6⟩, ⟨-1/2, -1/6⟩;
    0, 1, 0, 0;
    ⟨1/2, -1/6⟩, 0, ⟨1/2, 1/6⟩, ⟨1/2, 1/6⟩;
    ⟨0, 1/3⟩, 0, ⟨0, -1/3⟩, ⟨1/2, 1/6⟩],
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![1, 0, 0, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨-1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, ⟨-1/2, -1/6⟩;
    0, ⟨-1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨1/2, 1/6⟩],
    !![1, 0, 0, 0;
    0, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨1/2, 1/6⟩, ⟨0, 1/3⟩;
    0, ⟨-1/2, 1/6⟩, ⟨0, 1/3⟩, ⟨0, -1/3⟩],
    !![1, 0, 0, 0;
    0, ⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩, ⟨0, 1/3⟩;
    0, ⟨0, -1/3⟩, ⟨1/2, -1/6⟩, ⟨-1/2, 1/6⟩;
    0, ⟨-1/2, -1/6⟩, ⟨-1/2, 1/6⟩, ⟨-1/2, -1/6⟩],
    !![1, 0, 0, 0;
    0, 0, ⟨-1/2, 1/2⟩, 0;
    0, ⟨-1/2, -1/2⟩, 0, 0;
    0, 0, 0, ⟨-1, 0⟩]]

theorem hp_QKlit_eq : ∀ i, pc_Q hp_TKlit i = hp_QKlit i := by decide +kernel

theorem hp_TKlit_prod : (List.ofFn hp_TKlit).prod = 1 := by decide +kernel

theorem hp_TKlit_unitary : ∀ j, (hp_TKlit j)ᴴ * 1 * hp_TKlit j = 1 := by decide +kernel

theorem hp_TKlit_mem : ∀ a, pc_relation hp_TKlit (hp_certK a) = 0 := by decide +kernel

theorem hp_TKlit_gram_0 : ∀ b, (1 + 2 * pc_zeta) *
    pc_SInvFree hp_TKlit 1 (hp_certK 0) (hp_certK b) = HodgeLean.Papers.g32H0 pc_zeta 0 b := by
  simp only [pc_SInvFree, pc_F, hp_QKlit_eq]
  decide +kernel

theorem hp_TKlit_gram_1 : ∀ b, (1 + 2 * pc_zeta) *
    pc_SInvFree hp_TKlit 1 (hp_certK 1) (hp_certK b) = HodgeLean.Papers.g32H0 pc_zeta 1 b := by
  simp only [pc_SInvFree, pc_F, hp_QKlit_eq]
  decide +kernel

theorem hp_TKlit_gram_2 : ∀ b, (1 + 2 * pc_zeta) *
    pc_SInvFree hp_TKlit 1 (hp_certK 2) (hp_certK b) = HodgeLean.Papers.g32H0 pc_zeta 2 b := by
  simp only [pc_SInvFree, pc_F, hp_QKlit_eq]
  decide +kernel

theorem hp_TKlit_gram_3 : ∀ b, (1 + 2 * pc_zeta) *
    pc_SInvFree hp_TKlit 1 (hp_certK 3) (hp_certK b) = HodgeLean.Papers.g32H0 pc_zeta 3 b := by
  simp only [pc_SInvFree, pc_F, hp_QKlit_eq]
  decide +kernel

theorem hp_TKlit_gram_4 : ∀ b, (1 + 2 * pc_zeta) *
    pc_SInvFree hp_TKlit 1 (hp_certK 4) (hp_certK b) = HodgeLean.Papers.g32H0 pc_zeta 4 b := by
  simp only [pc_SInvFree, pc_F, hp_QKlit_eq]
  decide +kernel

theorem hp_TKlit_gram_5 : ∀ b, (1 + 2 * pc_zeta) *
    pc_SInvFree hp_TKlit 1 (hp_certK 5) (hp_certK b) = HodgeLean.Papers.g32H0 pc_zeta 5 b := by
  simp only [pc_SInvFree, pc_F, hp_QKlit_eq]
  decide +kernel

theorem hp_TKlit_gram (a b : Fin 6) : (1 + 2 * pc_zeta) *
    pc_SInvFree hp_TKlit 1 (hp_certK a) (hp_certK b) = HodgeLean.Papers.g32H0 pc_zeta a b := by
  fin_cases a
  · exact hp_TKlit_gram_0 b
  · exact hp_TKlit_gram_1 b
  · exact hp_TKlit_gram_2 b
  · exact hp_TKlit_gram_3 b
  · exact hp_TKlit_gram_4 b
  · exact hp_TKlit_gram_5 b

/-- Kernel bases `B_j` of `T_j − 1` over `K`, for the twelve reflections. -/
def hp_kerB : Fin 12 → Matrix (Fin 4) (Fin 3) hp_K :=
  ![!![⟨-1/2, 1/2⟩, 0, ⟨1/2, -1/2⟩;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![⟨-1/2, 1/2⟩, 0, ⟨1/2, -1/2⟩;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![⟨1/2, 1/2⟩, ⟨1/2, 1/2⟩, 0;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![⟨1/2, 1/2⟩, ⟨1/2, 1/2⟩, 0;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![⟨-1/2, 1/2⟩, 0, ⟨1/2, 1/2⟩;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![⟨-1/2, 1/2⟩, 0, ⟨1/2, 1/2⟩;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![0, 1, ⟨-1/2, -1/2⟩;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![0, 1, ⟨-1/2, -1/2⟩;
    1, 0, 0;
    0, 1, 0;
    0, 0, 1],
    !![1, 0, 0;
    0, ⟨-1/2, 1/2⟩, ⟨-1, 0⟩;
    0, 1, 0;
    0, 0, 1],
    !![1, 0, 0;
    0, 1, 0;
    0, 0, 1;
    0, 0, 0],
    !![1, 0, 0;
    0, ⟨-1/2, 1/2⟩, ⟨1/2, 1/2⟩;
    0, 1, 0;
    0, 0, 1],
    !![1, 0, 0;
    0, ⟨-1/2, 1/2⟩, ⟨1/2, -1/2⟩;
    0, 1, 0;
    0, 0, 1]]

/-- Left inverses `C_j` of the kernel bases (`C_j B_j = 1`). -/
def hp_kerC : Fin 12 → Matrix (Fin 3) (Fin 4) hp_K :=
  ![!![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![1, 0, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0],
    !![1, 0, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1],
    !![1, 0, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1]]

/-- Complements `M_j` with `B_j C_j + M_j (T_j − 1) = 1`. -/
def hp_kerM : Fin 12 → Matrix (Fin 4) (Fin 4) hp_K :=
  ![!![⟨-3/2, -1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-3/2, 1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-3/2, -1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-3/2, 1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-3/2, -1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-3/2, 1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-3/2, -1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-3/2, 1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, ⟨-3/2, -1/2⟩, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, ⟨-1/2, 1/6⟩],
    !![0, 0, 0, 0;
    0, ⟨-3/2, -1/2⟩, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, ⟨-3/2, 1/2⟩, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]]

/-- The kernel basis of `T₁₃ − 1` (`x² − 1`). -/
def hp_kerB12 : Matrix (Fin 4) (Fin 2) hp_K :=
  !![1, 0;
    0, ⟨-1/2, 1/2⟩;
    0, 1;
    0, 0]

/-- Its left inverse. -/
def hp_kerC12 : Matrix (Fin 2) (Fin 4) hp_K :=
  !![1, 0, 0, 0;
    0, 0, 1, 0]

/-- Its complement. -/
def hp_kerM12 : Matrix (Fin 4) (Fin 4) hp_K :=
  !![0, 0, 0, 0;
    0, ⟨-1, 0⟩, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, ⟨-1/2, 0⟩]

/-- Coefficients `L_j` with `Σ_j L_j (T_j − 1) = 1` over `j ∈ {0, 2, 4, 8}`. -/
def hp_fixL : Fin 4 → Matrix (Fin 4) (Fin 4) hp_K :=
  ![!![0, 0, 0, 0;
    ⟨-1/2, -1/2⟩, 0, 0, 0;
    ⟨1/2, 1/2⟩, 0, 0, 0;
    ⟨-1/2, 1/2⟩, 0, 0, 0],
    !![⟨-1, 0⟩, 0, 0, 0;
    ⟨1/2, 1/2⟩, 0, 0, 0;
    ⟨1/2, -1/2⟩, 0, 0, 0;
    0, 0, 0, 0],
    !![⟨-1/2, -1/2⟩, 0, 0, 0;
    0, 0, 0, 0;
    ⟨-1, 0⟩, 0, 0, 0;
    ⟨1/2, -1/2⟩, 0, 0, 0],
    !![0, ⟨1/2, -1/2⟩, 0, 0;
    0, ⟨-1, 0⟩, 0, 0;
    0, ⟨1/2, -1/2⟩, 0, 0;
    0, 0, 0, 0]]

theorem hp_ker_cert : ∀ j : Fin 12, (hp_TKlit j.castSucc - 1) * hp_kerB j = 0 ∧
    hp_kerC j * hp_kerB j = 1 ∧
    hp_kerB j * hp_kerC j + hp_kerM j * (hp_TKlit j.castSucc - 1) = 1 := by decide +kernel

theorem hp_ker_cert12 : (hp_TKlit 12 - 1) * hp_kerB12 = 0 ∧ hp_kerC12 * hp_kerB12 = 1 ∧
    hp_kerB12 * hp_kerC12 + hp_kerM12 * (hp_TKlit 12 - 1) = 1 := by decide +kernel

theorem hp_fix_cert :
    ∑ k : Fin 4, hp_fixL k * (hp_TKlit (![0, 2, 4, 8] k) - 1) = 1 := by decide +kernel

theorem hp_zeta_sq_add : pc_zeta ^ 2 + pc_zeta + 1 = 0 := by decide +kernel

end HodgeLean.Foundations.Program
