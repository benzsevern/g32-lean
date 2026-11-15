import HodgeLean.Foundations.Program.PrymParabolicIntersectionWindowSpecs

set_option linter.unusedSectionVars false

noncomputable section
open Set Complex
namespace HodgeLean.Foundations.Program

/-! ## Table data -/

theorem hga_mr_pos_eq (j : Fin 12) : mr_pos j = hg5_markRe j := by
  fin_cases j <;> norm_num [mr_pos, mr_int, hg5_markRe]

theorem hga_mark_waist_gap (i : Fin 13) (j : Fin 12) : 1 / 2 ≤ |hg5_markRe j - hg3_waist i| := by
  rw [abs_sub_comm, ← hga_mr_pos_eq]
  exact hg3_waist_gap i j

theorem hga_mark_bound (j : Fin 12) : |hg5_markRe j + 11 / 2| ≤ 7 := by
  obtain ⟨h0, h1⟩ := hg5_markRe_bounds j
  rw [abs_le]; constructor <;> linarith

theorem hga_finRotate_lt (i : Fin 13) (h : i.val < 12) : (finRotate 13 i).val = i.val + 1 := by
  rw [finRotate_of_lt h]

theorem hga_finRotate_symm_val (i : Fin 13) (h : i ≠ 0) :
    ((finRotate 13).symm i).val = i.val - 1 := by
  have h1 : (finRotate 13).symm i ≠ Fin.last 12 := by
    intro he
    apply h
    have := congrArg (finRotate 13) he
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    decide
  have h2 := coe_finRotate_of_ne_last h1
  rw [Equiv.apply_symm_apply] at h2
  omega

theorem hga_waist_A12 : 2 * (hg3_waist 12 + 11 / 2) = 14 := by norm_num [hg3_waist]

theorem hga_waist_B12 : 2 * (hg3_waist 0 + 11 / 2) = -14 := by norm_num [hg3_waist]

theorem hga_triA12 (a : Convexity.StdSimplex ℝ (Fin 3)) :
    hg5_tri (Sum.inl (12, ())) a = hg5_chartInv (hg5_coneFun 14 a) := by
  change hg5_triA 12 a = _
  rw [hg5_triA_12, hg5_cone_apply, hga_waist_A12]

theorem hga_triB12 (a : Convexity.StdSimplex ℝ (Fin 3)) :
    hg5_tri (Sum.inr (12, ())) a = hg5_chartInv (hg5_coneFun (-14) a) := by
  change hg5_triB 12 a = _
  rw [hg5_triB_12, hg5_cone_apply, hga_waist_B12]

/-! ## The window data of each base edge -/

/-- Window data on the base edge `e_i`.
Source: `hga_specE`, `hga_specEc`. -/
def hga_specOfE (i : Fin 13) : hga_WindowSpec :=
  if h : i.val < 12 then
    hga_specE (Sum.inr (i, ())) (Sum.inl (i, ())) (hg3_waist (finRotate 13 i)) (hg3_waist i)
      (hg5_markRe ⟨i.val, h⟩) (fun a ↦ hg5_triB_lt i h a) (fun a ↦ hg5_triA_lt i h a)
      (hg3_waist_bound _) (hg3_waist_bound _) (hga_mark_bound _)
      (hga_mark_waist_gap _ _) (hga_mark_waist_gap _ _)
      (hg5_mark_lt_waist _ _ (by rw [hga_finRotate_lt i h]; simp))
      (hg5_waist_lt_mark _ _ (by simp))
  else
    have hi : i = 12 := Fin.ext (by have := i.isLt; simp at h ⊢; omega)
    hga_specEc (Sum.inr (i, ())) (Sum.inl (i, ())) (fun a ↦ by rw [hi]; exact hga_triA12 a)
      (hga_coneRayE_path _ (-14) 1 (fun a ↦ by rw [hi]; exact hga_triB12 a) (by norm_num)
        (Or.inl rfl) (by norm_num))
      (hga_coneRayE_path _ 14 (-1) (fun a ↦ by rw [hi]; exact hga_triA12 a) (by norm_num)
        (Or.inr rfl) (by norm_num))

/-- Window data on the base edge `h_i`.
Source: `hga_specH`, `hga_specHc`. -/
def hga_specOfH (i : Fin 13) : hga_WindowSpec :=
  if h : i.val < 12 then
    hga_specH (Sum.inr (i, ())) (Sum.inl (i, ())) (hg3_waist (finRotate 13 i)) (hg3_waist i)
      (hg5_markRe ⟨i.val, h⟩) (fun a ↦ hg5_triB_lt i h a) (fun a ↦ hg5_triA_lt i h a)
      (hg3_waist_bound _) (hg3_waist_bound _) (hga_mark_bound _)
      (hga_mark_waist_gap _ _) (hga_mark_waist_gap _ _)
      (hg5_mark_lt_waist _ _ (by rw [hga_finRotate_lt i h]; simp))
      (hg5_waist_lt_mark _ _ (by simp))
  else
    have hi : i = 12 := Fin.ext (by have := i.isLt; simp at h ⊢; omega)
    hga_specHc (Sum.inr (i, ())) (Sum.inl (i, ())) (fun a ↦ by rw [hi]; exact hga_triA12 a)
      (hga_coneRayH_path _ (-14) 1 (fun a ↦ by rw [hi]; exact hga_triB12 a) (by norm_num)
        (Or.inl rfl) (by norm_num))
      (hga_coneRayH_path _ 14 (-1) (fun a ↦ by rw [hi]; exact hga_triA12 a) (by norm_num)
        (Or.inr rfl) (by norm_num))

theorem hga_rot_symm_ne_12 (i : Fin 13) (h0 : i ≠ 0) : ((finRotate 13).symm i).val < 12 := by
  rw [hga_finRotate_symm_val i h0]
  have := i.isLt
  omega

theorem hga_rot_symm_0 : (finRotate 13).symm 0 = 12 := by decide

theorem hga_rot_rot_symm (i : Fin 13) : finRotate 13 ((finRotate 13).symm i) = i :=
  Equiv.apply_symm_apply _ _

/-- Window data on the base arc `f_i`.
Source: `hga_specF`, `hga_rayF_path`, `hga_coneRayF_path`. -/
def hga_specOfF (i : Fin 13) : hga_WindowSpec :=
  if h0 : i = 0 then
    have hlt : i.val < 12 := by rw [h0]; decide
    hga_specF (Sum.inl (i, ())) (Sum.inr ((finRotate 13).symm i, ())) (Sum.inl (i, ()))
      (hg3_waist i) (hg5_markRe ⟨i.val, hlt⟩) (fun a ↦ hg5_triA_lt i hlt a) (hg3_waist_bound _)
      (hga_rayF_path _ (hg3_waist i) (hg5_markRe ⟨i.val, hlt⟩) 1 (fun a ↦ hg5_triA_lt i hlt a)
        (hg3_waist_bound _) (hga_mark_bound _) (hga_mark_waist_gap _ _) (Or.inl rfl)
        (by rw [one_mul, sub_nonneg]; exact (hg5_waist_lt_mark _ _ (by simp)).le))
      (hga_coneRayF_path _ (hg3_waist i) (-1)
        (fun a ↦ by
          rw [h0, hga_rot_symm_0]
          change hg5_triB 12 a = _
          rw [hg5_triB_12, hg5_cone_apply])
        (by rw [h0]; norm_num [hg3_waist]) (Or.inr rfl) (by rw [h0]; norm_num [hg3_waist]))
  else if h12 : i = 12 then
    have hj : ((finRotate 13).symm i).val < 12 := hga_rot_symm_ne_12 i h0
    have hrot : finRotate 13 ((finRotate 13).symm i) = i := hga_rot_rot_symm i
    hga_specF (Sum.inl (i, ())) (Sum.inr ((finRotate 13).symm i, ()))
      (Sum.inr ((finRotate 13).symm i, ()))
      (hg3_waist i) (hg5_markRe ⟨((finRotate 13).symm i).val, hj⟩)
      (fun a ↦ by
        change hg5_triB _ a = _
        rw [hg5_triB_lt _ hj, hrot])
      (hg3_waist_bound _)
      (hga_coneRayF_path _ (hg3_waist i) 1
        (fun a ↦ by
          rw [h12]
          change hg5_triA 12 a = _
          rw [hg5_triA_12, hg5_cone_apply])
        (by rw [h12]; norm_num [hg3_waist]) (Or.inl rfl) (by rw [h12]; norm_num [hg3_waist]))
      (hga_rayF_path _ (hg3_waist i) (hg5_markRe ⟨((finRotate 13).symm i).val, hj⟩) (-1)
        (fun a ↦ by
          change hg5_triB _ a = _
          rw [hg5_triB_lt _ hj, hrot])
        (hg3_waist_bound _) (hga_mark_bound _) (hga_mark_waist_gap _ _) (Or.inr rfl)
        (by
          have := hg5_mark_lt_waist i ⟨((finRotate 13).symm i).val, hj⟩
            (by rw [hga_finRotate_symm_val i h0]; have := i.isLt; simp; omega)
          linarith))
  else
    have hlt : i.val < 12 := by
      have := i.isLt
      have : i.val ≠ 12 := fun h ↦ h12 (Fin.ext h)
      omega
    have hj : ((finRotate 13).symm i).val < 12 := hga_rot_symm_ne_12 i h0
    have hrot : finRotate 13 ((finRotate 13).symm i) = i := hga_rot_rot_symm i
    hga_specF (Sum.inl (i, ())) (Sum.inr ((finRotate 13).symm i, ())) (Sum.inl (i, ()))
      (hg3_waist i) (hg5_markRe ⟨i.val, hlt⟩) (fun a ↦ hg5_triA_lt i hlt a) (hg3_waist_bound _)
      (hga_rayF_path _ (hg3_waist i) (hg5_markRe ⟨i.val, hlt⟩) 1 (fun a ↦ hg5_triA_lt i hlt a)
        (hg3_waist_bound _) (hga_mark_bound _) (hga_mark_waist_gap _ _) (Or.inl rfl)
        (by rw [one_mul, sub_nonneg]; exact (hg5_waist_lt_mark _ _ (by simp)).le))
      (hga_rayF_path _ (hg3_waist i) (hg5_markRe ⟨((finRotate 13).symm i).val, hj⟩) (-1)
        (fun a ↦ by
          change hg5_triB _ a = _
          rw [hg5_triB_lt _ hj, hrot])
        (hg3_waist_bound _) (hga_mark_bound _) (hga_mark_waist_gap _ _) (Or.inr rfl)
        (by
          have := hg5_mark_lt_waist i ⟨((finRotate 13).symm i).val, hj⟩
            (by rw [hga_finRotate_symm_val i h0]; have := i.isLt; simp; omega)
          linarith))

/-- The window data of a base edge.
Source: `hga_specOfE`, `hga_specOfF`, `hga_specOfH`. -/
def hga_baseSpec : hg2_Edge Unit 13 → hga_WindowSpec
  | Sum.inl (i, _) => hga_specOfE i
  | Sum.inr (Sum.inl (i, _)) => hga_specOfF i
  | Sum.inr (Sum.inr (i, _)) => hga_specOfH i

end HodgeLean.Foundations.Program
