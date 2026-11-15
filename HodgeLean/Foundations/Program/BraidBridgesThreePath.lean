import HodgeLean.Foundations.Program.BraidBridgesTwo
import HodgeLean.Foundations.Program.BraidCertificate
import HodgeLean.Foundations.Program.PrymFamilyExistsDefs

/-! # Endpoint loops of a based family along the certified path

At time one the certified configuration is the list of finite marks of `mr_base`, so a based
family avoiding the moving configuration and infinity ends in loops of `b6t_punctured mr_base`.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- The configuration at time one is the list of finite marks. -/
theorem b65x_configuration_one (p : Fin 12 → ℂ) (j : Fin 12) :
    b65b_configuration p 1 j = mr_marks j := by
  have h : b65b_configuration p 1 j = b65b_track 1 j := by
    norm_num [b65b_configuration]
  rw [h]
  fin_cases j <;>
    simp [b65b_track, b65b_vertex1, mr_marks, mr_base, Fin.append, Fin.addCases] <;> norm_num

/-- A point of the plane off the finite marks lies in the sphere punctured at `mr_base`. -/
theorem b65x_mem_punctured {w : OnePoint ℂ} (hw : w ≠ OnePoint.infty)
    (hm : ∀ j : Fin 12, w ≠ (mr_marks j : OnePoint ℂ)) : w ∈ b6t_punctured mr_base := by
  rintro ⟨k, rfl⟩
  fin_cases k
  exacts [hm 0 rfl, hm 1 rfl, hm 2 rfl, hm 3 rfl, hm 4 rfl, hm 5 rfl, hm 6 rfl, hm 7 rfl,
    hm 8 rfl, hm 9 rfl, hm 10 rfl, hm 11 rfl, hw rfl]

/-- The loop of `b6t_punctured mr_base` traced by the time-one end of a based family that
avoids the configuration and infinity. -/
def b65x_endLoop (p : Fin 12 → ℂ) (K : C(unitInterval × unitInterval, OnePoint ℂ))
    (hKb : ∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ t s, K (t, s) ≠ OnePoint.infty ∧
      ∀ j, K (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) :
    Path b63gP_basePoint b63gP_basePoint where
  toFun s := ⟨K (1, s), b65x_mem_punctured (hKa 1 s).1 fun j ↦ by
    have h := (hKa 1 s).2 j
    rwa [show ((1 : unitInterval) : ℝ) = 1 from rfl, b65x_configuration_one] at h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact K.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  source' := Subtype.ext (hKb 1).1
  target' := Subtype.ext (hKb 1).2

theorem b65x_endLoop_apply (p : Fin 12 → ℂ) (K : C(unitInterval × unitInterval, OnePoint ℂ))
    (hKb : ∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ))
    (hKa : ∀ t s, K (t, s) ≠ OnePoint.infty ∧
      ∀ j, K (t, s) ≠ (b65b_configuration p t j : OnePoint ℂ)) (s : unitInterval) :
    ((b65x_endLoop p K hKb hKa s : b6t_punctured mr_base) : OnePoint ℂ) = K (1, s) := rfl

end HodgeLean.Foundations.Program
