import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteRootTriviality

/-! Euclidean coordinate transport for plane polynomial families.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Separate the last coordinate of a plane family over a specified base subset.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, plane coordinate transport step. -/
def s2v_t11b_planeFamilyBaseChart (F : ℝ → ℝ → ℝ) (K : Set ℝ) :
    {y : EuclideanSpace ℝ (Fin 2) | F (y 1) (y 0) = 0 ∧ y 1 ∈ K} ≃ₜ
      {z : K × ℝ | F z.1.val z.2 = 0} where
  toFun y := ⟨(⟨y.val 1, y.property.2⟩, y.val 0), y.property.1⟩
  invFun z := ⟨WithLp.toLp 2 ![z.val.2, z.val.1.val], z.property, z.val.1.property⟩
  left_inv y := by
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
      continuous_subtype_val).subtype_mk _).prodMk
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_snd.comp continuous_subtype_val
    · exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)

/-- A plane family's actual coordinate fiber is its real root space at that value.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, plane coordinate transport step. -/
def s2v_t11b_planeFamilyFiberChart (F : ℝ → ℝ → ℝ) (b : ℝ) :
    {y : EuclideanSpace ℝ (Fin 2) | F (y 1) (y 0) = 0 ∧ y 1 = b} ≃ₜ
      {x : ℝ | F b x = 0} where
  toFun y := ⟨y.val 0, by
    exact (congrArg (fun t => F t (y.val 0)) y.property.2).symm.trans y.property.1⟩
  invFun x := ⟨WithLp.toLp 2 ![x.val, b], x.property, rfl⟩
  left_inv y := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · exact y.property.2.symm
  right_inv _ := rfl
  continuous_toFun := ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_subtype_val
    · exact continuous_const

end HodgeLean.Foundations.Program
