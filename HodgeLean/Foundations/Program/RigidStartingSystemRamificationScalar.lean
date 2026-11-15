import HodgeLean.Foundations.Program.RigidStartingSystemDefs

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65r_logDerivative_power_factor (φ g : ℂ → ℂ) (a z φ' g' : ℂ)
    (e : ℕ) (he : 0 < e) (hz : z ≠ a) (hg0 : g z ≠ 0)
    (hfactor : ∀ w, φ w = (w-a)^e*g w)
    (hφ : HasDerivAt φ φ' z) (hg : HasDerivAt g g' z) :
    φ'/φ z-g'/g z = (e : ℂ)/(z-a) := by
  have hf : φ = (fun w ↦ (w-a)^e*g w) := funext hfactor
  have hprod := (((hasDerivAt_id z).sub_const a).fun_pow e).mul hg
  rw [hf] at hφ
  have hd := hφ.unique hprod
  rw [hd,hfactor z]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  have hw : z-a ≠ 0 := sub_ne_zero.mpr hz
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, mul_one, pow_succ, id_eq]
  field_simp
  ring

end HodgeLean.Foundations.Program
