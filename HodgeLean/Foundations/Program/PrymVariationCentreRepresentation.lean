import HodgeLean.Foundations.Program.PrymVariationCentreChevalleyWeil

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- The printed four dimensional representation on column vectors.
Source: G32 v0.16, Appendix A; Serre, §1.1. -/
def b63d_naturalRep : Representation ℂ b4b_Group (Fin 4 → ℂ) where
  toFun g := Matrix.toLin' (b4b_toMatrix g)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.toLin'_mul]; rfl

example (g : b4b_Group) (v : Fin 4 → ℂ) :
    b63d_naturalRep g v = (b4b_toMatrix g).mulVec v := rfl

theorem b63d_naturalRep_scalar (v : Fin 4 → ℂ) :
    b63d_naturalRep b63d_scalarElement v = g32h_omega • v := by
  change Matrix.toLin' (b4b_toMatrix b63d_scalarElement) v = _
  rw [b63d_scalarElement_matrix, map_smul, Matrix.toLin'_one]
  rfl

theorem b63d_omega_ne_one : g32h_omega ≠ 1 := by
  intro h
  have hw := g32h_omega_sq_add
  rw [h] at hw
  norm_num at hw

theorem b63d_naturalRep_nontrivial :
    ∃ (g : b4b_Group) (v : Fin 4 → ℂ), b63d_naturalRep g v ≠ v := by
  refine ⟨b63d_scalarElement, fun _ ↦ 1, ?_⟩
  rw [b63d_naturalRep_scalar]
  intro h
  apply b63d_omega_ne_one
  simpa using congrFun h 0

theorem b63d_naturalRep_finrank : Module.finrank ℂ (Fin 4 → ℂ) = 4 := by simp

theorem b63d_conjugateRep_nontrivial :
    ∃ (g : b4b_Group) (v : HurwitzPrymRex_Bar (Fin 4 → ℂ)),
      HurwitzPrymRex_barRep b63d_naturalRep g v ≠ v :=
  HurwitzPrymRex_barRep_nontrivial _ b63d_naturalRep_nontrivial

theorem b63d_conjugateRep_finrank :
    Module.finrank ℂ (HurwitzPrymRex_Bar (Fin 4 → ℂ)) = 4 := by
  rw [HurwitzPrymRex_Bar.finrank_eq, b63d_naturalRep_finrank]

theorem b63d_conjugateRep_scalar (v : HurwitzPrymRex_Bar (Fin 4 → ℂ)) :
    HurwitzPrymRex_barRep b63d_naturalRep b63d_scalarElement v =
      star g32h_omega • v := by
  apply HurwitzPrymRex_Bar.ext
  change b63d_naturalRep b63d_scalarElement v.val = _
  rw [b63d_naturalRep_scalar]
  simp only [HurwitzPrymRex_Bar.val_smul, starRingEnd_apply, star_star]

end HodgeLean.Foundations.Program
