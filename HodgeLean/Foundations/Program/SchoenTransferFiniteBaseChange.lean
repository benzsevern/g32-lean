import HodgeLean.Foundations.HodgeLieAlgebra

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Extension to complex coefficients commutes with a finite indexed intersection. -/
theorem s4_baseChange_iInf_fin {V : Type*} [AddCommGroup V] [Module ℚ V]
    (n : ℕ) (U : Fin n → Submodule ℚ V) :
    (⨅ i, U i).baseChange ℂ = ⨅ i, (U i).baseChange ℂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (⨅ i, U i) = U 0 ⊓ ⨅ i : Fin n, U i.succ := by
      ext x
      simp only [Submodule.mem_iInf, Submodule.mem_inf, Fin.forall_fin_succ]
    rw [he, HodgeLean.Foundations.baseChange_inf, ih]
    ext x
    simp only [Submodule.mem_iInf, Submodule.mem_inf, Fin.forall_fin_succ]

/-- Extension to complex coefficients commutes with intersections over a finite type. -/
theorem s4_baseChange_iInf {V I : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype I] (U : I → Submodule ℚ V) :
    (⨅ i, U i).baseChange ℂ = ⨅ i, (U i).baseChange ℂ := by
  let e := Fintype.equivFin I
  calc
    (⨅ i, U i).baseChange ℂ = (⨅ j : Fin (Fintype.card I), U (e.symm j)).baseChange ℂ :=
      congrArg (Submodule.baseChange ℂ) (e.symm.surjective.iInf_comp U).symm
    _ = ⨅ j : Fin (Fintype.card I), (U (e.symm j)).baseChange ℂ := s4_baseChange_iInf_fin _ _
    _ = ⨅ i, (U i).baseChange ℂ := e.symm.surjective.iInf_comp (fun i : I => (U i).baseChange ℂ)

end HodgeLean.Foundations.Program
