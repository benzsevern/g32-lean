import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.Defs
import HodgeLean.Foundations.Program.RiemannRochDefs

noncomputable section
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

theorem degreeZero_sum_of_surjective {C M : Type} [AddCommGroup M]
    (f : C → M) (p : C) (hp : f p = 0) (hsurj : Function.Surjective (weightedSum f)) (t : M) :
    ∃ D : C →₀ ℤ, b4c_deg D = 0 ∧ weightedSum f D = t := by
  classical
  obtain ⟨D, hD⟩ := hsurj t
  let δ := weightedSum (fun _ : C ↦ (1 : ℤ))
  have hδ (z : C →₀ ℤ) : δ z = b4c_deg z := by
    simp only [δ, weightedSum, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply,
      b4c_deg, zsmul_eq_mul, mul_one, Int.cast_id]
  have hsingle : δ (Finsupp.single p (b4c_deg D)) = b4c_deg D := by
    simp only [δ, weightedSum, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_single,
      zsmul_eq_mul, Int.cast_id, mul_one]
  refine ⟨D - Finsupp.single p (b4c_deg D), ?_, ?_⟩
  · exact (hδ _).symm.trans ((map_sub δ _ _).trans
      ((congrArg₂ (fun a b : ℤ ↦ a - b) (hδ D) hsingle).trans (sub_self _)))
  · have hs : weightedSum f (Finsupp.single p (b4c_deg D)) = 0 := by
      simp only [weightedSum, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_single,
        hp, smul_zero]
    exact (map_sub (weightedSum f) _ _).trans
      ((congrArg₂ (fun a b : M ↦ a - b) hD hs).trans (sub_zero _))

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
