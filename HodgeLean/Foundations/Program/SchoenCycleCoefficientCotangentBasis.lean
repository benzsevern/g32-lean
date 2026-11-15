import HodgeLean.Foundations.Program.SchoenCycleCoefficientLinearization
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual coefficient variables form a basis of the coefficient-origin cotangent module.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_coefficient_origin_cotangent_basis
    {R σ : Type*} [CommRing R] [Fintype σ] :
    ∃ B : Module.Basis σ R (idealOfVars σ R).Cotangent,
      ∀ i, B i = (idealOfVars σ R).toCotangent ⟨X i, Ideal.subset_span ⟨i, rfl⟩⟩ := by
  classical
  let I := idealOfVars σ R
  let v (i : σ) : I := ⟨X i, Ideal.subset_span ⟨i, rfl⟩⟩
  let w (i : σ) := I.toCotangent (v i)
  have hsum (a : σ → R) :
      I.toCotangent (∑ i, a i • v i) = ∑ i, a i • w i := by
    simp only [map_sum, LinearMap.map_smul_of_tower, w]
  have hind : LinearIndependent R w := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hz : I.toCotangent (∑ i, a i • v i) = 0 := (hsum a).trans ha
    have hp := (I.toCotangent_eq_zero _).mp hz
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, v] at hp
    have hc := (mem_pow_idealOfVars_iff' 2 _).mp hp (Finsupp.single i 1) (by simp)
    simpa [coeff_sum, coeff_smul, coeff_X, Finsupp.single_left_inj] using hc
  have hspan : ⊤ ≤ Submodule.span R (Set.range w) := by
    intro z _
    obtain ⟨p, rfl⟩ := I.toCotangent_surjective z
    let a : σ → R := fun i => p.val.coeff (Finsupp.single i 1)
    have hz : I.toCotangent p = ∑ i, a i • w i := by
      rw [← hsum]
      apply I.toCotangent_eq.mpr
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, v]
      simpa only [a, ← C_mul'] using s2e_coefficient_polynomial_linearization p.val p.property
    rw [hz]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  exact ⟨Module.Basis.mk hind hspan, fun i => Module.Basis.mk_apply hind hspan i⟩

#print axioms s2e_coefficient_origin_cotangent_basis
end HodgeLean.Foundations.Program
