import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Maps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The actual coefficient-origin ideal over a field is maximal, including the empty index type.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_coefficient_origin_isMaximal
    (k σ : Type*) [Field k] : (idealOfVars σ k).IsMaximal := by
  classical
  have he : idealOfVars σ k = RingHom.ker (constantCoeff : MvPolynomial σ k →+* k) := by
    ext p
    constructor
    · intro hp
      exact (mem_pow_idealOfVars_iff' 1 p).mp (by simpa only [pow_one] using hp) 0 (by simp)
    · intro hp
      rw [← pow_one (idealOfVars σ k)]
      apply (mem_pow_idealOfVars_iff' 1 p).mpr
      intro x hx
      have hd : Finsupp.degree x = 0 := by omega
      have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp hd
      subst x
      exact hp
  rw [he]
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨C c, by simp⟩

#print axioms s2e_coefficient_origin_isMaximal
end HodgeLean.Foundations.Program
