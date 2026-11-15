import HodgeLean.Foundations.Program.SchoenCycleAffineLinearIdeal

/-! # Reduced polynomial equations of degree at most one -/
noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Every complex polynomial of total degree at most one generates a radical ideal, including constant equations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, I.1. -/
theorem s2e_linear_polynomial_span_isRadical {σ : Type*}
    (F : MvPolynomial σ ℂ) (hF : F.totalDegree ≤ 1) :
    (Ideal.span ({F} : Set (MvPolynomial σ ℂ))).IsRadical := by
  classical
  by_cases hzero : F.totalDegree = 0
  · obtain ⟨c, rfl⟩ : ∃ c, F = C c := ⟨F.coeff 0, totalDegree_eq_zero_iff_eq_C.mp hzero⟩
    by_cases hc : c = 0
    · subst c
      simpa using (Ideal.isRadical_bot : (⊥ : Ideal (MvPolynomial σ ℂ)).IsRadical)
    · rw [Ideal.span_singleton_eq_top.mpr ((isUnit_iff_ne_zero.mpr hc).map C)]
      exact fun _ _ => Submodule.mem_top
  · have hdeg : F.totalDegree = 1 := by omega
    have hirr : Irreducible F := by
      apply irreducible_of_totalDegree_eq_one hdeg
      intro r hr
      apply isUnit_iff_ne_zero.mpr
      intro hrzero
      have hFzero : F = 0 := by
        ext d
        simpa [hrzero, zero_dvd_iff] using hr d
      simpa [hFzero] using hdeg
    exact ((Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime).isRadical

end HodgeLean.Foundations.Program
