import HodgeLean.Foundations.Program.SchoenCycleQuotientSeparation

/-! # Recovery of an effective divisor from a retained quotient lift -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Every actual lift of an effective divisor's quotient value enumerates that divisor with multiplicity.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_retained_quotient_lift_recovers_divisor
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (D : ComplexPoint Z →₀ ℤ) (hD : ∀ p, 0 ≤ D p)
    (hd : b4c_deg D = (n : ℤ)) (x : ComplexPoint (g3_power Z n))
    (hx : s2e_symmetricQuotientEvaluation n γ (s2e_divisorSym D hD hd) = Point.map γ x) :
    D = ∑ i, Finsupp.single (Point.map (g3_proj Z n i) x) (1 : ℤ) := by
  obtain ⟨f, hf, hDf⟩ := (s2e_effectiveDivisor_quotient_eq_iff Z B n γ hγ D hD hd
    (Point.map γ x)).mp hx
  obtain ⟨σ, hσ⟩ := s2e_step1_retained_symmetric_orbits Z B n γ hsurj hγ hquot
    (s2_lift n f) x hf
  change s2_lift n f ≫ s2_permute Z n σ = x at hσ
  rw [s2e_lift_permute] at hσ
  have hcoord (i : Fin n) : Point.map (g3_proj Z n i) x = f (σ.symm i) := by
    have h := congrArg (fun t => t ≫ g3_proj Z n i) hσ
    change x ≫ g3_proj Z n i = f (σ.symm i)
    simpa only [s2_check_lift_proj] using h.symm
  rw [hDf]
  simp_rw [hcoord]
  exact (σ.symm.sum_comp (fun i => Finsupp.single (f i) (1 : ℤ))).symm

#print axioms s2e_retained_quotient_lift_recovers_divisor
end HodgeLean.Foundations.Program
