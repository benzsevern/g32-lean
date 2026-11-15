import HodgeLean.Foundations.Program.G32Native.PairedResidualDivisorPoint
import HodgeLean.Foundations.Program.G32Native.PairedResidualDivisorIndexing

/-! # Actual quotient points indexed by their full divisor multiplicities -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Every point of the supplied point-surjective symmetric quotient has an
ordered lift indexed by its exact effective divisor support and multiplicities.
Source: Schoen, Compositio Mathematica 65 (1988), §2. -/
theorem residual_quotient_point_support_indices
    (Z B : Over (Spec ↧ℂ)) (n : ℕ) (γ : g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hpoint : Function.Surjective (Point.map γ)) (b : ComplexPoint B) :
    ∃ (D : ComplexPoint Z →₀ ℤ) (hD : ∀ q, 0 ≤ D q),
      b4c_deg D = (n : ℤ) ∧
      ∃ (x : ComplexPoint (g3_power Z n))
        (ι : (Σ i : D.support, Fin (Int.toNat (D i.1))) ≃ Fin n),
        Point.map γ x = b ∧
        (∀ i l, Point.map (g3_proj Z n (ι ⟨i, l⟩)) x = i.1) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hpoint b
  let t₀ := fun j => Point.map (g3_proj Z n j) x₀
  let D := s2e_markedPoleDivisor t₀
  have hD (q : ComplexPoint Z) : 0 ≤ D q := by
    change 0 ≤ (∑ j, Finsupp.single (t₀ j) (1 : ℤ)) q
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_nonneg
    intro j _
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  have hn : b4c_deg D = (n : ℤ) := s2e_markedPoleDivisor_degree t₀
  have henum : ∃ ι : (Σ i : D.support, Fin (Int.toNat (D i.1))) ≃ Fin n,
      D = ∑ j, Finsupp.single (ι.symm j).1.1 (1 : ℤ) :=
    residual_effective_divisor_support_enumeration (C := ComplexPoint Z) D hD (n := n) hn
  obtain ⟨ι, hι⟩ := henum
  let t : Fin n → ComplexPoint Z := fun j => (ι.symm j).1.1
  let x := s2_lift n t
  have hproj (j : Fin n) : Point.map (g3_proj Z n j) x = t j :=
    s2_check_lift_proj n t j
  have hdiv : D = ∑ j, Finsupp.single (Point.map (g3_proj Z n j) x) (1 : ℤ) := by
    simpa only [hproj] using hι
  have hx : Point.map γ x = b := by
    have he := residual_quotient_divisor_lift_evaluation Z B n γ hγ D hD hn x hdiv
    have he₀ := residual_quotient_divisor_lift_evaluation Z B n γ hγ D hD hn x₀ rfl
    exact he.trans (he₀.symm.trans hx₀)
  refine ⟨D, hD, hn, x, ι, hx, ?_⟩
  intro i l
  rw [hproj]
  simp only [t, Equiv.symm_apply_apply]

#print axioms residual_quotient_point_support_indices
end HodgeLean.Foundations.Program.G32Native
