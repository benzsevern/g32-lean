import HodgeLean.Foundations.Program.SchoenCycleAnalyticCoordinateGerms

/-! # Coordinate products under actual stalk realization -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
open Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- A realization sending the selected parameters to nonzero scalar coordinate multiples sends their product times a unit to the reduced coordinate product times a unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analytic_parameter_product_unit
    {R : Type*} [CommRing R] (n : ℕ) (A : R →+* AnalyticGermAt n 0)
    (t : Fin n → R) (S : Finset (Fin n)) (scalar : ℂ) (hscalar : scalar ≠ 0)
    (ht : ∀ i ∈ S, (A (t i)).val =
      Filter.Germ.ofFun (fun z : Fin n → ℂ => scalar * z i)) (u : Rˣ) :
    ∃ v : (AnalyticGermAt n 0)ˣ,
      A ((∏ i ∈ S, t i) * (u : R)) =
        (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (v : AnalyticGermAt n 0) := by
  let K : AnalyticGermAt n 0 :=
    ⟨Filter.Germ.ofFun (fun _ => scalar), fun _ => scalar, analyticAt_const, rfl⟩
  have hK : IsUnit K := (s2e_analyticGermAt_isUnit_iff K).mpr hscalar
  have hti (i : Fin n) (hi : i ∈ S) : A (t i) = s2e_analyticCoordinateGerm n i * K := by
    apply Subtype.ext
    rw [ht i hi]
    apply Filter.Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => mul_comm scalar (z i))
  have heq : A ((∏ i ∈ S, t i) * (u : R)) =
      (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * (K ^ S.card * A (u : R)) := by
    rw [map_mul, map_prod]
    calc
      (∏ i ∈ S, A (t i)) * A (u : R) =
          (∏ i ∈ S, (s2e_analyticCoordinateGerm n i * K)) * A (u : R) := by
        congr 1
        exact Finset.prod_congr rfl hti
      _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const]; ring
  obtain ⟨v, hv⟩ := (hK.pow S.card).mul (u.isUnit.map A)
  exact ⟨v, heq.trans (congrArg (fun w => (∏ i ∈ S, s2e_analyticCoordinateGerm n i) * w) hv.symm)⟩

end HodgeLean.Foundations.Program
