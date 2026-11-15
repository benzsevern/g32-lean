import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelPeriods
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelDescent
import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemEvaluation
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.Defs

/-! # Actual Abel values of effective divisors in the supplied quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The algebraic Abel map evaluates the literal weighted divisor, with all multiplicities. -/
theorem residual_abel_value_effective_divisor (n : ℕ) (p : ComplexPoint Z)
    (γ : g3_power Z n ⟶ B) (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z n i) u)))
    (D : ComplexPoint Z →₀ ℤ) (hD : ∀ q, 0 ≤ D q) (hd : b4c_deg D = (n : ℤ)) :
    Point.map a (s2e_symmetricQuotientEvaluation n γ (s2e_divisorSym D hD hd)) =
      theta (C := ComplexPoint Z) hOne
        (weightedSum (analyticAbel (C := ComplexPoint Z) hOne p) D) := by
  classical
  obtain ⟨f, hf⟩ := s2e_effectiveDivisor_exists_tuple D hD hd
  have he := s2e_symmetricQuotientEvaluation_eq n γ hγ _ f
    (s2e_divisor_tuple_enumeration D hD hd f hf)
  have hev : Point.map a (s2e_symmetricQuotientEvaluation n γ (s2e_divisorSym D hD hd)) =
      Point.map a (Point.map γ (s2_lift n f)) :=
    congrArg (fun b : ComplexPoint B => Point.map a b) he
  refine hev.trans ?_
  calc
    Point.map a (Point.map γ (s2_lift n f)) = Point.map (γ ≫ a) (s2_lift n f) :=
      (Point.map_comp_apply γ a (s2_lift n f)).symm
    _ = theta (C := ComplexPoint Z) hOne
        (∑ i, analyticAbel (C := ComplexPoint Z) hOne p
          (Point.map (g3_proj Z n i) (s2_lift n f))) := congrFun ha _
    _ = theta (C := ComplexPoint Z) hOne
        (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (f i)) := by
      apply congrArg (theta (C := ComplexPoint Z) hOne)
      apply Finset.sum_congr rfl
      intro i _
      change analyticAbel hOne p (s2_lift n f ≫ g3_proj Z n i) = _
      rw [s2_check_lift_proj]
    _ = theta (C := ComplexPoint Z) hOne
        (weightedSum (analyticAbel (C := ComplexPoint Z) hOne p) D) := by
      apply congrArg (theta (C := ComplexPoint Z) hOne)
      rw [hf, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [weightedSum, Finsupp.linearCombination_single]

#print axioms residual_abel_value_effective_divisor
/-- Projective full-system evaluation has exactly the retained weighted Abel value. -/
theorem residual_abel_value_projective_system
    (k r : ℕ) (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hOne q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hOne q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ t, q.val ⟨p, t⟩ = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (p : ComplexPoint Z) (γ : g3_power Z (2 * k) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u))) (z : Projectivization ℂ W) :
    Point.map a (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id z) =
      theta (C := ComplexPoint Z) hOne (weightedSum
        (analyticAbel (C := ComplexPoint Z) hOne p) (residualProjectiveDivisor hOne y W z)) := by
  let D := residualProjectiveDivisor hOne y W z
  have hD := residualProjectiveDivisor_effective hOne y hy W hW z
  have hd := residualProjectiveDivisor_degree hOne y W
    (fun q => ⟨(hW q).1, (hW q).2.2⟩) hgenus z
  have hm := congrArg (fun s : Sym (ComplexPoint Z) (2 * k) =>
    Point.map a (s2e_symmetricQuotientEvaluation (2 * k) γ s))
    (Sym.map_id (s2e_divisorSym D hD hd))
  exact hm.trans (residual_abel_value_effective_divisor Z B (2 * k) p γ hγ a ha D hD hd)

#print axioms residual_abel_value_projective_system

/-- The descended algebraic Abel map has one value on the entire full projective system. -/
theorem residual_system_abel_value_constant
    (k r : ℕ) (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hOne q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hOne q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ t, q.val ⟨p, t⟩ = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (p : ComplexPoint Z) (γ : g3_power Z (2 * k) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u))) :
    ∀ u v : Projectivization ℂ W,
      Point.map a (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id u) =
        Point.map a (residualProjectiveSystemPoint hOne y hy W hW hgenus γ id v) := by
  have he := residual_abel_value_projective_system Z B k r y hy W hW hgenus p γ hγ a ha
  intro u v
  have hs : weightedSum (analyticAbel (C := ComplexPoint Z) hOne p)
      (residualProjectiveDivisor hOne y W u) =
      weightedSum (analyticAbel (C := ComplexPoint Z) hOne p)
        (residualProjectiveDivisor hOne y W v) := by
    induction u using Projectivization.ind with
    | h u hu =>
      induction v using Projectivization.ind with
      | h v hv =>
        exact residual_normalized_divisor_abel_sum_eq hOne (Set.range y) W
          (fun q => ⟨(hW q).1, (hW q).2.2⟩) u v hu hv p (s2e_markedPoleDivisor y)
  exact (he u).trans ((congrArg (theta (C := ComplexPoint Z) hOne) hs).trans (he v).symm)

#print axioms residual_system_abel_value_constant

end HodgeLean.Foundations.Program.G32Native
