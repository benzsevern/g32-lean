import HodgeLean.Foundations.Program.SchoenCycleCollisionAdicGeneration
import HodgeLean.Foundations.Program.SchoenCycleAdicApproximationTransport
import HodgeLean.Foundations.Program.SchoenCycleCollisionStalkJets

/-! # Coefficient parameters at a total collision
First infrastructure part. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped Classical BigOperators
namespace HodgeLean.Foundations.Program

/-- Coefficient parameters at a total collision.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, §3, symmetric products;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1. -/
theorem s2e_collision_coefficient_parameters_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a)
    (N : ℕ) (hN : n < N) :
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ c : Fin n → S,
      IsLocalRing.maximalIdeal S = Ideal.span (Set.range c) ∧
      (∀ j, γ.left.stalkMap x.underlying (c j) -
        aeval (s2e_curvePowerParameter Z n x) (esymm (Fin n) ℂ (j.val + 1)) ∈
        IsLocalRing.maximalIdeal R ^ N) := by
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  let S := B.left.presheaf.stalk (γ.left x.underlying)
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI := s2e_quotient_isLocallyNoetherian (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ hquot
  letI : IsNoetherianRing S := inferInstanceAs
    (IsNoetherianRing (B.left.presheaf.stalk (γ.left x.underlying)))
  obtain ⟨c, hc, he⟩ := s2e_total_collision_adic_elementary_generators Z B n γ hγ hquot x a hx
  have hgen : IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal S) S) =
      Ideal.span (Set.range c) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact hc
  obtain ⟨d, hd, hdiff⟩ := s2e_local_generators_approximating_adic_generators c hgen
    (max 2 N) (le_max_left _ _)
  refine ⟨d, hd, fun j => ?_⟩
  apply (Ideal.pow_le_pow_right (le_max_right 2 N))
  exact s2e_adic_stalkMap_approximation_transport γ.left x.underlying (c j)
    (aeval (s2e_curvePowerParameter Z n x) (esymm (Fin n) ℂ (j.val + 1)))
    (he j) (d j) (max 2 N) (hdiff j)

end HodgeLean.Foundations.Program
