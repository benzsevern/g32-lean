import HodgeLean.Foundations.Program.SchoenCycleInsertionPointRange
import HodgeLean.Foundations.Program.SchoenCycleBranchAdicPrincipality
import HodgeLean.Foundations.Program.SchoenCyclePrincipalGeneratorDescent
import HodgeLean.Foundations.Program.SchoenCycleAdicApproximationTransport

/-! # Normalized algebraic generators of the actual branch stalk ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained branch ideal in the actual algebraic stalk has a generator
whose pullback approximates the geometric parameter product to any given order.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2 and 10. -/
theorem s2e_total_collision_branch_stalk_normalized_generator
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (y : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z (n + 1) i)
      (Point.map (s2c_branchInsertion Z n a) y) = a)
    (U : B.left.affineOpens)
    (hu : (s2c_branchInsertion Z n a ≫ γ).left y.underlying ∈ U.1) (N : ℕ) :
    let x := Point.map (s2c_branchInsertion Z n a) y
    let R := (g3_power Z (n + 1)).left.presheaf.stalk x.underlying
    let D := B.left.presheaf.stalk (γ.left x.underlying)
    ∃ d : D, ((s2c_branchIdeal Z B n γ a).ideal U).map
      (B.left.presheaf.germ U.1 (γ.left x.underlying) hu).hom = Ideal.span {d} ∧
      (γ.left.stalkMap x.underlying).hom d -
        (∏ i, s2e_curvePowerParameter Z (n + 1) x i) ∈ IsLocalRing.maximalIdeal R ^ N := by
  letI : IsLocallyNoetherian (g3_power Z (n + 1)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z (n + 1)).hom
  letI := s2e_quotient_isLocallyNoetherian (g3_power Z (n + 1)) B (Equiv.Perm (Fin (n + 1)))
    (s2_permute Z (n + 1)) (s2e_step1_permute_one Z (n + 1))
    (s2e_step1_permute_mul Z (n + 1)) γ hγ hquot
  let x := Point.map (s2c_branchInsertion Z n a) y
  let D := B.left.presheaf.stalk (γ.left x.underlying)
  letI : IsNoetherianRing D := inferInstanceAs
    (IsNoetherianRing (B.left.presheaf.stalk (γ.left x.underlying)))
  obtain ⟨c, hgen, hc⟩ := s2e_total_collision_branch_adic_principal Z B n γ hγ hquot y a hx U hu
  obtain ⟨d, hd, he⟩ := s2e_local_principal_generator_approximating_adic _ c hgen N
  refine ⟨d, hd, ?_⟩
  exact s2e_adic_stalkMap_approximation_transport γ.left x.underlying c _ hc d N he

#print axioms s2e_total_collision_branch_stalk_normalized_generator
/-- At any actual total-collision point, the retained branch stalk ideal has
an algebraic generator with arbitrary finite-order product normalization.
Source: Schoen, Compositio Mathematica 65 (1988), §2, printed p. 12;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2 and 10. -/
theorem s2e_total_collision_branch_stalk_generator_at_point
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (n + 1) ⟶ T),
      (∀ σ, s2_permute Z (n + 1) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z (n + 1))) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z (n + 1) i) x = a)
    (U : B.left.affineOpens) (hu : γ.left x.underlying ∈ U.1) (N : ℕ) :
    let R := (g3_power Z (n + 1)).left.presheaf.stalk x.underlying
    let D := B.left.presheaf.stalk (γ.left x.underlying)
    ∃ d : D, ((s2c_branchIdeal Z B n γ a).ideal U).map
      (B.left.presheaf.germ U.1 (γ.left x.underlying) hu).hom = Ideal.span {d} ∧
      (γ.left.stalkMap x.underlying).hom d -
        (∏ i, s2e_curvePowerParameter Z (n + 1) x i) ∈ IsLocalRing.maximalIdeal R ^ N := by
  obtain ⟨y, rfl⟩ : ∃ y : ComplexPoint (g3_power Z n),
      Point.map (s2c_branchInsertion Z n a) y = x :=
    ⟨Point.map (s2e_dropFirstPowerCoordinate Z n) x,
      s2e_branchInsertion_point_of_first_coordinate Z n a x (hx 0)⟩
  exact s2e_total_collision_branch_stalk_normalized_generator Z B n γ hγ hquot y a hx U hu N

#print axioms s2e_total_collision_branch_stalk_generator_at_point
end HodgeLean.Foundations.Program
