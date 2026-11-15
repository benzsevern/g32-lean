import HodgeLean.Foundations.Program.SchoenCycleAffineIdealShrinking
import HodgeLean.Foundations.Program.SchoenCycleBranchStalkGenerator
import HodgeLean.Foundations.Program.SchoenCycleBranchAffineImage
import HodgeLean.Foundations.Program.SchoenCycleCoefficientImage
import HodgeLean.Foundations.Program.SchoenCycleCollisionStalkJets

/-! # Actual branch equation at a total collision
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

/-- Actual branch equation at a total collision.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
ACGH, Geometry of Algebraic Curves I, Chapter I, §3. -/
theorem s2e_collision_branch_local_equation_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a)
    (q : ℕ) (hq : n = q + 1) :
    let γq : g3_power Z (q + 1) ⟶ B := eqToHom (congrArg (g3_power Z) hq.symm) ≫ γ
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    ∃ (U : B.left.affineOpens) (hu : γ.left x.underlying ∈ U.1)
      (c : Γ(B.left, U.1)),
      (s2c_branchIdeal Z B q γq a).ideal U = Ideal.span {c} ∧
      γ.left.stalkMap x.underlying
        (B.left.presheaf.germ U.1 (γ.left x.underlying) hu c) -
          (∏ i : Fin n, s2e_curvePowerParameter Z n x i) ∈
        IsLocalRing.maximalIdeal R ^ (n + 1) := by
  subst n
  dsimp only [eqToHom_refl, Category.id_comp]
  letI : IsLocallyNoetherian (g3_power Z (q + 1)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z (q + 1)).hom
  letI := s2e_quotient_isLocallyNoetherian (g3_power Z (q + 1)) B (Equiv.Perm (Fin (q + 1)))
    (s2_permute Z (q + 1)) (s2e_step1_permute_one Z (q + 1))
    (s2e_step1_permute_mul Z (q + 1)) γ hγ hquot
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show γ.left x.underlying ∈ (⊤ : B.left.Opens) from trivial)
  obtain ⟨d, hd, hnorm⟩ := s2e_total_collision_branch_stalk_generator_at_point
    Z B q γ hγ hquot x a hx ⟨U, hU⟩ hpU (q + 1 + 1)
  obtain ⟨W, _, hpW, c, hI, hc⟩ := s2e_affine_generator_of_stalk_generator
    B.left (s2c_branchIdeal Z B q γ a) ⟨U, hU⟩ (γ.left x.underlying) hpU d hd
  refine ⟨W, hpW, c, hI, ?_⟩
  change (γ.left.stalkMap x.underlying).hom
    ((B.left.presheaf.germ W.1 (γ.left x.underlying) hpW).hom c) -
      (∏ i, s2e_curvePowerParameter Z (q + 1) x i) ∈
        IsLocalRing.maximalIdeal ((g3_power Z (q + 1)).left.presheaf.stalk x.underlying) ^ (q + 1 + 1)
  rw [hc]
  exact hnorm

end HodgeLean.Foundations.Program
