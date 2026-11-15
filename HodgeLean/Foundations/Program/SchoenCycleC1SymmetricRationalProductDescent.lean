import HodgeLean.Foundations.Program.SchoenCycleC1QuotientRationalDescent
import HodgeLean.Foundations.Program.SchoenCycleC1PermutationRationalProduct

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual coordinate rational product descends through the retained
symmetric categorical quotient with its exact generic stalk embedding. -/
theorem s2e_c1_symmetric_rational_product_descent
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (N : ℕ)
    (γ : g3_power Z N ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγinv : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (φ : Fin N → (Z.left.functionField →+* (g3_power Z N).left.functionField))
    (hφ : ∀ i (p : (g3_power Z N).left) (r : Z.left.presheaf.stalk ((g3_proj Z N i).left p)),
      φ i (algebraMap (Z.left.presheaf.stalk ((g3_proj Z N i).left p)) Z.left.functionField r) =
        algebraMap ((g3_power Z N).left.presheaf.stalk p) (g3_power Z N).left.functionField
          (((g3_proj Z N i).left.stalkMap p).hom r))
    (f : Z.left.functionField) :
    let hg := s2e_c1_dominant_generic_point γ.left
    let ψ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      γ.left.stalkMap (genericPoint (g3_power Z N).left)).hom
    ∃ d : B.left.functionField, ψ d = ∏ i, φ i f := by
  dsimp only
  letI : ∀ σ, IsIso (s2_permute Z N σ) :=
    s2e_step1_action_isIso (g3_power Z N) (Equiv.Perm (Fin N)) (s2_permute Z N)
      (s2e_step1_permute_one Z N) (s2e_step1_permute_mul Z N)
  exact s2e_c1_quotient_rational_descent (g3_power Z N) B (Equiv.Perm (Fin N))
    (s2_permute Z N) γ hγinv hγ (∏ i, φ i f)
    (fun σ => s2e_c1_permutation_rational_product_invariant Z N φ hφ f σ)

end HodgeLean.Foundations.Program
