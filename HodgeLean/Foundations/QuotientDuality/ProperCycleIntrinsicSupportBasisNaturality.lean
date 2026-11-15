import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportBasis

/-! # Literal zero-extension naturality of intrinsic homology coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The constructed intrinsic homology coordinates commute with actual support inclusion after literal zero extension at the original scheme points.
Source: properCycle_intrinsic_support_sum_enlarge; properCycle_extend_include_coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_basis_enlarge
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ δ : AlgebraicCycle X.left ℚ)
    (hcγ : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (hcδ : ∀ ξ ∈ δ.support, Order.coheight ξ = k)
    (h : a3b4_cycleSupport X.hom γ ⊆ a3b4_cycleSupport X.hom δ)
    (a : Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)) :
    properCycle_extend_coordinates X.left δ
      ((properCycle_intrinsic_support_basis X k hk hdim δ hcδ).symm
        (homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h)) a)) =
      properCycle_extend_coordinates X.left γ
        ((properCycle_intrinsic_support_basis X k hk hdim γ hcγ).symm a) := by
  let E := properCycle_intrinsic_support_basis X k hk hdim γ hcγ
  let F := properCycle_intrinsic_support_basis X k hk hdim δ hcδ
  let v := E.symm a
  let w := properCycle_include_coordinates X.left γ δ v
  have he : F w = homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h)) a := by
    change properCycle_intrinsic_support_sum X k hdim δ hcδ w = _
    rw [← properCycle_intrinsic_support_sum_enlarge X k hdim γ δ hcγ hcδ h v]
    change homologyMap ℚ (2*k) (TopCat.ofHom (ContinuousMap.inclusion h)) (E (E.symm a)) = _
    rw [E.apply_symm_apply]
  have hi := congrArg F.symm he
  rw [F.symm_apply_apply] at hi
  change properCycle_extend_coordinates X.left δ (F.symm _) =
    properCycle_extend_coordinates X.left γ v
  rw [← hi]
  exact properCycle_extend_include_coordinates X.left γ δ
    (properCycle_pure_prime_support_subset X k γ δ hcγ hcδ h) v

end HodgeLean.Foundations.QuotientDuality
