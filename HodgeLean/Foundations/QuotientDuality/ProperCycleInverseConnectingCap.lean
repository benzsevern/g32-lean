import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVCapConnecting

/-! # Actual quotient caps through inverse connecting maps
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original even cap commutes with inverse actual connecting maps whenever those maps are isomorphisms.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_subcomplex_mv_cap_connecting.
HC no distance; AV milestone no distance. -/
theorem properCycle_subcomplex_mv_cap_inverse_connecting
    (X : TopCat.{0}) (A P Q : (TopCat.toSSet.obj X).Subcomplex)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0)
    [IsIso ((properCycle_fixed_subcomplex_sequence_shortExact X A P Q).δ
      (p + (q+1)) (p+q) (Nat.add_assoc p q 1).symm)]
    [IsIso ((properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ (q+1) q rfl)] :
    inv ((properCycle_fixed_subcomplex_sequence_shortExact X A P Q).δ
        (p + (q+1)) (p+q) (Nat.add_assoc p q 1).symm) ≫
      properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q+1) hp φ hA hφ =
    properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ ≫
      inv ((properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ (q+1) q rfl) := by
  apply (cancel_mono ((properCycle_subcomplex_quotient_sequence_shortExact X P Q).δ
    (q+1) q rfl)).mp
  rw [Category.assoc, properCycle_subcomplex_mv_cap_connecting, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end HodgeLean.Foundations.QuotientDuality
