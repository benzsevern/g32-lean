import HodgeLean.Foundations.Program.SchoenCycleC11Proofs

/-! # Finite etale covers of projective space
Implication from an actual finite etale surjection to disjoint scheme sections
whose ranges exhaust the source. Branch avoidance and residual deck transport
are later units. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite etale projective-space cover has actual disjoint copies of its base.
Source: Schoen (1988), printed p. 15, etale cover over the lifted projective slice;
Hartshorne, Algebraic Geometry, Appendix B, comparison with complex topology. -/
theorem s2e_chain_projective_etale_sections
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left] [Surjective β.left] :
    ∃ (n : ℕ) (_ : 0 < n)
      (ι : Fin n → (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ W)),
      (∀ i, IsClosedImmersion (ι i).left) ∧
      (∀ i, ι i ≫ β = 𝟙 _) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ι i).left) (Set.range (ι j).left)) ∧
      (∀ w : W.left, ∃ i, w ∈ Set.range (ι i).left) :=
  s2e_chain_projective_etale_sections_aux k W β

example := @s2e_chain_projective_etale_sections

end HodgeLean.Foundations.Program
