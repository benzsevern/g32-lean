import HodgeLean.Foundations.Program.SchoenCycleTupleStabilizerCoordinates

/-! # Exact stabilizers of mixed collision blocks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The full actual tuple stabilizer is exactly the set of permutations preserving its indexed collision blocks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_tuple_stabilizer_iff_blocks
    (X : Over (Spec ↧ℂ)) (n b : ℕ) (x : ComplexPoint (g3_power X n))
    (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint X) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj X n (ι ⟨a, i⟩)) x = p a)
    (σ : Equiv.Perm (Fin n)) :
    Point.map (s2_permute X n σ) x = x ↔
      ∀ i, (ι.symm (σ i)).1 = (ι.symm i).1 := by
  have hcoord (i : Fin n) : Point.map (g3_proj X n i) x = p (ι.symm i).1 := by
    obtain ⟨⟨a, j⟩, rfl⟩ := ι.surjective i
    simpa only [ι.symm_apply_apply] using hx a j
  rw [s2e_tuple_stabilizer_iff_coordinates]
  constructor
  · intro h i
    apply hp
    rw [← hcoord (σ i), ← hcoord i]
    exact h i
  · intro h i
    rw [hcoord, hcoord, h i]

#print axioms s2e_mixed_tuple_stabilizer_iff_blocks
end HodgeLean.Foundations.Program
