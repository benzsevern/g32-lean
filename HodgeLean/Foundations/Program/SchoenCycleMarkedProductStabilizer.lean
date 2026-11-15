import HodgeLean.Foundations.Program.SchoenCycleCollisionBlocks

/-! # Stabilizer invariance of actual marked coordinate products -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The actual marked-coordinate product is fixed by every permutation fixing its tuple.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_marked_parameter_product_stabilizer_invariant
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (n : ℕ) (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (S : Finset (Fin n))
    (hS : ∀ i, i ∈ S ↔ Point.map (g3_proj Z n i) x = a)
    (σ : Equiv.Perm (Fin n)) (hσ : Point.map (s2_permute Z n σ) x = x) :
    s2e_fixed_point_stalkPullback (g3_power Z n).left (s2_permute Z n σ).left x.underlying
      (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ) x hσ)
      (∏ i ∈ S, s2e_curvePowerParameter Z n x i) =
        ∏ i ∈ S, s2e_curvePowerParameter Z n x i := by
  have hmem (i : Fin n) : i ∈ S ↔ σ i ∈ S :=
    (hS i).trans ((s2e_fixed_tuple_collision_block Z n x a σ hσ i).trans ((hS (σ i)).symm))
  rw [map_prod]
  simp only [s2e_fixed_permutation_curvePowerParameter Z n σ x hσ]
  apply Finset.prod_bij (fun i _ => σ.symm i)
  · intro i hi
    exact (hmem (σ.symm i)).mpr (by simpa only [σ.apply_symm_apply] using hi)
  · intro i _ j _ hij
    exact σ.symm.injective hij
  · intro j hj
    exact ⟨σ j, (hmem j).mp hj, σ.symm_apply_apply j⟩
  · intro i _
    rfl

end HodgeLean.Foundations.Program
