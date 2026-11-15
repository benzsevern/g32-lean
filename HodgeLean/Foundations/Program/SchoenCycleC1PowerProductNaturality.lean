import HodgeLean.Foundations.Program.SchoenCycleC1LocalSquareComposition
import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Coordinate rational products commute with the actual power map whenever
the rational embeddings retain its original local stalk squares. -/
theorem s2e_c1_power_product_naturality
    (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (p : Y ⟶ Z) (N : ℕ)
    (π : Z.left.functionField →+* Y.left.functionField)
    (hπ : ∀ x (r : Z.left.presheaf.stalk (p.left x)),
      π (algebraMap (Z.left.presheaf.stalk (p.left x)) Z.left.functionField r) =
        algebraMap (Y.left.presheaf.stalk x) Y.left.functionField ((p.left.stalkMap x).hom r))
    (φY : Fin N → (Y.left.functionField →+* (g3_power Y N).left.functionField))
    (hY : ∀ i x (r : Y.left.presheaf.stalk ((g3_proj Y N i).left x)),
      φY i (algebraMap (Y.left.presheaf.stalk ((g3_proj Y N i).left x)) Y.left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk x) (g3_power Y N).left.functionField
          (((g3_proj Y N i).left.stalkMap x).hom r))
    (φZ : Fin N → (Z.left.functionField →+* (g3_power Z N).left.functionField))
    (hZ : ∀ i x (r : Z.left.presheaf.stalk ((g3_proj Z N i).left x)),
      φZ i (algebraMap (Z.left.presheaf.stalk ((g3_proj Z N i).left x)) Z.left.functionField r) =
        algebraMap ((g3_power Z N).left.presheaf.stalk x) (g3_power Z N).left.functionField
          (((g3_proj Z N i).left.stalkMap x).hom r))
    (ρ : (g3_power Z N).left.functionField →+* (g3_power Y N).left.functionField)
    (hρ : ∀ x (r : (g3_power Z N).left.presheaf.stalk ((s2_powerMap p N).left x)),
      ρ (algebraMap ((g3_power Z N).left.presheaf.stalk ((s2_powerMap p N).left x))
        (g3_power Z N).left.functionField r) =
        algebraMap ((g3_power Y N).left.presheaf.stalk x) (g3_power Y N).left.functionField
          (((s2_powerMap p N).left.stalkMap x).hom r))
    (f : Z.left.functionField) :
    ρ (∏ i, φZ i f) = ∏ i, φY i (π f) := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hp : s2_powerMap p N ≫ g3_proj Z N i = g3_proj Y N i ≫ p :=
    s2_check_lift_proj _ _ _
  have hp' : (s2_powerMap p N).left ≫ (g3_proj Z N i).left =
      (g3_proj Y N i).left ≫ p.left := congrArg Over.Hom.left hp
  have hγ := s2e_c1_rational_local_square_comp (g3_proj Y N i).left p.left
    (φY i) π (hY i) hπ
  rw [← hp'] at hγ
  have he := s2e_c1_generic_pullback_composition (s2_powerMap p N).left
    (g3_proj Z N i).left ρ (φZ i) ((φY i).comp π) hρ (hZ i) hγ
  exact RingHom.congr_fun he.symm f

end HodgeLean.Foundations.Program
