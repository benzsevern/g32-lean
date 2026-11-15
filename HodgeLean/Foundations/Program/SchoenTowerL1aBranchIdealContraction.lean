import HodgeLean.Foundations.Program.SchoenTowerL1aBranchInsertionKernel
import HodgeLean.Foundations.Program.SchoenTowerL1aIdealOpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The retained insertion ideal on actual affine quotient restrictions

Implication from the actual insertion fibre and affine ideal image to the
contracted coordinate point ideal on the retained restricted quotient.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual retained branch ideal on an affine target restriction is the
contraction of the actual first-coordinate point ideal on its preimage.
Source: Schoen (1988), Lemma 2.2, printed p. 13; Hartshorne, Algebraic Geometry, II.5–6. -/
theorem s2v_l1a_branchIdeal_affine_contraction
    (Z B : Over (Spec ↧ℂ)) [IsSeparated Z.hom] (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (b : ComplexPoint Z) (U : B.left.affineOpens) :
    let hV := U.2.preimage γ.left
    ((s2c_branchIdeal Z B h γ b).comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top _ U.2⟩ =
      (((b.left.ker.comap (g3_proj Z (h + 1) 0).left).comap
        (γ.left ⁻¹ᵁ U.1).ι).ideal ⟨⊤, @isAffineOpen_top _ hV⟩).comap
          (γ.left ∣_ U.1).appTop.hom := by
  dsimp only
  rw [s2c_branchIdeal, Over.comp_left, Scheme.Hom.ker_comp,
    s2v_l1a_branchInsertion_kernel]
  exact s2v_l1a_restricted_ideal_image γ.left
    (b.left.ker.comap (g3_proj Z (h + 1) 0).left) U

end HodgeLean.Foundations.Program
