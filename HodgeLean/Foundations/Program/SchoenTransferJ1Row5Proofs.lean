import HodgeLean.Foundations.WitnessSelection.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenTransferQ2cApplications
import HodgeLean.Foundations.Program.SchoenTransferJ12RationalImage
import HodgeLean.Foundations.Program.SchoenTransferJ12SumReflection
import HodgeLean.Foundations.Program.SchoenSelectedGeometry
/-! # S4 selected witness applications

Implications from the literal retained S2 alternatives and realization choices.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Papers
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.Program
/-- Contract J1.5, on the specified native witnesses.
Source: Schoen (1988), Theorem 2.0 and Corollary 3.1; s4-chain-contract.md, J1 row 5.
Example: SchoenTransferJ1Checks.row5_construction.
HC no distance; AV milestone no distance. -/
theorem s4_chain_selected_part_cycles_aux {A : g32t_Sixfold} (X : g32p_Cover A)
    (S : g32p_Supplier) (hS : g32p_Admissible X.aut S)
    (P : g32p_Part X.J X.aut S)
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1)
    [IsIntegral (g3_power Y (2 * P.k)).left]
    [Smooth (g3_power Y (2 * P.k)).hom]
    [IsProjective (g3_power Y (2 * P.k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (he : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (hfaithful : Function.Injective a)
    (f : Y ⟶ P.P) (hf : Function.Injective (homPullback f 1))
    (himage : LinearMap.range (homPullback f 1) = LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (homPullback f 1 v) =
        homPullback f 1 (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v))
    (hS2CurveCycles : s4_invariantPrimitive S Y a e (2 * P.k) (Nat.mul_pos (by norm_num) P.act.cyc_positive) ≤ cfd_cycleSpan (g3_power Y (2 * P.k)) P.k) :
    cyc_Algebraic (cupProductOf (X.part S hS).P) (X.part S hS).act.cyc_coordinates := by
  apply (s0_part_algebraic_iff X.J X.aut S P (X.part S hS)).mp
  intro x hx
  apply s4_selected_sum_reflects_cycles P.P Y hdim f hf P.k x
  apply hS2CurveCycles
  rw [← s4_selected_rational_primitive_image X.J X.aut S P Y hdim a e he ha1
    hamul hfaithful f hf himage hscalar]
  exact Submodule.mem_map_of_mem hx

end HodgeLean.Foundations.Program
