import HodgeLean.Adapters.CycleClassDivisorPowersProofs

/-! # Divisor-first small-dimensional corollaries (frozen specification)

Implications from scoped Lefschetz (1,1), and in dimensions two and three
from the displayed polarization inputs. The old Blocks predicate is unchanged.
Translation invariance is the first geometric segment, not an intersection theorem.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
namespace HodgeLean.Adapters

/-- Translation acts trivially on rational cohomology in every degree.
Source: Hatcher, Algebraic Topology, Theorem 2.10 and §3.1;
Birkenhake--Lange, Complex Abelian Varieties, second edition, §1.1. -/
theorem ccm8_translation_pullback (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (t : ComplexPoint X) (n : ℕ) (a : HQ X n) :
    homPullback (GrpObj.mulRight t).hom n a = a :=
  ccm8_translation_pullback_aux X t n a

/-- The curve corollary needs no multiplicativity or cycle-to-Hodge premise.
Source: the degree split in HodgeBlocks.hodgeConjecture_g1.
Checks: F-1690 -/
@[hodge_milestone] theorem ccm8_hdg_le_span_g1 (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (hT : TorusCohomology μ)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  ccm8_hdg_le_span_g1_aux X μ hT h11 hg

/-- The surface corollary needs only the algebraic nonzero square.
Source: the degree split and top-line argument in HodgeBlocks.hodgeConjecture_g2.
Checks: F-1690 -/
@[hodge_milestone] theorem ccm8_hdg_le_span_g2 (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (hT : TorusCohomology μ) (η : HQ X 2)
    (hpow : cupPow X μ η 2 ∈ algebraicCycleClassSpan X 2)
    (hne : cupPow X μ η 2 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  ccm8_hdg_le_span_g2_aux X μ hT η hpow hne h11 hg

/-- The threefold corollary uses fixed-divisor closure and the Hodge type of η.
Source: HodgeBlocks.hodgeConjecture_g3; Voisin, Hodge Theory and Complex
Algebraic Geometry I, Theorem 6.25 and §7.1.
Checks: F-1690 -/
@[hodge_milestone] theorem ccm8_hdg_le_span_g3 (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (μ : CupProduct X) (hT : TorusCohomology μ) (η : HQ X 2)
    (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η)
    (hC : CupFiltered X μ) (hηH : η ∈ Hdg^1(X; ℚ))
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  ccm8_hdg_le_span_g3_aux X μ hT η hA hL hC hηH h11 hg

/-- W1: point divisor, translated by a constructed finite point of E.
Source: the cubic finite-point construction and translation invariance. -/
example : homPullback (GrpObj.mulRight (Over.homMk finitePoint finitePoint_over : ComplexPoint E)).hom 2 ccm8_pointClass =
    ccm8_pointClass := ccm8_translation_pullback E (Over.homMk finitePoint finitePoint_over : ComplexPoint E) 2 ccm8_pointClass

/-- W2: theta-product class, translated along the first coordinate of E².
Source: the power inclusion and translation invariance. -/
example : homPullback
    (GrpObj.mulRight ((Over.homMk finitePoint finitePoint_over : ComplexPoint E) ≫ (g3_powerData E 2).incl 0)).hom 2
      ccm8_thetaClass = ccm8_thetaClass :=
  ccm8_translation_pullback (g3_power E 2)
    ((Over.homMk finitePoint finitePoint_over : ComplexPoint E) ≫ (g3_powerData E 2).incl 0) 2 ccm8_thetaClass

/-- W3: all premises of the curve corollary are constructed on E.
Source: algebraicCycleClassSpan_one_cubic and the torus comparison. -/
example : ∀ p : ℕ, Hdg^p(E; ℚ) ≤ algebraicCycleClassSpan E p :=
  ccm8_hdg_le_span_g1 E (cupProductOf E) (torusCohomology_cupProductOf E)
    (by unfold LefschetzOneOneFor; rw [algebraicCycleClassSpan_one_cubic]; exact le_top) E_dim

/-- Application on the constructed square, with the remaining geometric inputs explicit.
This is an implication example, not a full premise witness.
Source: the product dimension formula and ccm8_hdg_le_span_g2. -/
example
    (hpow : cupPow (g3_power E 2) (cupProductOf (g3_power E 2)) ccm8_thetaClass 2
      ∈ algebraicCycleClassSpan (g3_power E 2) 2)
    (hne : cupPow (g3_power E 2) (cupProductOf (g3_power E 2)) ccm8_thetaClass 2 ≠ 0)
    (h11 : LefschetzOneOneFor (g3_power E 2)) :
    ∀ p : ℕ, Hdg^p(g3_power E 2; ℚ) ≤ algebraicCycleClassSpan (g3_power E 2) p :=
  ccm8_hdg_le_span_g2 (g3_power E 2) (cupProductOf (g3_power E 2))
    (torusCohomology_cupProductOf (g3_power E 2)) ccm8_thetaClass hpow hne h11
    (by rw [spec_g2_dim_eq (g3_powerData E 2), E_dim])

/-- Application on the cubic third power, with the remaining geometric inputs explicit.
This is an implication example, not a full premise witness.
Source: the product dimension formula and ccm8_hdg_le_span_g3. -/
example (η : HQ (g3_power E 3) 2)
    (hA : AlgebraicTimesDivisor (g3_power E 3) (cupProductOf (g3_power E 3)) η)
    (hL : HardLefschetz (g3_power E 3) (cupProductOf (g3_power E 3)) η)
    (hηH : η ∈ Hdg^1(g3_power E 3; ℚ))
    (h11 : LefschetzOneOneFor (g3_power E 3)) :
    ∀ p : ℕ, Hdg^p(g3_power E 3; ℚ) ≤ algebraicCycleClassSpan (g3_power E 3) p :=
  ccm8_hdg_le_span_g3 (g3_power E 3) (cupProductOf (g3_power E 3))
    (torusCohomology_cupProductOf (g3_power E 3)) η hA hL
    (cupFiltered_cupProductOf_of_abelian (g3_power E 3)) hηH h11
    (by rw [spec_g2_dim_eq (g3_powerData E 3), E_dim])

end HodgeLean.Adapters
