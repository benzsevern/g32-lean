import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.Defs
import Mathlib.Data.Finset.Sort

/-! # Retained symmetric charts and paired subsets

Charts compose with specified scheme isomorphisms. Finite subsets enumerate the
original branch labels without changing the retained branch ideal.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- The even and odd members of the retained pair.
Source: Schoen (1988), §2, pp. 12–14.
HC no distance; AV milestone no distance.
-/
def pairLabel (r : ℕ) (i : Fin r) (side : Fin 2) : Fin (2*r) :=
  ⟨2*i.val + side.val, by omega⟩

example : pairLabel 2 (1 : Fin 2) (1 : Fin 2) = (3 : Fin 4) := rfl

/-- Increasing enumeration of a selected set of branch labels.
Source: Schoen (1988), Lemma 2.2, finite branch intersections.
HC no distance; AV milestone no distance.
-/
def subsetPoints {C : Over (Spec ↧ℂ)} {r : ℕ}
    (z : Fin (2*r) → ComplexPoint C) (J : Finset (Fin (2*r))) :
    Fin J.card → ComplexPoint C := fun i => z (J.orderIsoOfFin rfl i)

example {C : Over (Spec ↧ℂ)} (z : Fin 4 → ComplexPoint C) :
    subsetPoints (r := 2) z ({1} : Finset (Fin 4)) ⟨0, by simp⟩ = z 1 := by
  apply congrArg z
  exact Finset.mem_singleton.mp (({1} : Finset (Fin 4)).orderIsoOfFin rfl ⟨0, by simp⟩).property

/-- Stage-zero branch family on the specified quotient, retaining each kernel.
Source: Schoen (1988), §2, p. 12, the divisors S_j.
HC no distance; AV milestone no distance.
-/
def stageZeroBranches (C B : Over (Spec ↧ℂ)) (h r : ℕ)
    (γ : g3_power C (h+1) ⟶ B) (z : Fin (2*r) → ComplexPoint C) :
    Fin (2*r) → B.left.IdealSheafData := fun j => s2c_branchIdeal C B h γ (z j)

example (C B : Over (Spec ↧ℂ)) (γ : g3_power C 2 ⟶ B)
    (z : Fin 2 → ComplexPoint C) :
    stageZeroBranches C B 1 1 γ z 1 = (s2c_branchInsertion C 1 (z 1) ≫ γ).left.ker := rfl

variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]

/-- An existing affine invariant chart transported to the retained target.
Source: SGA 1, Exposé V, §1; Milne, Jacobian Varieties, §3.
HC no distance; AV milestone no distance.
-/
def retainedChart (n : ℕ) {Q : Over (Spec ↧ℂ)}
    (e : symmetricPower C n ≅ Q) (W : Index C n) : affineChart C n W ⟶ Q.left :=
  chartInclusion C n W ≫ e.hom.left

example (W : Index C 2) : retainedChart C 2 (Iso.refl _) W = chartInclusion C 2 W :=
  Category.comp_id _

end HodgeLean.Foundations.Curves.SymmetricCharts.StageThree
