import HodgeLean.Foundations.Program.SchoenTowerConormalDefs
import HodgeLean.Foundations.Mathlib.CyclePushforwardCore

/-! # Cycles in the residual cyclic orbit
Actual prime cycles and their finite weighted sums on the tower spaces.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program
open Classical

/-- The prime cycle of the scheme image of an integral component.
Source: Fulton, Intersection Theory, §1.3; Schoen (1988), p. 15, Q. -/
def s2e_componentCycle {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (R : Type*) [Semiring R] : AlgebraicCycle W.left R :=
  Function.locallyFinsuppWithin.single (ι.left (genericPoint Q.left)) 1

example {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] (ι : Q ⟶ W) :
    s2e_componentCycle ι ℚ =
      Function.locallyFinsuppWithin.single (ι.left (genericPoint Q.left)) 1 := rfl

/-- Weighted sum of the actual translated components. The weights use the
negative residue, and the maps use forward powers of the residual generator.
Source: Schoen (1988), p. 15, zχ = ∑ χ(-t) δ(t)*Q. -/
def s2e_weightedCycle {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (d : W ⟶ W) (m : ℕ) (R : Type*) [CommRing R]
    (χ : ZMod m → R) : AlgebraicCycle W.left R :=
  ∑ t : Fin m, (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) R).mapRange
    (χ (-(t.val : ZMod m)) * ·) (mul_zero _)

example {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (d : W ⟶ W) (m : ℕ) (χ : ZMod m → ℂ) :
    s2e_weightedCycle ι d m ℂ χ = ∑ t : Fin m,
      (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) ℂ).mapRange
        (χ (-(t.val : ZMod m)) * ·) (mul_zero _) := rfl

/-- The character-weighted sum in any coefficient module, with the same
negative-residue convention as the geometric cycle.
Source: Schoen (1988), pp. 13 and 15, the cycle character sum. -/
def s2e_weightedSum (m : ℕ) {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (χ : ZMod m → R) (v : Fin m → M) : M :=
  ∑ t, χ (-(t.val : ZMod m)) • v t

example (m : ℕ) (χ : ZMod m → ℂ) (v : Fin m → ℂ) :
    s2e_weightedSum m χ v = ∑ t, χ (-(t.val : ZMod m)) • v t := rfl

end HodgeLean.Foundations.Program
