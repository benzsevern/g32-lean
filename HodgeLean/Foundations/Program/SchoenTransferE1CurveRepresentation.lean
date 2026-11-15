import HodgeLean.Foundations.Program.SchoenTransferE1Defs
import HodgeLean.Foundations.CyclicAction
import HodgeLean.RealDefs.FiniteBettiCompact

/-! The actual rational pullback representation of the supplied cyclic curve action. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The supplied group action induces the actual pullback representation in every degree.
Source: Schoen (1988), §1, p. 5; functoriality of rational cohomology. -/
def s4_e1_curvePullbackRepresentation
    {G : Type*} [Group G]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : G → (Y ⟶ Y)) (ha1 : a 1 = 𝟙 Y)
    (hamul : ∀ u v, a (u * v) = a u ≫ a v) (n : ℕ) :
    G →* Module.End ℚ (HQ Y n) where
  toFun u := homPullback (a u) n
  map_one' := by rw [ha1, spec_homPullback_id]; rfl
  map_mul' u v := by rw [hamul, spec_homPullback_comp]; rfl

/-- The pullback of a finite-order supplied automorphism has the same order relation.
Source: Schoen (1988), §1, p. 5; functoriality of rational cohomology. -/
theorem s4_e1_curvePullback_pow
    {G : Type*} [Group G]
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : G → (Y ⟶ Y)) (ha1 : a 1 = 𝟙 Y)
    (hamul : ∀ u v, a (u * v) = a u ≫ a v) (n : ℕ)
    (g : G) (m : ℕ) (hg : g ^ m = 1) : homPullback (a g) n ^ m = 1 := by
  let ρ := s4_e1_curvePullbackRepresentation Y a ha1 hamul n
  change ρ g ^ m = 1
  rw [← map_pow, hg, map_one]

/-- The literal residual generator supplied by e has m-th power equal to the identity on cohomology.
Source: Schoen (1988), §1, p. 5, the residual cyclic generator. -/
theorem s4_e1_curve_generator_pow
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v) (n : ℕ) :
    homPullback (a (e.symm (.ofAdd 1))) n ^ S.m = 1 := by
  have hp : Multiplicative.ofAdd (1 : ZMod S.m) ^ S.m = 1 := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self,
      mul_one, ofAdd_zero]
  apply s4_e1_curvePullback_pow Y a ha1 hamul n
  rw [← map_pow, hp, map_one]

/-- The actual residual pullback splits into all its root-of-unity character spaces
in every cohomological degree after extension to the complex numbers.
Source: Schoen (1988), Lemma 1.1, p. 5; finite cyclic semisimplicity. -/
theorem s4_e1_curve_character_decomposition
    (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v) (n : ℕ) :
    DirectSum.IsInternal (fun ζ : rootsOfUnity S.m ℂ =>
      Module.End.eigenspace ((homPullback (a (e.symm (.ofAdd 1))) n).baseChange ℂ)
        ((ζ : ℂˣ) : ℂ)) := by
  letI := (finbetti_finiteBetti Y).finite n
  exact HodgeLean.Foundations.isInternal_eigenspace_baseChange _
    (lt_of_lt_of_le (by decide : 0 < 3) S.three_le)
    (s4_e1_curve_generator_pow S Y a e ha1 hamul n)

#print axioms s4_e1_curvePullbackRepresentation
#print axioms s4_e1_curvePullback_pow
#print axioms s4_e1_curve_generator_pow
#print axioms s4_e1_curve_character_decomposition
end HodgeLean.Foundations.Program
