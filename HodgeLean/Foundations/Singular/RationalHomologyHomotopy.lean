import HodgeLean.Foundations.Singular.RationalContractionIdentity
import HodgeLean.Foundations.Singular.RationalHomologyChainMaps

/-! The actual deformation homotopy to the chosen rational homology representatives. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Singular

/-- Every actual rational chain complex retracts up to chain homotopy onto its chosen homology representatives.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyDeformationHomotopy (K : ChainComplex (ModuleCat ℚ) ℕ) :
    Homotopy (𝟙 K) (rationalHomologyChainProjection K ≫ rationalHomologyChainInclusion K) where
  hom i j := if h : i + 1 = j then by
    subst j
    exact ModuleCat.ofHom (rationalChainContraction K i)
    else 0
  zero i j hij := by
    rw [dif_neg]
    simpa using hij
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)]
      erw [dif_pos rfl]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change z = 0 + (K.d 1 0).hom (rationalChainContraction K 0 z) +
        rationalHomologyInclusion K 0 (rationalHomologyProjection K 0 z)
      simpa only [zero_add] using (rationalChainContraction_identity_zero K z).symm
    | succ n =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by simp)]
      erw [dif_pos rfl, dif_pos rfl]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (rationalChainContraction_identity_succ K n z).symm

#print axioms rationalHomologyDeformationHomotopy
end HodgeLean.Foundations.Singular
