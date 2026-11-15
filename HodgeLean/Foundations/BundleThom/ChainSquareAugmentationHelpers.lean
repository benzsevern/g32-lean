import HodgeLean.Foundations.BundleThom.SubcomplexMayerVietorisHelpers
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Augmenting an intersection–union chain square

The common target complex retains the base projection of all four domains.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- Compatible maps from a chain square to one complex give a map of its intersection–union sequence to the constant-square sequence.
Source: Hatcher, Algebraic Topology, §2.2, naturality of Mayer–Vietoris. -/
def i1_chainSquareAugmentation
    {A B C D T : ChainComplex (ModuleCat ℚ) ℕ}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (sq : CommSq f g i j)
    (pA : A ⟶ T) (pB : B ⟶ T) (pC : C ⟶ T) (pD : D ⟶ T)
    (hAB : f ≫ pB = pA) (hAC : g ≫ pC = pA)
    (hBD : i ≫ pD = pB) (hCD : j ≫ pD = pC) :
    sq.shortComplex ⟶
      (show CommSq (𝟙 T) (𝟙 T) (𝟙 T) (𝟙 T) from ⟨by simp⟩).shortComplex where
  τ₁ := pA
  τ₂ := biprod.map pB pC
  τ₃ := pD
  comm₁₂ := by
    dsimp [CommSq.shortComplex]
    apply biprod.hom_ext <;> simp [hAB, hAC]
  comm₂₃ := by
    dsimp [CommSq.shortComplex]
    apply biprod.hom_ext' <;> simp [hBD, hCD]

/-- The constant chain-square intersection–union sequence is short exact.
Source: Hatcher, Algebraic Topology, §2.2, the split constant Mayer–Vietoris sequence. -/
theorem i1_constantChainSquare_shortExact (T : ChainComplex (ModuleCat ℚ) ℕ) :
    (show CommSq (𝟙 T) (𝟙 T) (𝟙 T) (𝟙 T) from ⟨by simp⟩).shortComplex.ShortExact := by
  have hp : IsPushout (𝟙 T) (𝟙 T) (𝟙 T) (𝟙 T) :=
    IsPushout.of_horiz_isIso ⟨by simp⟩
  refine { exact := hp.exact_shortComplex, mono_f := ?_, epi_g := hp.epi_shortComplex_g }
  change Mono (biprod.lift (𝟙 T) (-𝟙 T))
  infer_instance

end HodgeLean.Foundations.BundleThom
