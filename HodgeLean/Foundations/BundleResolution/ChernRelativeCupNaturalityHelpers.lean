import HodgeLean.Foundations.BundleResolution.ChernRelativeCupCochainHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! # Relative cup cochains under actual pair maps

Pullback on the relative chain quotient respects the absolute comparison
and the Alexander–Whitney cup action.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.BundleResolution

variable {P Q : TopPair} (f : P ⟶ Q)

def i1_relativeCochainPullback (n : ℕ) :
    RelativeCochain ℚ Q n →ₗ[ℚ] RelativeCochain ℚ P n :=
  (((relativeChainFunctor ℚ).map f).f n).hom.dualMap

theorem i1_relativeCochainPullback_coboundary (n : ℕ) (φ : RelativeCochain ℚ Q n) :
    i1_relativeCochainPullback f (n + 1) (relativeCoboundary ℚ Q n φ) =
      relativeCoboundary ℚ P n (i1_relativeCochainPullback f n φ) := by
  ext c
  exact congrArg φ (ConcreteCategory.congr_hom
    (((relativeChainFunctor ℚ).map f).comm (n + 1) n) c)

theorem i1_relativeCochainPullback_toAbsolute (n : ℕ) (φ : RelativeCochain ℚ Q n) :
    relativeCochainToAbsolute ℚ P n (i1_relativeCochainPullback f n φ) =
      cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) n (relativeCochainToAbsolute ℚ Q n φ) := by
  ext c
  have h := congrArg (fun g => g.f n) (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  exact congrArg φ (ConcreteCategory.congr_hom h c)

theorem i1_relativeCupCochain_naturality (p q : ℕ)
    (φ : RelativeCochain ℚ Q p) (ψ : Cochain ℚ (TopCat.toSSet.obj Q.fst) q) :
    i1_relativeCochainPullback f (p + q) (i1_relativeCupCochain Q p q φ ψ) =
      i1_relativeCupCochain P p q (i1_relativeCochainPullback f p φ)
        (cochainMap ℚ (TopCat.toSSet.map (TopPair.Hom.fst f)) q ψ) := by
  apply i1_relativeCochainToAbsolute_injective P (p + q)
  rw [i1_relativeCochainPullback_toAbsolute, i1_relativeCupCochain_toAbsolute,
    HodgeLean.Foundations.Singular.cupCochain_naturality,
    i1_relativeCupCochain_toAbsolute, i1_relativeCochainPullback_toAbsolute]

end HodgeLean.Foundations.BundleResolution
