import HodgeLean.Foundations.BundleResolution.ChernDegreeLoweringChainHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeCupDifferentialHelpers

/-! # Actual even-degree cap as an integer-indexed chain comparison

The full relative complex is retained below the cap degree. The target
is the absolute singular complex extended by zero in positive degrees.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (k : ℕ) (φ : RelativeCochain ℚ P (2 * k))
variable (hφ : relativeCoboundary ℚ P (2 * k) φ = 0)

def i1_evenRelativeCapExtendedChainMap :
    ((relativeChainFunctor ℚ).obj P).extend (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ⟶
      (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj P.fst).extend
        (ComplexShape.embeddingUpIntLE 0) :=
  i1_degreeLoweringExtendedChainMap _ _ (2 * k)
    (fun n => relativeCapHom ℚ P (2 * k) n φ) (by
      intro n
      apply ModuleCat.hom_ext
      ext c
      change boundary ℚ n (relativeCap ℚ P (2 * k) (n + 1) φ c) =
        relativeCap ℚ P (2 * k) n φ (relativeBoundary ℚ P (2 * k + n) c)
      have h := LinearMap.congr_fun
        (boundary_relativeCap_eq_of_cocycle ℚ P (2 * k) n φ hφ) c
      have hs : (-1 : ℚ) ^ (2 * k) = 1 := by
        rw [pow_mul, neg_one_sq, one_pow]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, hs, one_smul] at h
      exact h)

end HodgeLean.Foundations.BundleResolution
