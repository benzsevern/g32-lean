import HodgeLean.Foundations.BundleResolution.ChernRelativeCupCochainHelpers

/-! # Differentials of relative cup multiplication by a cocycle

An even-degree relative cocycle acts by a degree-shifting cochain map.
The differential identity holds for arbitrary second cochains.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.BundleResolution

variable (P : TopPair) (p q : ℕ)

theorem i1_relativeCupCochain_coboundary_right
    (φ : RelativeCochain ℚ P p) (hφ : relativeCoboundary ℚ P p φ = 0)
    (ψ : Cochain ℚ (TopCat.toSSet.obj P.fst) q) :
    relativeCoboundary ℚ P (p + q) (i1_relativeCupCochain P p q φ ψ) =
      (-1 : ℚ) ^ p • i1_relativeCupCochain P p (q + 1) φ (coboundary ℚ q ψ) := by
  apply i1_relativeCochainToAbsolute_injective P (p + q + 1)
  have ha := congrArg (relativeCochainToAbsolute ℚ P (p + 1)) hφ
  rw [relativeCochainToAbsolute_coboundary, map_zero] at ha
  rw [relativeCochainToAbsolute_coboundary, i1_relativeCupCochain_toAbsolute,
    HodgeLean.Foundations.Singular.coboundary_cupCochain, ha]
  simp only [map_zero, LinearMap.zero_apply, LinearMap.zero_comp, zero_add,
    map_smul]
  exact congrArg (fun v => (-1 : ℚ) ^ p • v)
    (i1_relativeCupCochain_toAbsolute P p (q + 1) φ (coboundary ℚ q ψ)).symm

theorem i1_relativeCupCochain_even_coboundary_right (k : ℕ)
    (φ : RelativeCochain ℚ P (2 * k))
    (hφ : relativeCoboundary ℚ P (2 * k) φ = 0)
    (ψ : Cochain ℚ (TopCat.toSSet.obj P.fst) q) :
    relativeCoboundary ℚ P (2 * k + q) (i1_relativeCupCochain P (2 * k) q φ ψ) =
      i1_relativeCupCochain P (2 * k) (q + 1) φ (coboundary ℚ q ψ) := by
  rw [i1_relativeCupCochain_coboundary_right P (2 * k) q φ hφ ψ,
    pow_mul, neg_one_sq, one_pow, one_smul]

end HodgeLean.Foundations.BundleResolution
