import HodgeLean.Foundations.BundleResolution.ChernThomNonzeroHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # The actual normalized normal coclass as a scalar basis

Evaluation on the prescribed complex local homology generator gives the
inverse to scalar multiplication by the actual normalized coclass.
HC no distance; AV milestone no distance. -/

noncomputable section
open AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleResolution

theorem i1_normalizedPointCoclass_scalar_bijective (k : ℕ) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ
      (RelativeCohomology ℚ (puncturedPair ℂ k) (2 * k)) (normalizedPointCoclass k)) := by
  let z := standardComplexLocalClass ℚ k
  let e := relativeCohomologyEquivDualHomology ℚ (puncturedPair ℂ k) (2 * k)
  have hn : e (normalizedPointCoclass k) z = 1 :=
    normalizedRelativeCoclass_pairing_self z (standardComplexLocalClass_ne_zero_for_chart k)
  constructor
  · intro a b h
    change a • normalizedPointCoclass k = b • normalizedPointCoclass k at h
    exact smul_left_injective ℚ (i1_normalizedPointCoclass_ne_zero k) h
  · intro β
    refine ⟨e β z, ?_⟩
    apply e.injective
    apply LinearMap.ext_on (s := {z}) (span_standardComplexLocalClass_eq_top_for_chart k)
    rintro _ rfl
    change e ((e β z) • normalizedPointCoclass k) z = e β z
    rw [map_smul, LinearMap.smul_apply, hn, smul_eq_mul, mul_one]

end HodgeLean.Foundations.BundleResolution
