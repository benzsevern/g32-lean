import HodgeLean.Foundations.BundleResolution.ChernRelativeCupForgetHelpers
import HodgeLean.Foundations.BundleResolution.ChernThomNonzeroHelpers

/-! # Actual point classes acting on the normalized normal coclass

The constant map from the original normal space to a point identifies
this cup action with scalar multiplication by its prescribed coclass.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

def i1_normalPointCupMap (k : ℕ) :
    Cohomology ℚ (TopCat.of PUnit) 0 →ₗ[ℚ]
      RelativeCohomology ℚ (puncturedPair ℂ k) (2 * k) :=
  (i1_relativeCup (puncturedPair ℂ k) (2 * k) 0 (normalizedPointCoclass k)).comp
    (cohomologyMap ℚ 0 (TopCat.ofHom (ContinuousMap.const _ PUnit.unit)))

theorem i1_normalPointCupMap_smul_unit (k : ℕ) (a : ℚ) :
    i1_normalPointCupMap k (a • unit (TopCat.of PUnit)) =
      a • normalizedPointCoclass k := by
  change i1_relativeCup (puncturedPair ℂ k) (2 * k) 0 (normalizedPointCoclass k)
    (cohomologyMap ℚ 0 (TopCat.ofHom (ContinuousMap.const _ PUnit.unit))
      (a • unit (TopCat.of PUnit))) = _
  rw [map_smul, cohomologyMap_unit]
  erw [map_smul, i1_relativeCup_one]

theorem i1_normalPointCupMap_injective (k : ℕ) :
    Function.Injective (i1_normalPointCupMap k) := by
  intro α β h
  let a := pointCohomologyZeroEquiv (R := ℚ) α
  let b := pointCohomologyZeroEquiv (R := ℚ) β
  have ha : a • unit (TopCat.of PUnit) = α :=
    (pointCohomologyZeroEquiv (R := ℚ)).injective
      (pointCohomologyZeroEquiv_smul_unit a)
  have hb : b • unit (TopCat.of PUnit) = β :=
    (pointCohomologyZeroEquiv (R := ℚ)).injective
      (pointCohomologyZeroEquiv_smul_unit b)
  rw [← ha, ← hb, i1_normalPointCupMap_smul_unit, i1_normalPointCupMap_smul_unit] at h
  have hab := smul_left_injective ℚ (i1_normalizedPointCoclass_ne_zero k) h
  exact ha.symm.trans ((congrArg (fun c : ℚ => c • unit (TopCat.of PUnit)) hab).trans hb)

end HodgeLean.Foundations.BundleResolution
