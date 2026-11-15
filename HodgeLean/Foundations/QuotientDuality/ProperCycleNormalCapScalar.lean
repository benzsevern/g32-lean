import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeCapEvaluation
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # Actual normalized scalar of the original normal relative cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original normalized relative coclass caps its actual nonzero normal orientation to a degree-zero class with original unit evaluation one.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3, normalized relative duals and cap evaluation.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_relative_cap_unit
    (P : TopPair.{0}) (p : ℕ) (z : RelativeHomology ℚ P p) (hz : z ≠ 0) :
    cohomologyEquivDualHomology ℚ P.fst 0 (unit (R := ℚ) P.fst)
      (relativeCapCohomologyLinear ℚ P p 0 (normalizedRelativeCoclass z hz) z) = 1 := by
  rw [properCycle_relative_cap_unit_evaluation]
  exact normalizedRelativeCoclass_pairing_self z hz

/-- Capping by the original normalized relative coclass is an actual isomorphism from a normal homology line to degree-zero homology when that target has dimension one.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3, normal orientation lines and cap evaluation.
HC no distance; AV milestone no distance. -/
lemma properCycle_normalized_relative_cap_bijective
    (P : TopPair.{0}) (p : ℕ) (z : RelativeHomology ℚ P p) (hz : z ≠ 0)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeHomology ℚ P p) z))
    (hdim : Module.finrank ℚ (Homology ℚ P.fst 0) = 1) :
    Function.Bijective (relativeCapCohomologyLinear ℚ P p 0 (normalizedRelativeCoclass z hz)) := by
  let F := relativeCapCohomologyLinear ℚ P p 0 (normalizedRelativeCoclass z hz)
  have hw : F z ≠ 0 := by
    intro hh
    have h := properCycle_normalized_relative_cap_unit P p z hz
    change cohomologyEquivDualHomology ℚ P.fst 0 (unit (R := ℚ) P.fst) (F z) = 1 at h
    rw [hh, map_zero] at h
    exact zero_ne_one h
  constructor
  · intro a b hab
    obtain ⟨r, hr⟩ := hgen.2 a
    obtain ⟨s, hs⟩ := hgen.2 b
    change r • z = a at hr
    change s • z = b at hs
    have hsc : r • F z = s • F z := by
      rw [← map_smul, ← map_smul, hr, hs]
      exact hab
    have hrs := smul_left_injective ℚ hw hsc
    rw [← hr, ← hs, hrs]
  · intro b
    obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' (F z) hw).mp hdim b
    exact ⟨r • z, (map_smul F r z).trans hr⟩

end HodgeLean.Foundations.QuotientDuality
