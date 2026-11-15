import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalCapScalar
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeGenerator

/-! # Actual normal cap with a fixed relative orientation
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- A relative homology generator makes the actual degree-zero cap injective in its cohomology variable.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3, universal coefficients and cap evaluation.
HC no distance; AV milestone no distance. -/
lemma properCycle_oriented_normal_cap_injective
    (P : TopPair.{0}) (p : ℕ) (z : RelativeHomology ℚ P p)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeHomology ℚ P p) z)) :
    Function.Injective (fun a : RelativeCohomology ℚ P p =>
      relativeCapCohomologyLinear ℚ P p 0 a z) := by
  intro a b hab
  apply (relativeCohomologyEquivDualHomology ℚ P p).injective
  apply LinearMap.ext
  intro v
  obtain ⟨r, hr⟩ := hgen.2 v
  change r • z = v at hr
  rw [← hr, map_smul, map_smul]
  congr 1
  have he := congrArg (cohomologyEquivDualHomology ℚ P.fst 0
    (HodgeLean.Foundations.Singular.unit (R := ℚ) P.fst)) hab
  simpa only [properCycle_relative_cap_unit_evaluation] using he

/-- A fixed relative orientation identifies normal cohomology with actual degree-zero homology when that target has dimension one.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3, cap evaluation on rational orientation lines.
HC no distance; AV milestone no distance. -/
lemma properCycle_oriented_normal_cap_bijective
    (P : TopPair.{0}) (p : ℕ) (z : RelativeHomology ℚ P p)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeHomology ℚ P p) z))
    (hdim : Module.finrank ℚ (Homology ℚ P.fst 0) = 1) :
    Function.Bijective (fun a : RelativeCohomology ℚ P p =>
      relativeCapCohomologyLinear ℚ P p 0 a z) := by
  refine ⟨properCycle_oriented_normal_cap_injective P p z hgen, ?_⟩
  have hz : z ≠ 0 := by
    intro hz
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (hgen.1 (by simp [hz]))
  let α := normalizedRelativeCoclass z hz
  have hcap := properCycle_normalized_relative_cap_bijective P p z hz hgen hdim
  intro b
  obtain ⟨v, hv⟩ := hcap.2 b
  obtain ⟨r, hr⟩ := hgen.2 v
  change r • z = v at hr
  refine ⟨r • α, ?_⟩
  change relativeCapCohomologyLinear ℚ P p 0 (r • α) z = b
  rw [map_smul, LinearMap.smul_apply]
  rw [← hr, map_smul] at hv
  exact hv

/-- The specified normalized relative coclass generates the actual dual orientation line.
Source: Hatcher, Algebraic Topology, section 3.1, universal coefficients over a field.
HC no distance; AV milestone no distance. -/
lemma properCycle_specified_normal_coclass_generates
    (P : TopPair.{0}) (p : ℕ) (z : RelativeHomology ℚ P p) (hz : z ≠ 0)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeHomology ℚ P p) z)) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeCohomology ℚ P p)
      (normalizedRelativeCoclass z hz)) := by
  obtain ⟨β, hβ, hβgen⟩ := properCycle_relative_normalized_generator P p z hgen
  obtain ⟨r, hr⟩ := hβgen.2 (normalizedRelativeCoclass z hz)
  change r • β = normalizedRelativeCoclass z hz at hr
  have hr1 : r = 1 := by
    have hh := congrArg (fun a : RelativeCohomology ℚ P p =>
      relativeCohomologyEquivDualHomology ℚ P p a z) hr
    simpa only [map_smul, LinearMap.smul_apply, hβ, smul_eq_mul, mul_one,
      normalizedRelativeCoclass_pairing_self] using hh
  have he : β = normalizedRelativeCoclass z hz := by simpa only [hr1, one_smul] using hr
  rwa [← he]

end HodgeLean.Foundations.QuotientDuality
