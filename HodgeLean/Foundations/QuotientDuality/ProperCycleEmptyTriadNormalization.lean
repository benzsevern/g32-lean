import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriadCohomologyCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleNormalCapScalar

/-! # Unit evaluation for the original empty-triad normal cap
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The normalized normal coclass has unit evaluation one after the original empty-triad cap and the actual inverse empty-relative projection.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3; properCycle_normalized_relative_cap_unit; properCycle_empty_triad_cohomology_cap_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_empty_triad_normalized_cap_unit
    (X : TopCat.{0}) (A : Set X) (p : ℕ) (hp : Even p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) p) (hz : z ≠ 0) :
    letI := properCycle_empty_relative_projection_isIso X
    let F := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) p).mapIso
      (properCycle_empty_triad_relative_iso X A)
    let G := HomologicalComplex.homologyMap
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))) 0
    cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X)
      ((inv G).hom (triadCapCohomologyLinear ℚ X A ∅ p 0
        (normalizedRelativeCoclass z hz) (F.inv.hom z))) = 1 := by
  letI := properCycle_empty_relative_projection_isIso X
  let F := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) p).mapIso
    (properCycle_empty_triad_relative_iso X A)
  let G := HomologicalComplex.homologyMap
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))) 0
  dsimp only
  have hc := ConcreteCategory.congr_hom
    (properCycle_empty_triad_cohomology_cap_comparison X A p 0 hp
      (normalizedRelativeCoclass z hz)) (F.inv.hom z)
  change G.hom (relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := X) A)
      p 0 (normalizedRelativeCoclass z hz) (F.hom.hom (F.inv.hom z))) =
    triadCapCohomologyLinear ℚ X A ∅ p 0 (normalizedRelativeCoclass z hz) (F.inv.hom z) at hc
  rw [show F.hom.hom (F.inv.hom z) = z from ConcreteCategory.congr_hom F.inv_hom_id z] at hc
  rw [← hc]
  have he := ConcreteCategory.congr_hom (IsIso.hom_inv_id G)
    (relativeCapCohomologyLinear ℚ (TopPair.ofSubset (X := X) A) p 0
      (normalizedRelativeCoclass z hz) z)
  change (inv G).hom (G.hom _) = _ at he
  rw [he]
  exact properCycle_normalized_relative_cap_unit _ p z hz

/-- Unit evaluation after the actual empty-triad cap detects every change in the original source coefficient, including zero and sign reversal.
Source: properCycle_empty_triad_normalized_cap_unit; linearity of the original cap and evaluation maps.
HC no distance; AV milestone no distance. -/
theorem properCycle_empty_triad_source_scale_detected
    (X : TopCat.{0}) (A : Set X) (p : ℕ) (hp : Even p)
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) p) (hz : z ≠ 0) (q : ℚ) :
    letI := properCycle_empty_relative_projection_isIso X
    let F := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) p).mapIso
      (properCycle_empty_triad_relative_iso X A)
    let G := HomologicalComplex.homologyMap
      (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (∅ : Set X))) 0
    cohomologyEquivDualHomology ℚ X 0 (unit (R := ℚ) X)
      ((inv G).hom (triadCapCohomologyLinear ℚ X A ∅ p 0
        (normalizedRelativeCoclass z hz) (F.inv.hom (q • z)))) = 1 ↔ q = 1 := by
  have h := properCycle_empty_triad_normalized_cap_unit X A p hp z hz
  dsimp only at h ⊢
  simp only [map_smul]
  rw [h]
  simp only [smul_eq_mul, mul_one]

end HodgeLean.Foundations.QuotientDuality
