import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalAffineCoordinateSections
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartDomainPoints

/-! # The actual native affine chart of the projective normal base -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified affine parameterization into the actual projective scheme points. -/
def normalSchemeAffineParam (k : ℕ) (z : Fin k → ℂ) :
    ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :=
  normalProjectiveSchemeHomeomorph k (normalProjectiveChart k z)

/-- The actual affine scheme-point parameterization is an open embedding. -/
theorem isOpenEmbedding_normalSchemeAffineParam (k : ℕ) :
    Topology.IsOpenEmbedding (normalSchemeAffineParam k) :=
  (normalProjectiveSchemeHomeomorph k).isOpenEmbedding.comp
    (isOpenEmbedding_normalProjectiveChart k)

/-- The actual native affine chart, with its full parameter domain retained. -/
def normalSchemeAffineChart (k : ℕ) :
    OpenPartialHomeomorph
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
      (Fin k → ℂ) :=
  ((isOpenEmbedding_normalSchemeAffineParam k).toOpenPartialHomeomorph
    (normalSchemeAffineParam k)).symm

#print axioms normalSchemeAffineParam
#print axioms isOpenEmbedding_normalSchemeAffineParam
#print axioms normalSchemeAffineChart
/-- The leading chart of the actual projective scheme is exactly the model's specified affine chart. -/
theorem normalProjectiveSchemeHomeomorph_chart_domain (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) :
    (normalProjectiveSchemeHomeomorph k p).underlying ∈
      (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1 ↔
        p ∈ Set.range (normalProjectiveChart k) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [normalProjectiveSchemeHomeomorph_mk,
      s2e_standardProjectiveAffineOpen_mem_iff, normalProjectiveChart_range_mk]
    rfl

#print axioms normalProjectiveSchemeHomeomorph_chart_domain
/-- The actual regular coordinate section recovers each specified affine parameter. -/
theorem normalAffineCoordinateSection_param (k : ℕ) (j : Fin k) (z : Fin k → ℂ) :
    Point.evaluate (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1
      (normalAffineCoordinateSection k j) (normalSchemeAffineParam k z) = z j := by
  change Point.evaluate _ _
    (vectorToComplexPoint (Fin.cons (1 : ℂ) z) _) = z j
  rw [normalAffineCoordinateSection_evaluate k j _ (by simp)]
  simp only [Fin.cons_succ, Fin.cons_zero, div_one]

#print axioms normalAffineCoordinateSection_param
/-- The actual native affine chart recovers the specified parameters exactly. -/
theorem normalSchemeAffineChart_param (k : ℕ) (z : Fin k → ℂ) :
    normalSchemeAffineChart k (normalSchemeAffineParam k z) = z :=
  (isOpenEmbedding_normalSchemeAffineParam k).toOpenPartialHomeomorph_left_inv _

#print axioms normalSchemeAffineChart_param
/-- The actual native affine chart has precisely the parameterization image as its source. -/
theorem normalSchemeAffineChart_source (k : ℕ) :
    (normalSchemeAffineChart k).source = Set.range (normalSchemeAffineParam k) := by
  simp only [normalSchemeAffineChart, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]

#print axioms normalSchemeAffineChart_source
/-- The actual scheme-point parameter image is precisely the native leading affine open. -/
theorem normalSchemeAffineParam_range (k : ℕ) :
    Set.range (normalSchemeAffineParam k) =
      Point.overOpen (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1 := by
  ext q
  obtain ⟨p, rfl⟩ := (normalProjectiveSchemeHomeomorph k).surjective q
  change (∃ z, normalProjectiveSchemeHomeomorph k (normalProjectiveChart k z) =
    normalProjectiveSchemeHomeomorph k p) ↔
      (normalProjectiveSchemeHomeomorph k p).underlying ∈
        (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1
  rw [normalProjectiveSchemeHomeomorph_chart_domain]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (normalProjectiveSchemeHomeomorph k).injective hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, congrArg (normalProjectiveSchemeHomeomorph k) hz⟩

#print axioms normalSchemeAffineParam_range
/-- Every actual inverse chart coordinate is its specified regular section evaluation on the same native chart source. -/
theorem normalSchemeAffineChart_coordinate (k : ℕ) (j : Fin k)
    (q : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (hq : q ∈ (normalSchemeAffineChart k).source) :
    normalSchemeAffineChart k q j =
      Point.evaluate (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1
        (normalAffineCoordinateSection k j) q := by
  rw [normalSchemeAffineChart_source] at hq
  obtain ⟨z, rfl⟩ := hq
  rw [normalSchemeAffineChart_param, normalAffineCoordinateSection_param]

#print axioms normalSchemeAffineChart_coordinate
end HodgeLean.Foundations.Program.G32Native.EulerModel
