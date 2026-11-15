import HodgeLean.Foundations.Program.SchoenSegrePowerSections
import HodgeLean.Foundations.Program.SchoenFiniteProductSections
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Charts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A tuple differing in one coordinate recovers the actual normalized coordinate of that factor. -/
theorem s2_segrePowerSections_X_update (d n : ℕ) (a : Fin n → Fin (d + 1))
    (i : Fin n) (k : Fin (d + 1)) :
    s2_segrePowerSections d n a (X (Function.update a i k)) = s2_segrePowerCoord d n a i k := by
  classical
  rw [s2_segrePowerSections_X]
  calc
    _ = s2_segrePowerCoord d n a i (Function.update a i k i) :=
      Finset.prod_eq_single i (fun j _ hji => by
        rw [Function.update_of_ne hji, s2_segrePowerCoord_self]) (by simp)
    _ = _ := by simp only [Function.update_self]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite-factor Segre chart evaluation is surjective onto its affine product section ring. -/
theorem s2_segrePowerSections_surjective (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    Function.Surjective (s2_segrePowerSections d n a) := by
  classical
  intro z
  change z ∈ (s2_segrePowerSections d n a).range
  refine s2_schemeProduct_sections_mem n _ (s2_segrePowerSections d n a).range ?_ z
  intro i b
  let φ : Away (UniversalGrading d) (X (a i)) →+* Γ(s2_segrePowerChart d n a, ⊤) :=
    (s2_schemeProductπ n _ i).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (Away (UniversalGrading d) (X (a i))))).inv.hom
  let e := (Scheme.ΓSpecIso (CommRingCat.of
    (Away (UniversalGrading d) (X (a i))))).commRingCatIsoToRingEquiv
  obtain ⟨c, rfl⟩ := e.symm.surjective b
  change φ c ∈ (s2_segrePowerSections d n a).range
  have htop : Algebra.adjoin (UniversalGrading d 0)
      (Set.range (chartCoordinate (a i))) = ⊤ :=
    b54_away_adjoin_ratios_eq_top (UniversalGrading d) (isHomogeneous_X _ (a i))
      (X : Fin (d + 1) → UniversalRing d) (isHomogeneous_X _) (adjoin_coordinates_eq_top d)
  have hc : c ∈ Algebra.adjoin (UniversalGrading d 0)
      (Set.range (chartCoordinate (a i))) := by rw [htop]; trivial
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨X (Function.update a i k), s2_segrePowerSections_X_update d n a i k⟩
  | algebraMap c =>
    let e₀ : UniversalGrading d 0 ≃+* ℤ :=
      (ProjectiveSpace.degreeZeroEquiv (Fin (d + 1)) (ULift.{0} ℤ)).trans ULift.ringEquiv
    have hc : c = (e₀ c : UniversalGrading d 0) := by
      apply e₀.injective
      simp only [map_intCast, Int.cast_id]
    rw [hc, map_intCast, map_intCast]
    exact intCast_mem _ (e₀ c)
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (s2_segrePowerSections d n a).range.add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact (s2_segrePowerSections d n a).range.mul_mem hx hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each actual Segre tuple-chart morphism is a closed immersion after restriction to its selected projective target chart. -/
theorem s2_segrePowerChartMap_restrict_isClosedImmersion (d n : ℕ)
    (a : Fin n → Fin (d + 1)) :
    IsClosedImmersion (s2_segrePowerChartMap d n a ∣_
      Proj.basicOpen (homogeneousSubmodule (Fin n → Fin (d + 1)) (ULift.{0} ℤ)) (X a)) :=
  g3c_isClosedImmersion_fromOfGlobalSections_restrict _ _
    (s2_segrePowerSections_irrelevant d n a) (s2_segrePowerSections_surjective d n a)
    (isHomogeneous_X _ a) (s2_segrePowerSections_X_self d n a)

end HodgeLean.Foundations.Program
