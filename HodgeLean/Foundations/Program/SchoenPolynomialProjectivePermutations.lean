import HodgeLean.Foundations.Program.SchoenSegreCoordinateCoefficients
import HodgeLean.Foundations.Program.SchoenTerminalBaseChange

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial projective-space comparison retains its integral Proj coordinate map. -/
theorem s2_polynomialProjectiveSpaceIso_snd (R ι : Type) [CommRing R] :
    (s2_polynomialProjectiveSpaceIso R ι).hom ≫
        pullback.snd (terminal.from (Spec (.of R)))
          (terminal.from (Proj (homogeneousSubmodule ι (ULift.{0} ℤ)))) =
      Proj.map (s2_polynomialIntegralCoordinates R ι)
        (s2_polynomialIntegralCoordinates_irrelevant R ι) := by
  simp only [s2_polynomialProjectiveSpaceIso, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_snd, Category.comp_id, b54_relativeProj,
    pullback.lift_snd]

/-- The actual polynomial projective-space comparison intertwines tuple-coordinate permutations with integral base change. -/
theorem s2_polynomialProjectiveSpaceIso_permute (R : Type) [CommRing R] (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    s2_segreCoordinateMap R d n σ ≫
        (s2_polynomialProjectiveSpaceIso R (Fin n → Fin (d + 1))).hom =
      (s2_polynomialProjectiveSpaceIso R (Fin n → Fin (d + 1))).hom ≫
        ((s2_terminalBaseChange (Spec (.of R))).map
          (s2_segreCoordinateMap (ULift.{0} ℤ) d n σ)).left := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ ProjectiveSpace.toBase (Fin n → Fin (d + 1)) (Spec (.of R)) = _
    rw [Category.assoc, s2_polynomialProjectiveSpaceIso_toBase,
      ← Category.assoc, s2_segreCoordinateMap_toSpecZero]
    simp only [Category.assoc, s2_terminalBaseChange, Over.homMk_left,
      pullback.map, pullback.lift_fst, Category.comp_id]
    exact (s2_polynomialProjectiveSpaceIso_toBase R _).symm
  · rw [Category.assoc, s2_polynomialProjectiveSpaceIso_snd, Category.assoc,
      s2_terminalBaseChange_map_snd, ← Category.assoc,
      s2_polynomialProjectiveSpaceIso_snd]
    unfold s2_segreCoordinateMap
    rw [← Proj.map_comp, ← Proj.map_comp]
    congr 1
    exact s2_polynomialIntegralCoordinates_rename R d n σ

end HodgeLean.Foundations.Program
