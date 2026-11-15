import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveIdealGenerators

/-! # Retained ratio sections under the original projective immersion -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Pullback of a retained coordinate ratio is the same ratio on the
literal original source standard open, with the same index order. -/
theorem paired_c3_projective_inclusion_retained_section {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1)) (i l : Fin (k + 1)) :
    (pairedC3PolynomialCoordinateInclusion (A := ℂ) e).appLE
      (ProjSpace.standardOpen ℂ n (e i)) (ProjSpace.standardOpen ℂ k i)
      (paired_c3_coordinate_inclusion_preimage_basicOpen (A := ℂ) e i).ge
      (ProjSpace.coordinateRatioSection ℂ n (e i) (e l)) =
        ProjSpace.coordinateRatioSection ℂ k i l := by
  let f := pairedC3GradedCoordinateProjection (A := ℂ) e
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change (localRingHom f _ _ rfl _).val = _
  rw [val_localRingHom]
  let P := x.val.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := x.val.isPrime
  have hx : X i ∈ P.primeCompl := x.property
  have ha : X (e i) ^ 1 ∈ (P.comap f.toRingHom).primeCompl := by
    change f (X (e i) ^ 1) ∉ P
    rw [map_pow, pow_one]
    change pairedC3GradedCoordinateProjection (A := ℂ) e (X (e i)) ∉ P
    rw [paired_c3_coordinate_projection_variable]
    exact hx
  change Localization.localRingHom (P.comap f.toRingHom) P f.toRingHom rfl
    (Localization.mk (X (e l)) ⟨X (e i) ^ 1, ha⟩) =
      Localization.mk (X l) ⟨X i ^ 1, pow_mem hx 1⟩
  rw [Localization.localRingHom_mk]
  congr 1
  · exact paired_c3_coordinate_projection_variable e l
  · apply Subtype.ext
    simp only [map_pow]
    exact congrArg (fun z => z ^ 1) (paired_c3_coordinate_projection_variable (A := ℂ) e i)

end HodgeLean.Foundations.Program.G32Native
