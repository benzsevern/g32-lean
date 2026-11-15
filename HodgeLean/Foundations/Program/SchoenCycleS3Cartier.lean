import HodgeLean.Foundations.Program.SchoenCycleChartIdeals
import HodgeLean.Foundations.Program.SchoenCycleCartierLocalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program

theorem s2e_ideal_free_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (z : S)
    (hI : Ideal.map e.toRingHom I = Ideal.span {z})
    (hz : Function.Injective (fun a : S => a * z)) :
    Nonempty (I ≃ₗ[R] R) := by
  have hi : I = Ideal.span {e.symm z} := by
    calc
      I = Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom I) := (Ideal.map_of_equiv e).symm
      _ = Ideal.span {e.symm z} := by
        rw [hI, Ideal.map_span, Set.image_singleton]
        rfl
  rw [hi]
  apply s2e_regular_principal_ideal_free
  intro a b hab
  apply e.injective
  apply hz
  simpa only [map_mul, RingEquiv.apply_symm_apply] using congrArg e hab

theorem s2e_residue_parameter_regular {k : ℕ} (i j : Fin (k + 1)) :
    Function.Injective (fun a : MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ =>
      a * s2e_s2b_chartHom i (chartCoordinate i j)) := by
  classical
  rw [s2e_chartHom_coordinate]
  split_ifs with h
  · intro a b hab
    simpa only [mul_one] using hab
  · intro a b hab
    exact mul_right_cancel₀ (MvPolynomial.X_ne_zero (R := ℂ) (σ := {q : Fin (k + 1) // q ≠ i}) ⟨j, h⟩) hab

theorem s2e_residue_chart_free {k : ℕ} (i j : Fin (k + 1)) :
    let U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens :=
      ⟨s2e_s2b_chart i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩
    Nonempty ((s2e_s2b_residueIdeal k j).ideal U ≃ₗ[Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), U)] Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), U)) := by
  classical
  let f := s2e_s2b_chart i
  let R := MvPolynomial {q : Fin (k + 1) // q ≠ i} ℂ
  let e := (f.appIso ⊤).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  apply s2e_ideal_free_of_ringEquiv e _ (s2e_s2b_chartHom i (chartCoordinate i j))
  · have hh := s2e_residueIdeal_chart i j
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
      (s2e_s2b_residueIdeal k j) f ⟨⊤, isAffineOpen_top _⟩] at hh
    have he : (((s2e_s2b_residueIdeal k j).ideal
          ⟨f ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion f⟩).comap
          (f.appIso ⊤).inv.hom) =
        Ideal.map (f.appIso ⊤).hom.hom ((s2e_s2b_residueIdeal k j).ideal
          ⟨f ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion f⟩) :=
      Ideal.comap_symm (f.appIso ⊤).commRingCatIsoToRingEquiv
    rw [he, Ideal.map_map] at hh
    exact hh
  · exact s2e_residue_parameter_regular i j

end HodgeLean.Foundations.Program
