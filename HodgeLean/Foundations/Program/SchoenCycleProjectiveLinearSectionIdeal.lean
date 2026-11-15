import HodgeLean.Foundations.Program.SchoenCycleProjectiveLinearSection
import HodgeLean.Foundations.Program.SchoenCycleNormalizedLinearIdeal

/-! # Reduced principal ideals of actual regular projective linear sections -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The principal ideal of the actual standard-chart regular linear section is radical.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv), printed p. 14;
Lemma 2.4, printed p. 15; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_standardProjectiveLinearSection_span_isRadical
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k : ℕ) (hd : Module.finrank ℂ V = k + 1) (L : V →ₗ[ℂ] ℂ) (i : Fin (k + 1)) :
    (Ideal.span ({s2e_standardProjectiveLinearSection V k hd L i} :
      Set Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
        (s2e_standardProjectiveAffineOpen i).1))).IsRadical := by
  let e := s2e_standardProjectiveSectionRingEquiv i
  let J := Ideal.span ({s2e_standardProjectiveLinearSection V k hd L i} :
    Set Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
      (s2e_standardProjectiveAffineOpen i).1))
  have he : (J.map e.toRingHom).IsRadical := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    change (Ideal.span ({(e (s2e_standardProjectiveLinearSection V k hd L i))} : Set _)).IsRadical
    dsimp only [e, s2e_standardProjectiveLinearSection]
    rw [RingEquiv.apply_symm_apply]
    exact s2e_normalized_linear_span_isRadical i (fun j => L (Module.finBasisOfFinrankEq ℂ V hd j))
  have hc := he.comap e.toRingHom
  rw [J.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

end HodgeLean.Foundations.Program
