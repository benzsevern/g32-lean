import HodgeLean.Foundations.Program.SchoenTowerI2aReesSectionRange
import HodgeLean.Foundations.Program.SchoenTowerI2aOpenFromSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Local integral sections at every image point make the actual Rees
comparison an open immersion over its specified coefficient spectrum.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, standard charts. -/
theorem s2v_i2a_rees_open_immersion_of_sections
    (R : Type) [CommRing R] [IsDomain R] (x y : R) (hx : x ≠ 0)
    (Y : Scheme.{0}) (b : Y ⟶ Spec (CommRingCat.of R))
    (g : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ Y)
    (hg : g ≫ b = Spec.map (CommRingCat.ofHom (algebraMap R _)))
    (hsections : ∀ q : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)),
      ∃ (V : Scheme.{0}) (u : V ⟶ Y)
        (f : V ⟶ Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x))),
        IsIntegral V ∧ IsOpenImmersion u ∧ QuasiCompact u ∧ f ≫ g = u ∧
          g q ∈ Set.range u) : IsOpenImmersion g := by
  apply s2v_i2a_open_immersion_of_local_sections g
  intro q
  obtain ⟨V, u, f, hV, hu, huc, hf, hq⟩ := hsections q
  letI : IsIntegral V := hV
  letI : IsOpenImmersion u := hu
  letI : QuasiCompact u := huc
  have hfopen := (s2v_i2a_rees_local_inverse R x y hx Y V b g hg u f hf).2
  have hrange := s2v_i2a_rees_section_range R x y hx Y V b g hg u f hf
  refine ⟨V, u, f, hu, hfopen, hf, hrange, ?_⟩
  rw [hrange]
  exact hq

end HodgeLean.Foundations.Program
