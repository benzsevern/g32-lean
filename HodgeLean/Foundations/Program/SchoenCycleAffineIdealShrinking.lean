import HodgeLean.Foundations.Program.SchoenCycleAffineCurveParameter
import HodgeLean.Foundations.Program.SchoenCycleLocalizationShrinking
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Shrinking finite ideal comparisons around an actual scheme point -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two finite ideals on an affine chart that agree in an actual stalk
agree on a smaller affine neighborhood of that point.
Source: Hartshorne, Algebraic Geometry, II.5; Atiyah–Macdonald,
Introduction to Commutative Algebra, Chapter 3. -/
theorem s2e_affine_ideals_equal_near_point
    (X : Scheme) (U : X.affineOpens) (p : X) (hp : p ∈ U.1)
    (I J : Ideal Γ(X, U.1)) (hI : I.FG) (hJ : J.FG)
    (h : I.map (X.presheaf.germ U.1 p hp).hom =
      J.map (X.presheaf.germ U.1 p hp).hom) :
    ∃ (V : X.affineOpens) (hVU : V ≤ U), p ∈ V.1 ∧
      I.map (X.presheaf.map (homOfLE (X := X.Opens) hVU).op).hom =
        J.map (X.presheaf.map (homOfLE (X := X.Opens) hVU).op).hom := by
  let P := (U.2.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk p) P := U.2.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨s, hs, he⟩ := s2e_finite_ideals_localized_equality_denominator
    P.primeCompl I J hI hJ h
  letI := U.2.isLocalization_basicOpen s
  refine ⟨X.affineBasicOpen s, X.affineBasicOpen_le s, ?_, ?_⟩
  · apply (X.mem_basicOpen s p hp).mpr
    exact IsLocalization.map_units (X.presheaf.stalk p) (⟨s, hs⟩ : P.primeCompl)
  · apply he
    exact IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen s)) s

#print axioms s2e_affine_ideals_equal_near_point
/-- A specified generator of an ideal-sheaf stalk is represented by a section
that generates the retained ideal on a smaller affine neighborhood.
Source: Hartshorne, Algebraic Geometry, II.5, finite generation and stalks. -/
theorem s2e_affine_generator_of_stalk_generator
    (X : Scheme) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (U : X.affineOpens) (p : X) (hp : p ∈ U.1) (d : X.presheaf.stalk p)
    (hd : (I.ideal U).map (X.presheaf.germ U.1 p hp).hom = Ideal.span {d}) :
    ∃ (W : X.affineOpens) (hWU : W ≤ U) (hpW : p ∈ W.1) (c : Γ(X, W.1)),
      I.ideal W = Ideal.span {c} ∧ (X.presheaf.germ W.1 p hpW).hom c = d := by
  obtain ⟨V, hV, hVU, hpV, c, hc⟩ := s2e_affine_germ_representative X p U.1 hp d
  let Vb : X.affineOpens := ⟨V, hV⟩
  have hv : (I.ideal Vb).map (X.presheaf.germ V p hpV).hom =
      (Ideal.span {c}).map (X.presheaf.germ V p hpV).hom := by
    rw [← I.map_ideal (show Vb ≤ U from hVU), Ideal.map_map,
      ← CommRingCat.hom_comp]
    change (I.ideal U).map ((X.presheaf.map (homOfLE hVU).op ≫
      X.presheaf.germ V p hpV).hom) = _
    rw [X.presheaf.germ_res]
    rw [hd, Ideal.map_span, Set.image_singleton, hc]
  letI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian Vb
  obtain ⟨W, hWV, hpW, he⟩ := s2e_affine_ideals_equal_near_point X Vb p hpV
    (I.ideal Vb) (Ideal.span {c}) (Ideal.fg_of_isNoetherianRing _) (Submodule.fg_span_singleton c) hv
  let r := X.presheaf.map (homOfLE (X := X.Opens) hWV).op
  refine ⟨W, hWV.trans hVU, hpW, r c, ?_, ?_⟩
  · have h := (I.map_ideal hWV).symm.trans he
    rw [Ideal.map_span, Set.image_singleton] at h
    exact h
  · change (r ≫ X.presheaf.germ W.1 p hpW).hom c = d
    rw [X.presheaf.germ_res]
    exact hc

#print axioms s2e_affine_generator_of_stalk_generator
end HodgeLean.Foundations.Program
