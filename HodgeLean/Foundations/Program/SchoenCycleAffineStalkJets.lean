import HodgeLean.Foundations.Program.SchoenCycleLocalizationJets
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Finite stalk jets represented on actual affine scheme charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every finite jet in the stalk at a closed point is represented by a section
on any specified affine neighbourhood of that point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, affine sections and stalks;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3. -/
theorem s2e_affine_stalk_power_jet_representative
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (p : X) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X)) (N : ℕ)
    (r : X.presheaf.stalk p) :
    ∃ s : Γ(X, U), r - (X.presheaf.germ U p hp).hom s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N := by
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hp⟩ hclosed
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk p) P := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨s, hs⟩ := s2e_localization_power_jet_representative Γ(X, U) (X.presheaf.stalk p) P N r
  have hmap : P.map (algebraMap Γ(X, U) (X.presheaf.stalk p)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk p)
  rw [Ideal.map_pow, hmap] at hs
  exact ⟨s, hs⟩

/-- The germ map on an actual affine chart reflects finite jet vanishing at a
closed point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, affine sections and stalks;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3. -/
theorem s2e_affine_stalk_power_jet_mem_iff
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (p : X) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X)) (N : ℕ)
    (s : Γ(X, U)) :
    (X.presheaf.germ U p hp).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N ↔
      s ∈ (hU.primeIdealOf ⟨p, hp⟩).asIdeal ^ N := by
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hp⟩ hclosed
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk p) P := hU.isLocalization_stalk ⟨p, hp⟩
  have hmap : P.map (algebraMap Γ(X, U) (X.presheaf.stalk p)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk p)
  have h := s2e_localization_power_jet_mem_iff Γ(X, U) (X.presheaf.stalk p) P N s
  rw [Ideal.map_pow, hmap] at h
  exact h

end HodgeLean.Foundations.Program
