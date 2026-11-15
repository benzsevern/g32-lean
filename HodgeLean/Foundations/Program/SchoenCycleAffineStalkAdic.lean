import HodgeLean.Foundations.Program.SchoenCycleLocalizationAdic
import HodgeLean.Foundations.Program.SchoenCycleAffineStalkJets

/-! # Affine chart and actual stalk adic rings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- At a closed point of an affine chart, the actual germ map induces an
adic equivalence preserving the germs of all chart sections.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 3 and 10. -/
theorem s2e_affine_stalk_adic_equiv
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (p : X) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X)) :
    let P := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
    ∃ E : AdicCompletion P Γ(X, U) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
      ∀ s, E (AdicCompletion.of P Γ(X, U) s) =
        AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) _
          ((X.presheaf.germ U p hp).hom s) := by
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hp⟩ hclosed
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk p) P := hU.isLocalization_stalk ⟨p, hp⟩
  have hmap : P.map (algebraMap Γ(X, U) (X.presheaf.stalk p)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk p)
  have H := s2e_localization_adic_equiv Γ(X, U) (X.presheaf.stalk p) P
  rw [hmap] at H
  exact H

#print axioms s2e_affine_stalk_adic_equiv
/-- The actual affine germ map extends the point ideal to the stalk maximal ideal.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, IsLocalization.AtPrime.map_eq_maximalIdeal. -/
theorem s2e_affine_germ_map_point_ideal
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (p : X) (hp : p ∈ U) :
    (hU.primeIdealOf ⟨p, hp⟩).asIdeal.map (X.presheaf.germ U p hp).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) := by
  let P := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk p) P := hU.isLocalization_stalk ⟨p, hp⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk p)

#print axioms s2e_affine_germ_map_point_ideal
/-- At a closed point, the canonical adic map induced by the affine germ is bijective.
Source: Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapters 3 and 10. -/
theorem s2e_affine_germ_adic_map_bijective
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (p : X) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X)) :
    Function.Bijective (s2e_adic_ring_map (hU.primeIdealOf ⟨p, hp⟩).asIdeal
      (IsLocalRing.maximalIdeal (X.presheaf.stalk p))
      (X.presheaf.germ U p hp).hom (s2e_affine_germ_map_point_ideal X U hU p hp).le) := by
  let P := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hp⟩ hclosed
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk p) P := hU.isLocalization_stalk ⟨p, hp⟩
  have H : ∀ (J : Ideal (X.presheaf.stalk p))
      (he : P.map (algebraMap Γ(X, U) (X.presheaf.stalk p)) = J),
      Function.Bijective (s2e_adic_ring_map P J
        (algebraMap Γ(X, U) (X.presheaf.stalk p)) he.le) := by
    intro J he
    subst J
    exact s2e_localization_adic_map_bijective Γ(X, U) (X.presheaf.stalk p) P
  exact H _ (s2e_affine_germ_map_point_ideal X U hU p hp)

#print axioms s2e_affine_germ_adic_map_bijective
end HodgeLean.Foundations.Program
