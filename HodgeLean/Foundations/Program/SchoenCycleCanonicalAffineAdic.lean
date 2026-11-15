import HodgeLean.Foundations.Program.SchoenCycleCanonicalLocalizationAdic
import HodgeLean.Foundations.Program.SchoenCycleAffineStalkJets

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The canonical adic algebra equivalence induced by the actual affine germ map at a retained point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
def s2e_canonical_affine_point_adic_equiv
    (X : Scheme) (U : X.Opens) (hU : IsAffineOpen U)
    (p : X) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X)) :
    let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
    letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
    AdicCompletion P Γ(X, U) ≃ₐ[Γ(X, U)]
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) := by
  dsimp only
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨p, hp⟩).asIdeal
  letI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hp⟩ hclosed
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk p) P := hU.isLocalization_stalk ⟨p, hp⟩
  exact s2e_canonical_localization_adic_equiv P (X.presheaf.stalk p)

end HodgeLean.Foundations.Program
