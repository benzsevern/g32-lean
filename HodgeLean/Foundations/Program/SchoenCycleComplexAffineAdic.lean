import HodgeLean.Foundations.Program.SchoenCycleComplexAffineGerm
import HodgeLean.Foundations.Program.SchoenCycleCanonicalAffineAdic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The canonical formal affine germ comparison is an equivalence for the prescribed complex scalar structures.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
def s2e_complex_affine_point_adic_equiv
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (p : X.left) (hp : p ∈ U) (hclosed : IsClosed ({p} : Set X.left)) :
    letI := s2e_step1_sectionAlgebra X U
    letI : Algebra ℂ (X.left.presheaf.stalk p) :=
      (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    AdicCompletion (hU.primeIdealOf ⟨p, hp⟩).asIdeal Γ(X.left, U) ≃ₐ[ℂ]
      AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p))
        (X.left.presheaf.stalk p) := by
  letI := s2e_step1_sectionAlgebra X U
  letI : Algebra ℂ (X.left.presheaf.stalk p) :=
    (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  have hf : ∀ n a, a ∈ (hU.primeIdealOf ⟨p, hp⟩).asIdeal ^ n →
      s2e_complex_section_germ X U p hp a ∈
        IsLocalRing.maximalIdeal (X.left.presheaf.stalk p) ^ n := by
    intro n a ha
    exact (s2e_affine_stalk_power_jet_mem_iff X.left U hU p hp hclosed n a).mpr ha
  apply AlgEquiv.ofBijective (s2e_adic_algebra_map _ _ (s2e_complex_section_germ X U p hp) hf)
  letI : Algebra Γ(X.left, U) (X.left.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨p, hp⟩
  exact (s2e_canonical_affine_point_adic_equiv X.left U hU p hp hclosed).bijective

#print axioms s2e_complex_affine_point_adic_equiv
end HodgeLean.Foundations.Program
