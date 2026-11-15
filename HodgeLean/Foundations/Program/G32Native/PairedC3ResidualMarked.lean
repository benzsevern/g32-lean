import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualProduct
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupResidueIndex
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # The coordinate condition on the marked C3 intersection -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The C3 residual intersection retains the exceptional hyperplane, including
its inclusion into the original projective slice.
Source: Hartshorne, Algebraic Geometry, II.3; Schoen, Compositio Mathematica
65 (1988), Sublemma 2.7. -/
theorem pairedC3_marked_intersection
    {base : Scheme} {P V : Over base} (i : P ⟶ V) [IsClosedImmersion i.left]
    {X Q : Scheme} (σ : V.left ⟶ X) (i₀ : Q ⟶ X)
    (a : P.left ⟶ Q) (ha : i.left ≫ σ = a ≫ i₀)
    (K : X.IdealSheafData) (H : P.left.IdealSheafData)
    (hH : (K.comap σ).comap i.left = H) :
    ∃ e : (residualIntersection i (K.comap σ ⊔ i₀.ker.comap σ)).left ≅ H.subscheme,
      e.hom ≫ H.subschemeι =
        (residualIntersectionFirst i (K.comap σ ⊔ i₀.ker.comap σ)).left := by
  apply (residual_intersection_subscheme_iff _ _ _).mpr
  exact (pairedC3_residual_restriction i σ i₀ a ha K).trans hH

/-- The numerical caller's literal zeroth-coordinate marked inclusion requires
that the retained residue index is zero. Abstract isomorphism of hyperplanes
alone does not give the required equation over the slice.
Source: Hartshorne, Algebraic Geometry, II.2, projective coordinates. -/
theorem pairedC3_fixed_marked_intersection_iff
    (k : ℕ) {V : Over (Spec ↧ℂ)}
    (i : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ V)
    [IsClosedImmersion i.left]
    {X Q : Scheme} (σ : V.left ⟶ X) (i₀ : Q ⟶ X)
    (a : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)) ⟶ Q)
    (ha : i.left ≫ σ = a ≫ i₀) (K : X.IdealSheafData)
    (j : Fin (k + 1))
    (hH : (K.comap σ).comap i.left = s2e_s2b_residueIdeal k j) :
    (∃ e : (residualIntersection i (K.comap σ ⊔ i₀.ker.comap σ)).left ≅
        (s2e_hyperplaneIdeal k).subscheme,
      e.hom ≫ (s2e_hyperplaneIdeal k).subschemeι =
        (residualIntersectionFirst i (K.comap σ ⊔ i₀.ker.comap σ)).left) ↔ j = 0 := by
  rw [residual_intersection_subscheme_iff,
    pairedC3_residual_restriction i σ i₀ a ha K, hH]
  change s2e_s2b_residueIdeal k j = s2e_s2b_residueIdeal k 0 ↔ j = 0
  exact (paired_coordinate_residue_injective k).eq_iff

#print axioms pairedC3_marked_intersection
#print axioms pairedC3_fixed_marked_intersection_iff
end HodgeLean.Foundations.Program.G32Native
