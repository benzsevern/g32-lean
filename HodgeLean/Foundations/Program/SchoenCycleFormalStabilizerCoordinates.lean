import HodgeLean.Foundations.Program.SchoenCycleCanonicalFormalCoordinates
import HodgeLean.Foundations.Program.SchoenCycleRenamedAdicPowers
import HodgeLean.Foundations.Program.SchoenCycleAdicAlgebraMapComp
import HodgeLean.Foundations.Program.SchoenCycleParameterPolynomialAction

/-! # Actual tuple stabilizers in multiplicative formal coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The canonical formal coordinates identify the actual tuple-stabilizer action with variable permutation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_curve_power_adic_equiv_stabilizer
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (x : ComplexPoint (g3_power X n)) (σ : Equiv.Perm (Fin n))
    (hx : Point.map (s2_permute X n σ) x = x) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    let hp := s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ) x hx
    let β : R →ₐ[ℂ] R :=
      { toRingHom := s2e_fixed_point_stalkPullback (g3_power X n).left (s2_permute X n σ).left x.underlying hp
        commutes' := s2e_fixed_point_stalkPullback_scalars (g3_power X n) (s2_permute X n σ) x.underlying hp }
    (s2e_adic_algebra_map (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal R) β
      (fun N r hr => s2e_fixed_point_stalkPullback_power (g3_power X n).left (s2_permute X n σ).left x.underlying hp N r hr)).comp
        (s2e_curve_power_adic_equiv X n x).toAlgHom =
    (s2e_curve_power_adic_equiv X n x).toAlgHom.comp
      (s2e_adic_algebra_map (idealOfVars (Fin n) ℂ) (idealOfVars (Fin n) ℂ) (rename σ.symm)
        (s2e_rename_preserves_origin_powers σ.symm)) := by
  dsimp only
  let R := (g3_power X n).left.presheaf.stalk x.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let hp := s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ) x hx
  let β : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback (g3_power X n).left (s2_permute X n σ).left x.underlying hp
      commutes' := s2e_fixed_point_stalkPullback_scalars (g3_power X n) (s2_permute X n σ) x.underlying hp }
  let hβ : ∀ N : ℕ, ∀ r ∈ IsLocalRing.maximalIdeal R ^ N, β r ∈ IsLocalRing.maximalIdeal R ^ N :=
    fun N r hr => s2e_fixed_point_stalkPullback_power (g3_power X n).left (s2_permute X n σ).left x.underlying hp N r hr
  change (s2e_adic_algebra_map _ _ β hβ).comp
      (s2e_adic_algebra_map _ _ (aeval (s2e_curvePowerParameter X n x))
        (s2e_curve_power_aeval_preserves_powers X n x)) =
    (s2e_adic_algebra_map _ _ (aeval (s2e_curvePowerParameter X n x))
      (s2e_curve_power_aeval_preserves_powers X n x)).comp
      (s2e_adic_algebra_map _ _ (rename σ.symm) (s2e_rename_preserves_origin_powers σ.symm))
  rw [s2e_adic_algebra_map_comp, s2e_adic_algebra_map_comp]
  congr 1
  apply AlgHom.ext
  intro p
  exact s2e_fixed_permutation_parameter_polynomial X n σ x hx p

#print axioms s2e_curve_power_adic_equiv_stabilizer
end HodgeLean.Foundations.Program
