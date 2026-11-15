import HodgeLean.Foundations.Program.SchoenCycleAdicRingMaps
import HodgeLean.Foundations.Program.SchoenCycleParameterPolynomialAction

/-! # The actual fixed-point action on adic stalk rings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Pullback at a fixed scheme point induces an endomorphism of its actual
maximal-ideal adic stalk ring.
Source: Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
def s2e_fixed_point_adicPullback (X : Scheme) (f : X ⟶ X)
    (p : X) (hp : f p = p) :
    AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) →+*
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) :=
  s2e_adic_ring_map _ _ (s2e_fixed_point_stalkPullback X f p hp) (by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change s2e_fixed_point_stalkPullback X f p hp r ∈ IsLocalRing.maximalIdeal _
    simpa only [pow_one] using s2e_fixed_point_stalkPullback_power X f p hp 1 r
      (by simpa only [pow_one] using hr))

#print axioms s2e_fixed_point_adicPullback

/-- Actual adic stalk pullback agrees with section pullback on section germs.
Source: Hartshorne, Algebraic Geometry, II.2, compatibility of germs and pullback. -/
theorem s2e_fixed_point_adicPullback_germ
    (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U) (s : Γ(X, U)) :
    s2e_fixed_point_adicPullback X f p hp
      (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) _
        ((X.presheaf.germ U p hmem).hom s)) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) _
        ((X.presheaf.germ U p hmem).hom ((f.appLE U U hU).hom s)) := by
  unfold s2e_fixed_point_adicPullback
  rw [s2e_adic_ring_map_of]
  congr 1
  exact congrArg (fun k : Γ(X, U) ⟶ X.presheaf.stalk p => k.hom s)
    ((Scheme.FixedPointStalk.germ_transport X).2 f p hp U hU hmem)

#print axioms s2e_fixed_point_adicPullback_germ

/-- The actual permutation action on the adic stalk renames every polynomial
expression in the chosen curve-power parameters.
Source: Hartshorne, Algebraic Geometry, II.2; Macdonald, Symmetric Functions
and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_fixed_permutation_adic_parameter_polynomial
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : ComplexPoint (g3_power X n))
    (hx : Point.map (s2_permute X n σ) x = x) (p : MvPolynomial (Fin n) ℂ) :
    let R := (g3_power X n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    s2e_fixed_point_adicPullback (g3_power X n).left (s2_permute X n σ).left x.underlying
      (s2e_complex_point_fixed_underlying (g3_power X n) (s2_permute X n σ) x hx)
      (AdicCompletion.of (IsLocalRing.maximalIdeal R) R
        (aeval (s2e_curvePowerParameter X n x) p)) =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R
        (aeval (s2e_curvePowerParameter X n x) (rename σ.symm p)) := by
  dsimp only
  unfold s2e_fixed_point_adicPullback
  rw [s2e_adic_ring_map_of]
  congr 1
  exact s2e_fixed_permutation_parameter_polynomial X n σ x hx p

#print axioms s2e_fixed_permutation_adic_parameter_polynomial
/-- Actual germ-induced adic maps intertwine section and fixed-point stalk
pullback on every adic element.
Source: Hartshorne, Algebraic Geometry, II.2, compatibility of germs and pullback. -/
theorem s2e_fixed_point_adicPullback_germ_map
    (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U)
    (I : Ideal Γ(X, U)) (hI : I.map (f.appLE U U hU).hom ≤ I)
    (hg : I.map (X.presheaf.germ U p hmem).hom ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (x : AdicCompletion I Γ(X, U)) :
    s2e_fixed_point_adicPullback X f p hp
      (s2e_adic_ring_map _ _ (X.presheaf.germ U p hmem).hom hg x) =
    s2e_adic_ring_map _ _ (X.presheaf.germ U p hmem).hom hg
      (s2e_adic_ring_map I I (f.appLE U U hU).hom hI x) := by
  unfold s2e_fixed_point_adicPullback
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2e_adic_ring_map_eval, s2e_adic_ring_map_eval,
    s2e_adic_ring_map_eval, s2e_adic_ring_map_eval]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  change Ideal.Quotient.mk _
    (s2e_fixed_point_stalkPullback X f p hp ((X.presheaf.germ U p hmem).hom r)) =
      Ideal.Quotient.mk _ ((X.presheaf.germ U p hmem).hom ((f.appLE U U hU).hom r))
  congr 1
  exact congrArg (fun k : Γ(X, U) ⟶ X.presheaf.stalk p => k.hom r)
    ((Scheme.FixedPointStalk.germ_transport X).2 f p hp U hU hmem)

#print axioms s2e_fixed_point_adicPullback_germ_map
end HodgeLean.Foundations.Program
