import HodgeLean.Foundations.Program.SchoenCycleCollisionAdicCoefficients
import HodgeLean.Foundations.Program.SchoenCycleEquivariantAdicCoordinates
import HodgeLean.Foundations.Program.SchoenCycleInvariantAdicGeneration
import HodgeLean.Foundations.Program.SchoenCycleAdicLocalMap

/-! # Elementary generators in the actual quotient adic stalk -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The exact elementary lifts generate the extended maximal ideal in the
actual downstairs adic stalk at a total collision.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_total_collision_adic_elementary_generators
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a) 

    : let R := (g3_power Z n).left.presheaf.stalk x.underlying
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ c : Fin n → AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (IsLocalRing.maximalIdeal S).map (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) =
        Ideal.span (Set.range c) ∧
      ∀ j, s2e_adic_stalkMap γ.left x.underlying (c j) =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R
          (aeval (s2e_curvePowerParameter Z n x) (esymm (Fin n) ℂ (j.val + 1))) := by
  intro R S
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI : IsLocallyNoetherian (g3_power Z n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (g3_power Z n).hom
  letI := s2e_quotient_isLocallyNoetherian (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ hquot
  letI : IsNoetherianRing R := inferInstanceAs
    (IsNoetherianRing ((g3_power Z n).left.presheaf.stalk x.underlying))
  letI : IsNoetherianRing S := inferInstanceAs
    (IsNoetherianRing (B.left.presheaf.stalk (γ.left x.underlying)))
  let F := s2e_adic_stalkMap γ.left x.underlying
  letI : IsLocalHom F := s2e_adic_ring_map_isLocalHom (γ.left.stalkMap x.underlying).hom
  have hF : Function.Injective F :=
    s2e_total_collision_adic_stalkMap_injective Z B n γ hγ hquot x a hx
  obtain ⟨E, hE, hEq⟩ := s2e_smooth_curve_power_equivariant_adic_coordinates Z n x
  letI : IsLocalHom E.symm.toRingHom := by
    constructor
    intro r hr
    change IsUnit (E.symm r) at hr
    simpa only [RingEquiv.apply_symm_apply] using hr.map E
  let f := E.symm.toRingHom.comp F
  letI : IsLocalHom f := inferInstanceAs (IsLocalHom (E.symm.toRingHom.comp F))
  have hf : Function.Injective f := E.symm.injective.comp hF
  have hEf (s) : E (f s) = F s := E.apply_symm_apply (F s)
  have hact (σ : Equiv.Perm (Fin n)) z : E (s2e_polynomial_adic_rename σ z) =
      s2e_fixed_point_adicPullback (g3_power Z n).left (s2_permute Z n σ.symm).left x.underlying
        (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.symm) x
          (s2e_total_collision_permutation_fixed Z n x a hx σ.symm)) (E z) := by
    simpa using hEq σ.symm (s2e_total_collision_permutation_fixed Z n x a hx σ.symm) z
  have hfix (σ : Equiv.Perm (Fin n)) s : s2e_polynomial_adic_rename σ (f s) = f s := by
    apply E.injective
    rw [hact]
    have hs := (s2e_total_collision_adic_stalkMap_invariants Z B n γ hγ hquot x a hx (F s)).mpr
      ⟨s, rfl, fun y hy => hF hy⟩
    rw [hEf]
    exact hs σ.symm
  have hdesc z (hz : ∀ σ : Equiv.Perm (Fin n), s2e_polynomial_adic_rename σ z = z) :
      ∃ s, f s = z := by
    have hi : ∀ σ, s2e_fixed_point_adicPullback (g3_power Z n).left (s2_permute Z n σ).left x.underlying
        (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ) x
          (s2e_total_collision_permutation_fixed Z n x a hx σ)) (E z) = E z := by
      intro σ
      simpa only [Equiv.symm_symm, hz] using (hact σ.symm z).symm
    obtain ⟨s, hs, _⟩ := (s2e_total_collision_adic_stalkMap_invariants Z B n γ hγ hquot x a hx (E z)).mp hi
    refine ⟨s, ?_⟩
    change E.symm (F s) = z
    rw [hs, RingEquiv.symm_apply_apply]
  obtain ⟨c, hc, _⟩ := s2e_total_collision_adic_elementary_coefficients Z B n γ hγ hquot x a hx
  refine ⟨c, ?_, hc⟩
  rw [← AdicCompletion.maximalIdeal_eq_map]
  apply s2e_invariant_adic_maximalIdeal_generators n f hf hfix hdesc c
  intro j
  apply E.injective
  rw [hEf]
  change F (c j) = E (AdicCompletion.of (idealOfVars (Fin n) ℂ) _ (esymm (Fin n) ℂ (j.val + 1)))
  rw [hc, hE]

#print axioms s2e_total_collision_adic_elementary_generators
end HodgeLean.Foundations.Program
