import HodgeLean.Foundations.Program.SchoenCycleCollisionAdicInvariants
import HodgeLean.Foundations.Program.SchoenCycleEquivariantAdicCoordinates
import HodgeLean.Foundations.Program.SchoenCyclePowerSeriesBranch

/-! # Marked parameter ideal contraction at an actual total collision -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped BigOperators
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- In the actual adic stalks at a total collision, every marked parameter
ideal contracts to a principal ideal with exact product pullback.
Source: Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_total_collision_adic_marked_ideal
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
    ∃ c : AdicCompletion (IsLocalRing.maximalIdeal S) S,
      s2e_adic_stalkMap γ.left x.underlying c =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R
          (∏ i, s2e_curvePowerParameter Z n x i) ∧
      ∀ i, (Ideal.span (Set.singleton (AdicCompletion.of (IsLocalRing.maximalIdeal R) R
        (s2e_curvePowerParameter Z n x i)))).comap
          (s2e_adic_stalkMap γ.left x.underlying) = Ideal.span {c} := by
  intro R S
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let F := s2e_adic_stalkMap γ.left x.underlying
  have hF : Function.Injective F :=
    s2e_total_collision_adic_stalkMap_injective Z B n γ hγ hquot x a hx
  obtain ⟨E, hE, hEq⟩ := s2e_smooth_curve_power_equivariant_powerSeries_coordinates Z n x
  let f := E.symm.toRingHom.comp F
  have hf : Function.Injective f := E.symm.injective.comp hF
  have hEf (s) : E (f s) = F s := E.apply_symm_apply (F s)
  have hact (σ : Equiv.Perm (Fin n)) z : E (MvPowerSeries.rename σ z) =
      s2e_fixed_point_adicPullback (g3_power Z n).left (s2_permute Z n σ.symm).left x.underlying
        (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.symm) x
          (s2e_total_collision_permutation_fixed Z n x a hx σ.symm)) (E z) := by
    simpa using hEq σ.symm (s2e_total_collision_permutation_fixed Z n x a hx σ.symm) z
  have hfix (σ : Equiv.Perm (Fin n)) s : MvPowerSeries.rename σ (f s) = f s := by
    apply E.injective
    rw [hact]
    have hs := (s2e_total_collision_adic_stalkMap_invariants Z B n γ hγ hquot x a hx (F s)).mpr
      ⟨s, rfl, fun y hy => hF hy⟩
    rw [hEf]
    exact hs σ.symm
  have hdesc z (hz : ∀ σ : Equiv.Perm (Fin n), MvPowerSeries.rename σ z = z) :
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
  have hprod (e : Equiv.Perm (Fin n)) :
      MvPowerSeries.rename e (∏ j : Fin n, (MvPowerSeries.X j : MvPowerSeries (Fin n) ℂ)) =
        ∏ j : Fin n, MvPowerSeries.X j := by
    simp only [map_prod, MvPowerSeries.rename_X]
    exact Equiv.prod_comp e _
  obtain ⟨c, hc⟩ := hdesc (∏ j : Fin n, MvPowerSeries.X j) hprod
  have hEX (i : Fin n) : E (MvPowerSeries.X i) =
      AdicCompletion.of (IsLocalRing.maximalIdeal R) R (s2e_curvePowerParameter Z n x i) := by
    simpa only [MvPolynomial.coe_X, aeval_X] using hE (X i)
  refine ⟨c, ?_, ?_⟩
  · rw [← hEf, hc, map_prod]
    simp only [hEX]
    change (∏ i, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (s2e_curvePowerParameter Z n x i)) =
      algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (∏ i, s2e_curvePowerParameter Z n x i)
    exact (map_prod _ _ _).symm
  · intro i
    have hideal := s2e_powerSeries_invariant_root_ideal f hf
      (fun s e => hfix e s) hdesc c hc i
    ext s
    have hs := Ideal.ext_iff.mp hideal s
    change F s ∈ Ideal.span {(AdicCompletion.of (IsLocalRing.maximalIdeal R) R
      (s2e_curvePowerParameter Z n x i))} ↔ s ∈ Ideal.span {c}
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton] at hs ⊢
    rw [← hs]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨E.symm q, E.injective ?_⟩
      rw [hEf, map_mul, hEX, RingEquiv.apply_symm_apply]
      exact hq
    · rintro ⟨q, hq⟩
      refine ⟨E q, ?_⟩
      rw [← hEf, hq, map_mul, hEX]

#print axioms s2e_total_collision_adic_marked_ideal
end HodgeLean.Foundations.Program
