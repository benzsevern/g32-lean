import HodgeLean.Foundations.Program.SchoenCycleInvariantCoordinateTransport
import HodgeLean.Foundations.Program.SchoenCycleQuotientFormalPointValues
import HodgeLean.Foundations.Program.SchoenCycleMixedStalkInvariantValues
import HodgeLean.Foundations.Program.SchoenCycleQuotientFormalPoint
import HodgeLean.Foundations.Program.SchoenCycleQuotientTupleStabilizer
import HodgeLean.Foundations.Program.SchoenCycleMixedStalkInvariantCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Actual quotient formal coordinates retain exact elementary substitution under geometric stalk pullback.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_mixed_quotient_formal_values
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (U : B.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint (g3_power Z n)) (hxU : x.underlying ∈ γ.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set (g3_power Z n).left))
    (hcy : IsClosed ({γ.left x.underlying} : Set B.left))
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a) :
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ D : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[ℂ]
      AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ)
        (MvPolynomial (Σ a, Fin (m a)) ℂ),
      ∀ q : MvPolynomial (Σ a, Fin (m a)) ℂ,
        s2e_formal_stalk_pullback (g3_power Z n) B γ x.underlying
          (D.symm (AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
            (MvPolynomial (Σ a, Fin (m a)) ℂ) q)) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (aeval (s2e_curvePowerParameter Z n x)
              (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m q).val)) := by
  letI : Algebra ℂ (B.left.presheaf.stalk (γ.left x.underlying)) :=
    (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  letI := s2e_step1_sectionAction (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  let I0 := ((hU.preimage γ.left).primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
  let H0 := MulAction.stabilizer (Equiv.Perm (Fin n))
    (⟨I0, MulAction.mem_orbit_self I0⟩ : MulAction.orbit (Equiv.Perm (Fin n)) I0)
  have hh := s2e_quotient_formal_point_values (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n)
    γ hγ hquot U hU x hxU hcx hcy
  have hH := s2e_quotient_tuple_stabilizer_eq Z B n γ hγ U hU x hxU
  dsimp only at hh hH
  change H0 = s2e_powerPointStabilizer Z n x at hH
  obtain ⟨hfix, E0, hE0⟩ := hh
  let R := (g3_power Z n).left.presheaf.stalk x.underlying
  let Q := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let H := s2e_powerPointStabilizer Z n x
  let β (σ : H) : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback (g3_power Z n).left (s2_permute Z n σ.val).left x.underlying
        (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.val) x σ.property)
      commutes' := s2e_fixed_point_stalkPullback_scalars (g3_power Z n) (s2_permute Z n σ.val) x.underlying
        (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.val) x σ.property) }
  let α (σ : H) : Q →ₐ[ℂ] Q := s2e_adic_algebra_map _ _ (β σ)
    (fun N r hr => s2e_fixed_point_stalkPullback_power (g3_power Z n).left (s2_permute Z n σ.val).left
      x.underlying (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ.val) x σ.property) N r hr)
  let F : Subalgebra ℂ Q := ⨅ σ : H, AlgHom.equalizer (α σ) (AlgHom.id ℂ Q)
  let K : Subalgebra ℂ Q := ⨅ σ : H, AlgHom.equalizer (α σ⁻¹) (AlgHom.id ℂ Q)
  let β0 (g : H0) : R →ₐ[ℂ] R :=
    { toRingHom := s2e_fixed_point_stalkPullback (g3_power Z n).left
        (s2_permute Z n g.val⁻¹).left x.underlying (hfix g)
      commutes' := s2e_fixed_point_stalkPullback_scalars (g3_power Z n)
        (s2_permute Z n g.val⁻¹) x.underlying (hfix g) }
  let α0 (g : H0) : Q →ₐ[ℂ] Q := s2e_adic_algebra_map _ _ (β0 g)
    (s2e_fixed_point_stalkPullback_power (g3_power Z n).left
      (s2_permute Z n g.val⁻¹).left x.underlying (hfix g))
  let K0 : Subalgebra ℂ Q := ⨅ g : H0, AlgHom.equalizer (α0 g) (AlgHom.id ℂ Q)
  let S : H0 ≃* H := MulEquiv.subgroupCongr hH
  have hmap (g : H0) : α0 g = α (S g)⁻¹ := by rfl
  have hK0K : K0 = K := by
    ext q
    simp only [K0, K, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro h σ
      obtain ⟨g, rfl⟩ := S.surjective σ
      rw [← hmap]
      exact h g
    · intro h g
      rw [hmap]
      exact h (S g)
  have hKF : K = F := by
    ext q
    simp only [K, F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro h σ
      simpa only [inv_inv] using h σ⁻¹
    · intro h σ
      exact h σ⁻¹
  let E' : AdicCompletion (IsLocalRing.maximalIdeal (B.left.presheaf.stalk (γ.left x.underlying)))
      (B.left.presheaf.stalk (γ.left x.underlying)) ≃ₐ[ℂ] K :=
    E0.trans (Subalgebra.equivOfEq K0 K hK0K)
  let T := Subalgebra.equivOfEq K F hKF
  let C := s2e_mixed_formal_stalk_invariant_coordinates Z n b x m ι p hp hx
  let EF := E'.trans T
  have hEF (z : AdicCompletion (IsLocalRing.maximalIdeal (B.left.presheaf.stalk (γ.left x.underlying)))
      (B.left.presheaf.stalk (γ.left x.underlying))) :
      (EF z).val = s2e_formal_stalk_pullback (g3_power Z n) B γ x.underlying z := by
    dsimp only [Q, R, EF, E', T, AlgEquiv.trans_apply]
    exact hE0 z
  obtain ⟨D, hD⟩ := s2e_invariant_coordinate_transport_values F EF C
    (s2e_formal_stalk_pullback (g3_power Z n) B γ x.underlying) hEF
  refine ⟨D, ?_⟩
  intro q
  exact (hD _).trans (s2e_mixed_formal_stalk_invariant_values Z n b x m ι p hp hx q)

#print axioms s2e_mixed_quotient_formal_values

/-- Every actual mixed quotient point has formal coordinates retaining exact elementary pullback values, without affine or point-closure premises.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_quotient_formal_values_at_point
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n))
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a) :
    let S := B.left.presheaf.stalk (γ.left x.underlying)
    letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
    let R := (g3_power Z n).left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ D : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[ℂ]
      AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ)
        (MvPolynomial (Σ a, Fin (m a)) ℂ),
      ∀ q : MvPolynomial (Σ a, Fin (m a)) ℂ,
        s2e_formal_stalk_pullback (g3_power Z n) B γ x.underlying
          (D.symm (AdicCompletion.of (idealOfVars (Σ a, Fin (m a)) ℂ)
            (MvPolynomial (Σ a, Fin (m a)) ℂ) q)) =
          AdicCompletion.of (IsLocalRing.maximalIdeal R) R
            (aeval (s2e_curvePowerParameter Z n x)
              (rename ι (s2e_mixed_polynomial_invariant_coordinates ℂ b m q).val)) := by
  let X := g3_power Z n
  letI : IsClosedImmersion (x.left ≫ X.hom) := by
    rw [Over.w x]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left X.hom
  have hcx : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcy : IsClosed ({γ.left x.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using γ.left.isClosedMap {x.underlying} hcx
  obtain ⟨U, hU, hmem, _⟩ := exists_isAffineOpen_mem_and_subset
    (show γ.left x.underlying ∈ (⊤ : B.left.Opens) from trivial)
  exact s2e_mixed_quotient_formal_values Z B n γ hγ hquot U hU x hmem hcx hcy
    b m ι p hp hx

#print axioms s2e_mixed_quotient_formal_values_at_point
end HodgeLean.Foundations.Program
