import HodgeLean.Foundations.Program.SchoenCycleQuotientFormalPoint
import HodgeLean.Foundations.Program.SchoenCycleQuotientTupleStabilizer
import HodgeLean.Foundations.Program.SchoenCycleMixedStalkInvariantCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Mixed elementary coefficient formal coordinates identify the retained quotient point's actual formal local algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_mixed_quotient_formal_coordinates
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
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[ℂ]
      AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ)
        (MvPolynomial (Σ a, Fin (m a)) ℂ)) := by
  letI : Algebra ℂ (B.left.presheaf.stalk (γ.left x.underlying)) :=
    (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  have hh := s2e_quotient_formal_point_invariants (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n)
    γ hγ hquot U hU x hxU hcx hcy
  have hH := s2e_quotient_tuple_stabilizer_eq Z B n γ hγ U hU x hxU
  dsimp only at hh hH
  rw [hH] at hh
  obtain ⟨hfix, ⟨E⟩⟩ := hh
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
  have hKF : K = F := by
    ext q
    simp only [K, F, Algebra.mem_iInf, AlgHom.mem_equalizer, AlgHom.id_apply]
    constructor
    · intro h σ
      simpa only [inv_inv] using h σ⁻¹
    · intro h σ
      exact h σ⁻¹
  have E' : AdicCompletion (IsLocalRing.maximalIdeal (B.left.presheaf.stalk (γ.left x.underlying)))
      (B.left.presheaf.stalk (γ.left x.underlying)) ≃ₐ[ℂ] K := E
  exact ⟨E'.trans ((Subalgebra.equivOfEq K F hKF).trans
    (s2e_mixed_formal_stalk_invariant_coordinates Z n b x m ι p hp hx).symm)⟩

#print axioms s2e_mixed_quotient_formal_coordinates

/-- Mixed elementary formal coordinates identify the retained quotient stalk at every actual tuple, including partial collisions.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_mixed_quotient_formal_coordinates_at_point
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
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal S) S ≃ₐ[ℂ]
      AdicCompletion (idealOfVars (Σ a, Fin (m a)) ℂ)
        (MvPolynomial (Σ a, Fin (m a)) ℂ)) := by
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
  exact s2e_mixed_quotient_formal_coordinates Z B n γ hγ hquot U hU x hmem hcx hcy
    b m ι p hp hx

#print axioms s2e_mixed_quotient_formal_coordinates_at_point
end HodgeLean.Foundations.Program
