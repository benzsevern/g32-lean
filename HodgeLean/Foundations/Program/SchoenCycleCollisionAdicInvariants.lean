import HodgeLean.Foundations.Program.SchoenCycleCollisionAffineAdic
import HodgeLean.Foundations.Program.SchoenCycleQuotientAdicStalkAction

/-! # Actual adic stalk invariants at total collisions -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- At a total collision, permutation-invariant elements of the actual adic
stalk are precisely the unique images of the downstairs affine adic ring.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_total_collision_adic_stalk_invariants
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a)
    (U : B.left.Opens) (hU : IsAffineOpen U) (hxU : γ.left x.underlying ∈ U) :
    let X := (g3_power Z n).left
    let R := Γ(B.left, U)
    let A := Γ(X, γ.left ⁻¹ᵁ U)
    letI : Algebra R A := (γ.left.app U).hom.toAlgebra
    let I := (hU.primeIdealOf ⟨γ.left x.underlying, hxU⟩).asIdeal
    let M := IsLocalRing.maximalIdeal (X.presheaf.stalk x.underlying)
    ∃ hg : (I.map (algebraMap R A)).map
        (X.presheaf.germ (γ.left ⁻¹ᵁ U) x.underlying hxU).hom ≤ M,
      ∀ z : AdicCompletion M (X.presheaf.stalk x.underlying),
        (∀ σ, s2e_fixed_point_adicPullback X (s2_permute Z n σ).left x.underlying
          (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ) x
            (s2e_total_collision_permutation_fixed Z n x a hx σ)) z = z) ↔
        ∃! y : AdicCompletion I R,
          s2e_adic_ring_map _ M (X.presheaf.germ (γ.left ⁻¹ᵁ U) x.underlying hxU).hom hg
            (s2e_adic_ring_map I _ (algebraMap R A) le_rfl y) = z := by
  let X := g3_power Z n
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have hcx : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcb : IsClosed ({γ.left x.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using γ.left.isClosedMap {x.underlying} hcx
  exact s2e_quotient_adic_stalk_invariants (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n)
    γ hγ hquot x.underlying
    (fun σ => s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ) x
      (s2e_total_collision_permutation_fixed Z n x a hx σ)) hcb
    (s2e_total_collision_scheme_fiber Z B n γ hγ hquot x a hx) U hU hxU

#print axioms s2e_total_collision_adic_stalk_invariants
/-- At a total collision, the actual downstairs adic stalk maps bijectively
onto the permutation-invariant elements of the actual upstairs adic stalk.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_total_collision_adic_stalkMap_invariants
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a) :
    ∀ z : AdicCompletion
        (IsLocalRing.maximalIdeal ((g3_power Z n).left.presheaf.stalk x.underlying))
        ((g3_power Z n).left.presheaf.stalk x.underlying),
      (∀ σ, s2e_fixed_point_adicPullback (g3_power Z n).left (s2_permute Z n σ).left x.underlying
        (s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ) x
          (s2e_total_collision_permutation_fixed Z n x a hx σ)) z = z) ↔
      ∃! y : AdicCompletion
          (IsLocalRing.maximalIdeal (B.left.presheaf.stalk (γ.left x.underlying)))
          (B.left.presheaf.stalk (γ.left x.underlying)),
        s2e_adic_stalkMap γ.left x.underlying y = z := by
  let X := g3_power Z n
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have hcx : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcb : IsClosed ({γ.left x.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using γ.left.isClosedMap {x.underlying} hcx
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show γ.left x.underlying ∈ (⊤ : B.left.Opens) from trivial)
  exact s2e_quotient_adic_stalkMap_invariants (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n)
    γ hγ hquot x.underlying
    (fun σ => s2e_complex_point_fixed_underlying (g3_power Z n) (s2_permute Z n σ) x
      (s2e_total_collision_permutation_fixed Z n x a hx σ)) hcb
    (s2e_total_collision_scheme_fiber Z B n γ hγ hquot x a hx) U hU hxU


#print axioms s2e_total_collision_adic_stalkMap_invariants
/-- The actual downstairs adic stalk embeds in the upstairs adic stalk at a
total collision.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
the unique invariant lift of zero determines the kernel. -/
theorem s2e_total_collision_adic_stalkMap_injective
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsIntegral B.left] (n : ℕ)
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (a : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x = a) :
    Function.Injective (s2e_adic_stalkMap γ.left x.underlying) := by
  have h0 := (s2e_total_collision_adic_stalkMap_invariants Z B n γ hγ hquot x a hx 0).mp
    (fun σ => map_zero _)
  intro u v huv
  apply sub_eq_zero.mp
  apply h0.unique
  · rw [map_sub, huv, sub_self]
  · exact map_zero _

#print axioms s2e_total_collision_adic_stalkMap_injective
end HodgeLean.Foundations.Program
