import HodgeLean.Foundations.Program.SchoenCycleTotalCollisionFiber
import HodgeLean.Foundations.Program.SchoenCycleAffineSingletonFiber

/-! # Actual affine-to-stalk adic comparison at total collisions -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- At an actual total collision, the extended downstairs affine point ideal
and the upstairs stalk maximal ideal give equivalent adic rings via the germ map.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_total_collision_affine_stalk_adic_equiv
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
    let V := γ.left ⁻¹ᵁ U
    let I := ((hU.primeIdealOf ⟨γ.left x.underlying, hxU⟩).asIdeal).map (γ.left.app U).hom
    ∃ E : AdicCompletion I Γ(X, V) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x.underlying))
          (X.presheaf.stalk x.underlying),
      ∀ s, E (AdicCompletion.of I Γ(X, V) s) =
        AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x.underlying)) _
          ((X.presheaf.germ V x.underlying hxU).hom s) := by
  let X := g3_power Z n
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have hcx : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcb : IsClosed ({γ.left x.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using γ.left.isClosedMap {x.underlying} hcx
  exact s2e_affine_singleton_fiber_adic_equiv γ.left x.underlying hcb
    (s2e_total_collision_scheme_fiber Z B n γ hγ hquot x a hx) U hU hxU

#print axioms s2e_total_collision_affine_stalk_adic_equiv
/-- The actual germ at a total collision induces a bijective adic map for the
extended downstairs affine point ideal.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_total_collision_affine_stalk_adic_map_bijective
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
    let V := γ.left ⁻¹ᵁ U
    let I := ((hU.primeIdealOf ⟨γ.left x.underlying, hxU⟩).asIdeal).map (γ.left.app U).hom
    ∃ h : I.map (X.presheaf.germ V x.underlying hxU).hom ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x.underlying),
      Function.Bijective (s2e_adic_ring_map I
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x.underlying))
        (X.presheaf.germ V x.underlying hxU).hom h) := by
  let X := g3_power Z n
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have hcx : IsClosed ({x.underlying} : Set X.left) := by
    change IsClosed {x.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using x.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcb : IsClosed ({γ.left x.underlying} : Set B.left) := by
    simpa only [Set.image_singleton] using γ.left.isClosedMap {x.underlying} hcx
  exact s2e_affine_singleton_fiber_adic_map_bijective γ.left x.underlying hcb
    (s2e_total_collision_scheme_fiber Z B n γ hγ hquot x a hx) U hU hxU


#print axioms s2e_total_collision_affine_stalk_adic_map_bijective
end HodgeLean.Foundations.Program
