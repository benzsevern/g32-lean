import HodgeLean.Foundations.Program.SchoenCycleAdicStalkMap
import HodgeLean.Foundations.Program.SchoenCycleFixedAdicAction
import HodgeLean.Foundations.Program.SchoenCycleQuotientExtendedAdicInvariants
import HodgeLean.Foundations.Program.SchoenCycleAffineSingletonFiber

/-! # Actual quotient chart actions and adic stalk germs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual quotient chart action commutes with the canonical adic germ map.
Source: Hartshorne, Algebraic Geometry, II.2, compatibility of germs and pullback. -/
theorem s2e_quotient_adic_germ_equivariant
    (X Y : Over (Spec ↧ℂ)) (q : X ⟶ Y) (u : X ⟶ X) (hu : u ≫ q = q)
    (U : Y.left.Opens) (p : X.left) (hp : u.left p = p) (hmem : q.left p ∈ U)
    (I : Ideal Γ(Y.left, U))
    (hg : (I.map (q.left.app U).hom).map (X.left.presheaf.germ (q.left ⁻¹ᵁ U) p hmem).hom ≤
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk p)) :
    let R := Γ(Y.left, U)
    let A := Γ(X.left, q.left ⁻¹ᵁ U)
    letI : Algebra R A := (q.left.app U).hom.toAlgebra
    ∀ z : AdicCompletion (I.map (algebraMap R A)) A,
      s2e_fixed_point_adicPullback X.left u.left p hp
        (s2e_adic_ring_map _ _ (X.left.presheaf.germ (q.left ⁻¹ᵁ U) p hmem).hom hg z) =
      s2e_adic_ring_map _ _ (X.left.presheaf.germ (q.left ⁻¹ᵁ U) p hmem).hom hg
        (s2e_adic_ring_map _ _ (s2e_quotient_chartPullbackAlgHom X Y q u hu U).toRingHom
          (s2e_algHom_map_extended_ideal I (s2e_quotient_chartPullbackAlgHom X Y q u hu U)).le z) := by
  intro R A z
  letI : Algebra Γ(Y.left, U) Γ(X.left, q.left ⁻¹ᵁ U) := (q.left.app U).hom.toAlgebra
  exact s2e_fixed_point_adicPullback_germ_map X.left u.left p hp (q.left ⁻¹ᵁ U)
    (s2e_step1_action_preimage X Y q u hu U) hmem (I.map (q.left.app U).hom)
    (s2e_algHom_map_extended_ideal I (s2e_quotient_chartPullbackAlgHom X Y q u hu U)).le hg z

#print axioms s2e_quotient_adic_germ_equivariant
/-- At a fixed singleton fiber, the actual adic stalk invariants are precisely
the unique images of the downstairs affine adic ring.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_quotient_adic_stalk_invariants
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (p : X.left) (hfix : ∀ g, (a g).left p = p)
    (hclosed : IsClosed ({q.left p} : Set Y.left))
    (hfiber : q.left ⁻¹' {q.left p} = {p})
    (U : Y.left.Opens) (hU : IsAffineOpen U) (hmem : q.left p ∈ U) :
    let R := Γ(Y.left, U)
    let A := Γ(X.left, q.left ⁻¹ᵁ U)
    letI : Algebra R A := (q.left.app U).hom.toAlgebra
    let I := (hU.primeIdealOf ⟨q.left p, hmem⟩).asIdeal
    let M := IsLocalRing.maximalIdeal (X.left.presheaf.stalk p)
    ∃ hg : (I.map (algebraMap R A)).map
        (X.left.presheaf.germ (q.left ⁻¹ᵁ U) p hmem).hom ≤ M,
      ∀ z : AdicCompletion M (X.left.presheaf.stalk p),
        (∀ g, s2e_fixed_point_adicPullback X.left (a g).left p (hfix g) z = z) ↔
        ∃! y : AdicCompletion I R,
          s2e_adic_ring_map _ M (X.left.presheaf.germ (q.left ⁻¹ᵁ U) p hmem).hom hg
            (s2e_adic_ring_map I _ (algebraMap R A) le_rfl y) = z := by
  intro R A I M
  letI : Algebra R A := (q.left.app U).hom.toAlgebra
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  obtain ⟨hg, hb⟩ := s2e_affine_singleton_fiber_adic_map_bijective
    q.left p hclosed hfiber U hU hmem
  refine ⟨hg, ?_⟩
  let t := s2e_adic_ring_map _ M (X.left.presheaf.germ (q.left ⁻¹ᵁ U) p hmem).hom hg
  let b := s2e_adic_ring_map I (I.map (algebraMap R A)) (algebraMap R A) le_rfl
  let α := fun g => s2e_adic_ring_map _ _
    (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).toRingHom
    (s2e_algHom_map_extended_ideal I
      (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U)).le
  intro z
  obtain ⟨w, rfl⟩ := hb.surjective z
  have he (g : G) : s2e_fixed_point_adicPullback X.left (a g).left p (hfix g) (t w) =
      t (α g w) := s2e_quotient_adic_germ_equivariant
        X Y q (a g) (hinv g) U p (hfix g) hmem I hg w
  have ha (g : G) : s2e_fixed_point_adicPullback X.left (a g).left p (hfix g) (t w) = t w ↔
      α g w = w := by
    rw [he]
    exact hb.injective.eq_iff
  have hi (y : AdicCompletion I R) : t (b y) = t w ↔ b y = w := hb.injective.eq_iff
  change (∀ g, s2e_fixed_point_adicPullback X.left (a g).left p (hfix g) (t w) = t w) ↔
    ∃! y, t (b y) = t w
  simp only [ha, hi]
  exact s2e_quotient_affine_adic_ring_invariants X Y G a ha1 hamul q hinv hquot U hU I w

#print axioms s2e_quotient_adic_stalk_invariants
/-- The actual adic stalk pullback identifies the downstairs adic stalk with
the fixed elements upstairs at a fixed singleton fiber.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Hartshorne, Algebraic Geometry, II.2; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_quotient_adic_stalkMap_invariants
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (p : X.left) (hfix : ∀ g, (a g).left p = p)
    (hclosed : IsClosed ({q.left p} : Set Y.left))
    (hfiber : q.left ⁻¹' {q.left p} = {p})
    (U : Y.left.Opens) (hU : IsAffineOpen U) (hmem : q.left p ∈ U) :
    ∀ z : AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p))
        (X.left.presheaf.stalk p),
      (∀ g, s2e_fixed_point_adicPullback X.left (a g).left p (hfix g) z = z) ↔
      ∃! y : AdicCompletion (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk (q.left p)))
          (Y.left.presheaf.stalk (q.left p)), s2e_adic_stalkMap q.left p y = z := by
  let I := (hU.primeIdealOf ⟨q.left p, hmem⟩).asIdeal
  have hd := (s2e_affine_germ_map_point_ideal Y.left U hU (q.left p) hmem).le
  let d := s2e_adic_ring_map I _ (Y.left.presheaf.germ U (q.left p) hmem).hom hd
  have hb : Function.Bijective d :=
    s2e_affine_germ_adic_map_bijective Y.left U hU (q.left p) hmem hclosed
  let e := RingEquiv.ofBijective d hb
  obtain ⟨hg, hH⟩ := s2e_quotient_adic_stalk_invariants X Y G a ha1 hamul q hinv hquot
    p hfix hclosed hfiber U hU hmem
  intro z
  refine (hH z).trans ?_
  apply e.toEquiv.existsUnique_congr
  intro w
  change _ ↔ s2e_adic_stalkMap q.left p (d w) = z
  dsimp only [d]
  rw [s2e_adic_stalkMap_germ q.left p U hmem I hd hg w]
  rfl

#print axioms s2e_quotient_adic_stalkMap_invariants
end HodgeLean.Foundations.Program
