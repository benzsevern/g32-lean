import HodgeLean.Foundations.Program.SchoenCycleQuotientAdicInvariants
import HodgeLean.Foundations.Program.SchoenCycleAdicScalarExtension

/-! # Invariants in the extended-ideal adic ring of the actual quotient chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual quotient chart invariant comparison holds in the adic ring for
the extended ideal, with the action transported through the scalar comparison.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_quotient_affine_extended_adic_fixed_points
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(Y.left, U)) :
    let R := Γ(Y.left, U)
    let A := Γ(X.left, q.left ⁻¹ᵁ U)
    letI : Algebra R A := (q.left.app U).hom.toAlgebra
    let e := s2e_adic_scalar_extension_equiv (S := A) I
    ∀ x : AdicCompletion (I.map (algebraMap R A)) A,
      (∀ g, e (AdicCompletion.map I
        (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).toLinearMap
          (e.symm x)) = x) ↔
      ∃! y : AdicCompletion I R, e (AdicCompletion.map I (Algebra.linearMap R A) y) = x := by
  let R := Γ(Y.left, U)
  let A := Γ(X.left, q.left ⁻¹ᵁ U)
  letI : Algebra R A := (q.left.app U).hom.toAlgebra
  let e := s2e_adic_scalar_extension_equiv (S := A) I
  change ∀ x, (∀ g, e (AdicCompletion.map I
    (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).toLinearMap
      (e.symm x)) = x) ↔ ∃! y, e (AdicCompletion.map I (Algebra.linearMap R A) y) = x
  intro x
  have heq (z : AdicCompletion I A) : e z = x ↔ z = e.symm x := by
    constructor
    · intro h
      apply e.injective
      simpa only [LinearEquiv.apply_symm_apply] using h
    · intro h
      rw [h, LinearEquiv.apply_symm_apply]
  have H := s2e_quotient_affine_adic_fixed_points X Y G a ha1 hamul q hinv hquot U hU I (e.symm x)
  simpa only [heq] using H

#print axioms s2e_quotient_affine_extended_adic_fixed_points
/-- The actual quotient affine invariant comparison uses the canonical adic
ring maps induced by chart pullbacks.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_quotient_affine_canonical_adic_fixed_points
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(Y.left, U)) :
    let R := Γ(Y.left, U)
    let A := Γ(X.left, q.left ⁻¹ᵁ U)
    letI : Algebra R A := (q.left.app U).hom.toAlgebra
    let e := s2e_adic_scalar_extension_equiv (S := A) I
    ∀ x : AdicCompletion (I.map (algebraMap R A)) A,
      (∀ g, s2e_adic_ring_map _ _
        (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).toRingHom
        (s2e_algHom_map_extended_ideal I
          (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U)).le x = x) ↔
      ∃! y : AdicCompletion I R, e (AdicCompletion.map I (Algebra.linearMap R A) y) = x := by
  intro R A e x
  have H := s2e_quotient_affine_extended_adic_fixed_points
    X Y G a ha1 hamul q hinv hquot U hU I x
  simpa only [s2e_adic_scalar_extension_conjugate] using H

#print axioms s2e_quotient_affine_canonical_adic_fixed_points
/-- The actual quotient affine invariant ring is the unique image of the
canonical adic algebra map, with canonical adic chart actions.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_quotient_affine_adic_ring_invariants
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(Y.left, U)) :
    let R := Γ(Y.left, U)
    let A := Γ(X.left, q.left ⁻¹ᵁ U)
    letI : Algebra R A := (q.left.app U).hom.toAlgebra
    ∀ x : AdicCompletion (I.map (algebraMap R A)) A,
      (∀ g, s2e_adic_ring_map _ _
        (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U).toRingHom
        (s2e_algHom_map_extended_ideal I
          (s2e_quotient_chartPullbackAlgHom X Y q (a g) (hinv g) U)).le x = x) ↔
      ∃! y : AdicCompletion I R, s2e_adic_ring_map I (I.map (algebraMap R A))
        (algebraMap R A) le_rfl y = x := by
  intro R A x
  have H := s2e_quotient_affine_canonical_adic_fixed_points
    X Y G a ha1 hamul q hinv hquot U hU I x
  simpa only [s2e_adic_scalar_extension_algebraMap] using H

#print axioms s2e_quotient_affine_adic_ring_invariants
end HodgeLean.Foundations.Program
