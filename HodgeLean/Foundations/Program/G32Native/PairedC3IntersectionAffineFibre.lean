import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedChartFibre

/-! # Marked fibres with the original intersection quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual intersection quotient, rather than a replacement quotient
by a chosen coordinate, gives the fibre square whenever its image ideal is
the marked parameter ideal. -/
theorem pairedC3_intersection_affine_fibre
    (R B : Type) [CommRing R] [CommRing B]
    (N J : Ideal B) (c : R →+* (B ⧸ J)) (z : B ⧸ J) (a : R)
    (hN : N.map (Ideal.Quotient.mk J) = Ideal.span {z - c a}) :
    let q := Ideal.Quotient.factor (show J ≤ N ⊔ J from le_sup_right)
    IsPullback (Spec.map (CommRingCat.ofHom (q.comp c)))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))
      (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom c z))) := by
  let q := Ideal.Quotient.factor (show J ≤ N ⊔ J from le_sup_right)
  have hq : RingHom.ker q = Ideal.span {z - c a} := by
    dsimp only [q, Ideal.Quotient.factor]
    rw [Ideal.ker_quotient_lift, Ideal.mk_ker, Ideal.map_sup,
      Ideal.map_quotient_self, sup_bot_eq, hN]
  have hz : q z = q (c a) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply RingHom.mem_ker.mp
    rw [hq]
    exact Ideal.subset_span rfl
  have hs : CommRingCat.ofHom (Polynomial.eval₂RingHom c z) ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Polynomial.evalRingHom a) ≫ CommRingCat.ofHom (q.comp c) := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simpa using hz
  have hk : (RingHom.ker (Polynomial.evalRingHom a)).map
      (Polynomial.eval₂RingHom c z) = RingHom.ker q := by
    rw [hq, Polynomial.ker_evalRingHom]
    simp only [Ideal.map_span, Set.image_singleton, Polynomial.eval₂_sub,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C]
  exact (residual_surjective_isPushout _ _ _ _ hs
    (Polynomial.eval_surjective a) (Ideal.Quotient.factor_surjective (show J ≤ N ⊔ J from le_sup_right)) hk).op.map Scheme.Spec

#print axioms pairedC3_intersection_affine_fibre
end HodgeLean.Foundations.Program.G32Native
