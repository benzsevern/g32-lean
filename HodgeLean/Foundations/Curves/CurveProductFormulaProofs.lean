import HodgeLean.Foundations.Curves.CurveDivisors
import HodgeLean.Foundations.Curves.CurveDegree
import HodgeLean.Foundations.Curves.CurveZeroCount

/-! # Proof of the product formula on curves (lane J1b)

`CurveDegree.lean` reduces the degree of a principal divisor to the plain sum of orders
(`divisorDegree_principalDivisor_eq_finsum`). A constant has no zeros or poles. A nonconstant `f`
is transcendental over `ℂ`, the function field `K` is finite over `ℂ⟮f⟯ = ℂ⟮f⁻¹⟯`, and by
`finsum_toNat_ord_eq_finrank` both the zeros of `f` and the zeros of `f⁻¹` (the poles of `f`),
counted with multiplicity, number `[K : ℂ⟮f⟯]`. So the sum of orders is `n - n = 0`.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace IntermediateField

namespace HodgeLean.Foundations.Curves

attribute [local instance] overSpecAlgebra functionFieldAlgebra

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
  [IsLocallyNoetherian X.left] [CompactSpace X.left]

/-- Product formula: every principal divisor on a smooth projective curve has degree zero. -/
theorem degree_principalDivisor_aux (f : X.left.functionField) (hf : f ≠ 0) :
    divisorDegree X (principalDivisor X.left f) = 0 := by
  rw [divisorDegree_principalDivisor_eq_finsum f (ord_support_finite f hf)]
  by_cases halg : IsAlgebraic ℂ f
  · obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic halg
    have hc : c ≠ 0 := by
      rintro rfl
      exact hf (map_zero _)
    have h0 : ∀ P, X.left.ord (algebraMap ℂ X.left.functionField c) P = 0 := fun P ↦
      Scheme.ord_of_isUnit ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℂ Γ(X.left, ⊤)))
        (show P ∈ (⊤ : X.left.Opens) from trivial)
    simp [h0]
  · have ht : Transcendental ℂ f := halg
    have hti : Transcendental ℂ f⁻¹ := fun h ↦ ht (IsAlgebraic.inv_iff.mp h)
    have := finiteDimensional_functionField f ht
    have := finiteDimensional_functionField f⁻¹ hti
    have h1 := finsum_toNat_ord_eq_finrank f ht
    have h2 := finsum_toNat_ord_eq_finrank f⁻¹ hti
    have hF : ℂ⟮f⁻¹⟯ = ℂ⟮f⟯ := le_antisymm
      (adjoin_simple_le_iff.mpr (inv_mem (mem_adjoin_simple_self ℂ f)))
      (adjoin_simple_le_iff.mpr (by simpa using inv_mem (mem_adjoin_simple_self ℂ f⁻¹)))
    rw [hF] at h2
    have hfin : (Function.support (X.left.ord f)).Finite := ord_support_finite f hf
    have hfin1 : (Function.support fun P ↦ (X.left.ord f P).toNat).Finite :=
      hfin.subset fun P hP h ↦ hP (by simp [h])
    have hfin2 : (Function.support fun P ↦ (X.left.ord f⁻¹ P).toNat).Finite :=
      hfin.subset fun P hP h ↦ hP (by simp [ord_inv hf, h])
    have hcast := fun (g : X.left → ℕ) (hg : (Function.support g).Finite) ↦
      (Nat.castAddMonoidHom ℤ).map_finsum hg
    calc ∑ᶠ P, X.left.ord f P
        = ∑ᶠ P, (((X.left.ord f P).toNat : ℤ) - ((X.left.ord f⁻¹ P).toNat : ℤ)) :=
          finsum_congr fun P ↦ by rw [ord_inv hf]; omega
      _ = ∑ᶠ P, ((X.left.ord f P).toNat : ℤ) - ∑ᶠ P, ((X.left.ord f⁻¹ P).toNat : ℤ) :=
          finsum_sub_distrib (hfin1.subset fun P hP h ↦ hP (by simp [h]))
            (hfin2.subset fun P hP h ↦ hP (by simp [h]))
      _ = 0 := by
          have e1 := hcast _ hfin1
          have e2 := hcast _ hfin2
          simp only [Nat.coe_castAddMonoidHom] at e1 e2
          rw [← e1, ← e2, h1, h2, sub_self]

end HodgeLean.Foundations.Curves
