import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeLean.Foundations.Program.G32Native.PairedResidualNodeMap

/-! # The residual node equation in an actual regular-pair quotient chart -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native.FibreC

/-- In the quotient chart the two original branch equations have the specified ratio. -/
theorem residual_chart_relation {R : Type*} [CommRing R] (u v : R) :
    coeff u v u = ratio u v * coeff u v v := by
  let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
  change q (C u) = q X * q (C v)
  apply sub_eq_zero.mp
  rw [← map_mul, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The affine-plane quotient chart has independent denominator and shifted-ratio coordinates. -/
theorem residual_plane_chart_node_equiv (K : Type*) [CommRing K] :
    ∃ e : ring (C (X : Polynomial K)) (X : Polynomial (Polynomial K)) ≃+*
        Polynomial (Polynomial K),
      (∀ a : K, e (coeff (C (X : Polynomial K)) X (C (C a))) = C (C a)) ∧
      e (coeff (C (X : Polynomial K)) X X) = C X ∧
      e (ratio (C (X : Polynomial K)) X - 1) = X ∧
      e (coeff (C (X : Polynomial K)) X (C X - X)) = residualNodeMap K X := by
  let u : Polynomial (Polynomial K) := C X
  let v : Polynomial (Polynomial K) := X
  let f : Polynomial (Polynomial K) →+* Polynomial (Polynomial K) :=
    eval₂RingHom (eval₂RingHom (C.comp C) ((X + 1) * C X)) (C X)
  have hf : f u = (X + 1) * f v := by simp [f, u, v]
  obtain ⟨φ, hφ, _⟩ := universal u v f (X + 1) hf
  have hφc (a : Polynomial (Polynomial K)) : φ (coeff u v a) = f a :=
    DFunLike.congr_fun hφ.1 a
  let g : Polynomial (Polynomial K) →+* ring u v :=
    eval₂RingHom (eval₂RingHom ((coeff u v).comp (C.comp C)) (coeff u v v))
      (ratio u v - 1)
  have hgf : g.comp f = coeff u v := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        simp [f, g]
      · simp [f, g, u, v, sub_add_cancel]
        exact (residual_chart_relation u v).symm
    · simp [f, g, v]
  have hφg : φ.comp g = RingHom.id (Polynomial (Polynomial K)) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        change φ (g (C (C a))) = C (C a)
        have hg : g (C (C a)) = coeff u v (C (C a)) := by simp [g]
        rw [hg, hφc]
        simp [f]
      · change φ (g (C X)) = C X
        have hg : g (C X) = coeff u v v := by simp [g]
        rw [hg, hφc]
        simp [f, v]
    · simp [g, hφ.2]
  have hgφ : g.comp φ = RingHom.id (ring u v) := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext'
    · change (g.comp φ).comp (coeff u v) = coeff u v
      rw [RingHom.comp_assoc, hφ.1, hgf]
    · change g (φ (ratio u v)) = ratio u v
      rw [hφ.2]
      simp [g]
  let e : ring u v ≃+* Polynomial (Polynomial K) :=
    { φ with
      invFun := g
      left_inv := fun a => DFunLike.congr_fun hgφ a
      right_inv := fun a => DFunLike.congr_fun hφg a }
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro a
    change φ (coeff u v (C (C a))) = C (C a)
    rw [hφc]
    simp [f]
  · change φ (coeff u v v) = C X
    rw [hφc]
    simp [f, v]
  · change φ (ratio u v - 1) = X
    simp [hφ.2]
  · change φ (coeff u v (u - v)) = residualNodeMap K X
    rw [hφc]
    simp [f, u, v, residualNodeMap]
    ring

#print axioms residual_plane_chart_node_equiv
#print axioms residual_chart_relation
end HodgeLean.Foundations.Program.G32Native.FibreC
