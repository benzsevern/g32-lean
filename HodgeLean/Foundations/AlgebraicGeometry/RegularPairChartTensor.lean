import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartDefs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace AlgebraicGeometry.RegularPairChart
open Polynomial

/-- The two base generators satisfy the chart equation in the quotient ring. -/
theorem chart_relation {R : Type*} [CommRing R] (u v : R) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    q (C u) = q X * q (C v) := by
  dsimp only
  apply sub_eq_zero.mp
  rw [← map_mul, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- A solution of the chart equation induces a unique map from the chart ring. -/
theorem chart_lift {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (s : A) (hs : f u = s * f v) :
    ∃! φ : ring u v →+* A,
      φ.comp (Ideal.Quotient.mk (Ideal.span {C u - X * C v})) = eval₂RingHom f s := by
  let J : Ideal R[X] := Ideal.span {C u - X * C v}
  have hJ : J ≤ RingHom.ker (eval₂RingHom f s) := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    change (C u - X * C v).eval₂ f s = 0
    rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, hs, sub_self]
  let φ : ring u v →+* A :=
    Ideal.Quotient.lift J (eval₂RingHom f s) (fun p hp => hJ hp)
  refine ⟨φ, rfl, ?_⟩
  intro ψ hψ
  apply Ideal.Quotient.ringHom_ext
  exact hψ
/-- Extension of coefficients in a binomial chart is its tensor base change,
with the actual coefficient map and the chart ratio retained. -/
theorem tensor_ring_equiv
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (u v : R) :
    ∃ e : (ring u v ⊗[R] A) ≃+*
        ring (algebraMap R A u) (algebraMap R A v),
      (∀ a, e (Algebra.TensorProduct.includeRight a) =
        Ideal.Quotient.mk _ (Polynomial.C a)) ∧
      e (Algebra.TensorProduct.includeLeftRingHom (R := R) (B := A) (Ideal.Quotient.mk _ Polynomial.X)) =
        Ideal.Quotient.mk _ Polynomial.X := by
  let Q := ring u v
  let Q' := ring (algebraMap R A u) (algebraMap R A v)
  let T := Q ⊗[R] A
  let q := Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})
  let q' := Ideal.Quotient.mk (Ideal.span
    {Polynomial.C (algebraMap R A u) - Polynomial.X * Polynomial.C (algebraMap R A v)})
  have hrel : algebraMap R Q' u = q' Polynomial.X * algebraMap R Q' v :=
    chart_relation _ _
  obtain ⟨g, hg, _⟩ := chart_lift u v (algebraMap R Q') (q' Polynomial.X) hrel
  have hgC (r : R) : g (q (Polynomial.C r)) = algebraMap R Q' r :=
    (RingHom.congr_fun hg (Polynomial.C r)).trans (Polynomial.eval₂_C _ _)
  have hgX : g (q Polynomial.X) = q' Polynomial.X :=
    (RingHom.congr_fun hg Polynomial.X).trans (Polynomial.eval₂_X _ _)
  let ga : Q →ₐ[R] Q' := { g with commutes' := hgC }
  let F : T →+* Q' := (Algebra.TensorProduct.lift ga
    (IsScalarTower.toAlgHom R A Q') (fun _ _ => Commute.all _ _)).toRingHom
  let l : Q →+* T := algebraMap Q T
  let r : A →+* T := Algebra.TensorProduct.includeRight.toRingHom
  have hFl (x : Q) : F (l x) = g x := by
    change Algebra.TensorProduct.lift ga (IsScalarTower.toAlgHom R A Q') _ (x ⊗ₜ[R] 1) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hFr (x : A) : F (r x) = q' (Polynomial.C x) := by
    change Algebra.TensorProduct.lift ga (IsScalarTower.toAlgHom R A Q') _ (1 ⊗ₜ[R] x) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have hlr (x : R) : l (q (Polynomial.C x)) = r (algebraMap R A x) :=
    RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R) (A := Q) (B := A)) x
  have hrel' : r (algebraMap R A u) = l (q Polynomial.X) * r (algebraMap R A v) := by
    rw [← hlr, ← hlr, ← map_mul, ← chart_relation u v]
  obtain ⟨G, hG, _⟩ := chart_lift (algebraMap R A u) (algebraMap R A v)
    r (l (q Polynomial.X)) hrel'
  have hGC (x : A) : G (q' (Polynomial.C x)) = r x :=
    (RingHom.congr_fun hG (Polynomial.C x)).trans (Polynomial.eval₂_C _ _)
  have hGX : G (q' Polynomial.X) = l (q Polynomial.X) :=
    (RingHom.congr_fun hG Polynomial.X).trans (Polynomial.eval₂_X _ _)
  have hFG : F.comp G = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro x
      change F (G (q' (Polynomial.C x))) = q' (Polynomial.C x)
      rw [hGC, hFr]
    · change F (G (q' Polynomial.X)) = q' Polynomial.X
      rw [hGX, hFl, hgX]
  have hGl (x : Q) : G (g x) = l x := by
    have H : G.comp g = l := by
      apply Ideal.Quotient.ringHom_ext
      apply Polynomial.ringHom_ext'
      · apply RingHom.ext
        intro x
        change G (g (q (Polynomial.C x))) = l (q (Polynomial.C x))
        rw [hgC]
        change G (q' (Polynomial.C (algebraMap R A x))) = _
        rw [hGC, hlr]
      · change G (g (q Polynomial.X)) = l (q Polynomial.X)
        rw [hgX, hGX]
    exact RingHom.congr_fun H x
  have hGF : G.comp F = RingHom.id _ := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro x
      change G (F (l x)) = l x
      rw [hFl, hGl]
    · apply RingHom.ext
      intro x
      change G (F (r x)) = r x
      rw [hFr, hGC]
  let e : T ≃+* Q' :=
    { F with
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGF x
      right_inv := fun x => RingHom.congr_fun hFG x }
  exact ⟨e, hFr, (hFl _).trans hgX⟩

end AlgebraicGeometry.RegularPairChart
