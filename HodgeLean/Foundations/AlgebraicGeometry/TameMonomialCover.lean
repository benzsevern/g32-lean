import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialCoverProofs

/-! Tame monomial chart and inertia contracts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace AlgebraicGeometry.TameMonomialCover

/-- Pair rescaling preserves the other monomial exponents on both charts.
Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15; SchoenTowerI2aProofs.s2v_i2a_blowup_exponents_aux. -/
theorem pair_rescaling
    (K : Type*) [Field K] (n m a b : ℕ) (hm : 0 < m)
    (hab : a + b = m) (α : Fin n → ℕ)
    (ε t x y : K) (z : Fin n → K) (hx : x ≠ 0) (hy : y ≠ 0)
    (ht : t ^ m = ε * x ^ a * y ^ b * ∏ j, z j ^ α j) :
    (t / x) ^ m = ε * (y / x) ^ b * ∏ j, z j ^ α j ∧
    (t / y) ^ m = ε * (x / y) ^ a * ∏ j, z j ^ α j :=
  pair_rescaling_aux K n m a b hm hab α ε t x y z hx hy ht

/-- A vanishing coordinate supplies a subgroup fixing every integral-element evaluation.
Source: Schoen (1988), Lemma 2.5, printed p. 15, and Sublemma 2.9, printed p. 19; SchoenTowerI2aProofs.s2v_i2a_normalized_monomial_inertia_aux. -/
theorem integralClosure_inertia
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    (n m : ℕ) (hm : 0 < m)
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R K))
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε *
      ∏ j, (algebraMap R K (c (MvPolynomial.X j))) ^ α j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (ζ : k) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[R] K) (hd : d v = algebraMap k K ζ * v)
    (p : integralClosure R K →ₐ[k] k) (j : Fin n)
    (hp : p (algebraMap R (integralClosure R K) (c (MvPolynomial.X j))) = 0) :
    Subgroup.zpowers (d.mapIntegralClosure ^ α j) ≤
      { carrier := {g : integralClosure R K ≃ₐ[R] integralClosure R K |
            ∀ b, p (g b) = p b}
        one_mem' := fun _ => rfl
        mul_mem' := fun hg hk b => (hg _).trans (hk b)
        inv_mem' := fun {g} hg b => by
          have H := hg (g⁻¹ b)
          simpa only [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] using H.symm } :=
  integralClosure_inertia_aux k n m hm R K c hc hinj α ε hε v hv hgen ζ hζ d hd p j hp

-- A positive paired exponent check, independent of the general contract.
example : ((6 : ℚ) / 2) ^ 2 = (3 : ℚ) ^ 2 ∧
    ((6 : ℚ) / 3) ^ 2 = (2 : ℚ) ^ 2 := by
  norm_num

-- On the tame double cover x = t², the sign involution fixes x and every
-- evaluation at the ramification point, but moves t.
example :
    let σ := Polynomial.algEquivAevalNegX (R := ℂ)
    σ (Polynomial.X ^ 2) = Polynomial.X ^ 2 ∧
      σ Polynomial.X ≠ Polynomial.X ∧
      ∀ p : Polynomial ℂ, (σ p).eval 0 = p.eval 0 := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · simp [Polynomial.algEquivAevalNegX_apply]
  · intro h
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
    norm_num [Polynomial.algEquivAevalNegX_apply] at hc
  · intro p
    change (p.comp (-Polynomial.X)).eval 0 = p.eval 0
    simp [Polynomial.eval_comp]

end AlgebraicGeometry.TameMonomialCover
