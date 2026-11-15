import HodgeLean.Foundations.Program.SchoenTowerT11bCylindricalEncoding

/-! Cylindrical coordinates for actual Boolean polynomial realizations on regular bases.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open UniqueFactorizationMonoid
attribute [local instance] s2v_t11b_mvParameterNormalization

/-- Every normalized height retains the actual Boolean formula membership over a connected regular parameter region.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, cylindrical formula-compatibility step. -/
theorem s2v_t11b_cylindrical_formula_normalized_membership {n : ℕ}
    (f : s2v_t11b_Formula (n + 1)) (P : Polynomial (MvPolynomial (Fin n) ℝ)) (hP : P ≠ 0)
    (hdiv : ∀ q ∈ f.atoms, q ≠ 0 → MvPolynomial.finSuccEquiv ℝ n q ∣ P)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsPreconnected K) {m : ℕ}
    (ψ : Fin m → K → ℝ)
    (hroots : ∀ t : K, ∀ x, (radical P).eval₂ (MvPolynomial.eval (fun i => t.val i)) x = 0 ↔ ∃ i, x = ψ i t)
    (hsimple : ∀ t : K, ∀ x, (radical P).eval₂ (MvPolynomial.eval (fun i => t.val i)) x = 0 →
      ((radical P).map (MvPolynomial.eval (fun i => t.val i))).derivative.eval x ≠ 0)
    (E : (K × ℝ) ≃ₜ (K × ℝ)) (hbase : ∀ z, (E z).1 = z.1)
    (hEroots : ∀ t i, E (t, ψ i t) = (t, (i.val : ℝ) + 1)) (r : ℝ) (a b : K) :
    WithLp.toLp 2 (Fin.cons (E.symm (a, r)).2 (fun i => a.val i)) ∈ f.realize ↔
      WithLp.toLp 2 (Fin.cons (E.symm (b, r)).2 (fun i => b.val i)) ∈ f.realize := by
  haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  let φ : K → MvPolynomial (Fin n) ℝ →+* ℝ := fun t => MvPolynomial.eval (fun i => t.val i)
  have hφ : ∀ c, Continuous (fun t => φ t c) := fun c =>
    (s2v_t11b_mv_parameter_eval_contDiff c).continuous.comp continuous_subtype_val
  apply s2v_t11b_formula_membership_of_atom_signs
  intro q hq
  by_cases hqzero : q = 0
  · simp only [hqzero, map_zero]
  · have henc : MvPolynomial.finSuccEquiv ℝ n q ≠ 0 := by
      intro h
      apply hqzero
      apply (MvPolynomial.finSuccEquiv ℝ n).injective
      rw [h, map_zero]
    have hs := s2v_t11b_parameter_atom_sign_at_normalized_height φ hφ P
      (MvPolynomial.finSuccEquiv ℝ n q) hP henc (hdiv q hq hqzero)
      ψ hroots hsimple E hbase hEroots r a b
    change (0 ≤ (MvPolynomial.finSuccEquiv ℝ n q).eval₂ (MvPolynomial.eval (fun i => a.val i)) (E.symm (a, r)).2 ↔
      0 ≤ (MvPolynomial.finSuccEquiv ℝ n q).eval₂ (MvPolynomial.eval (fun i => b.val i)) (E.symm (b, r)).2) at hs
    simpa only [s2v_t11b_finSucc_family_eval] using hs

/-- An actual Boolean formula has an actual-fiber cylindrical chart on every connected regular base region of a carrier.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, regular cylindrical formula projection step. -/
theorem s2v_t11b_cylindrical_formula_regular_chart {n : ℕ}
    (f : s2v_t11b_Formula (n + 1)) (P : Polynomial (MvPolynomial (Fin n) ℝ)) (hP : P ≠ 0)
    (hdiv : ∀ q ∈ f.atoms, q ≠ 0 → MvPolynomial.finSuccEquiv ℝ n q ∣ P)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsPreconnected K) (a : K)
    (hlead : ∀ t ∈ K, MvPolynomial.eval (fun i => t i) (radical P).leadingCoeff ≠ 0)
    (hsimple : ∀ t ∈ K, ∀ x : ℝ, (radical P).eval₂ (MvPolynomial.eval (fun i => t i)) x = 0 →
      ((radical P).map (MvPolynomial.eval (fun i => t i))).derivative.eval x ≠ 0) :
    ∃ F : ({x : ℝ | WithLp.toLp 2 (Fin.cons x (fun i => a.val i)) ∈ f.realize} × K) ≃ₜ
        {z : K × ℝ | WithLp.toLp 2 (Fin.cons z.2 (fun i => z.1.val i)) ∈ f.realize},
      ∀ y, (F y).val.1 = y.2 := by
  obtain ⟨m, ψ, hc, hm, hr⟩ := s2v_t11b_mv_parameter_ordered_sections (radical P) K hK a hlead hsimple
  obtain ⟨E, hbase, hEroots, _⟩ := s2v_t11b_finite_sections_ambient_straightening ψ hc hm
  let S : Set (K × ℝ) := {z | WithLp.toLp 2 (Fin.cons z.2 (fun i => z.1.val i)) ∈ f.realize}
  have hconstant : ∀ b r, E.symm (b, r) ∈ S ↔ E.symm (a, r) ∈ S := by
    intro b r
    change WithLp.toLp 2 (Fin.cons (E.symm (b, r)).2 (fun i => (E.symm (b, r)).1.val i)) ∈ f.realize ↔
      WithLp.toLp 2 (Fin.cons (E.symm (a, r)).2 (fun i => (E.symm (a, r)).1.val i)) ∈ f.realize
    rw [s2v_t11b_ambient_inverse_base E hbase (b, r), s2v_t11b_ambient_inverse_base E hbase (a, r)]
    exact s2v_t11b_cylindrical_formula_normalized_membership f P hP hdiv K hK ψ hr
      (fun t x hx => hsimple t.val t.property x hx) E hbase hEroots r b a
  obtain ⟨D, e, he⟩ := s2v_t11b_normalized_membership_product E hbase S a hconstant
  let R := s2v_t11b_productSubsetFiberChart S a
  let A := s2v_t11b_actualFiberProduct (fun z : S => z.val.1) e he a
  refine ⟨(R.symm.prodCongr (Homeomorph.refl K)).trans A, ?_⟩
  intro y
  exact s2v_t11b_actualFiberProduct_projection (fun z : S => z.val.1) e he a (R.symm y.1, y.2)

end HodgeLean.Foundations.Program
