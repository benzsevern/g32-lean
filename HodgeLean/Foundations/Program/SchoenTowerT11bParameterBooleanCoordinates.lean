import HodgeLean.Foundations.Program.SchoenTowerT11bParameterAtomCoordinates

/-! Actual-fiber charts for Boolean selections of regular polynomial carriers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
open UniqueFactorizationMonoid

/-- Ordered radical roots construct actual-fiber charts for every Boolean selection of carrier-atom inequalities.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible parameter graph-and-band assembly step. -/
theorem s2v_t11b_parameter_boolean_actual_fiber_chart {A X : Type*}
    [CommRing A] [IsDomain A] [NormalizationMonoid (Polynomial A)]
    [UniqueFactorizationMonoid (Polynomial A)] [TopologicalSpace X] [PreconnectedSpace X]
    (φ : X → A →+* ℝ) (hφ : ∀ c, Continuous (fun t => φ t c))
    (P : Polynomial A) (hP : P ≠ 0) {k : ℕ} (Q : Fin k → Polynomial A)
    (hdiv : ∀ i, Q i ≠ 0 → Q i ∣ P) (C : (Fin k → Bool) → Bool)
    {m : ℕ} (ψ : Fin m → X → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hordered : ∀ t, StrictMono (fun i => ψ i t))
    (hroots : ∀ t x, (radical P).eval₂ (φ t) x = 0 ↔ ∃ i, x = ψ i t)
    (hsimple : ∀ t x, (radical P).eval₂ (φ t) x = 0 →
      ((radical P).map (φ t)).derivative.eval x ≠ 0) (a : X) :
    ∃ F : ({x : ℝ | C (fun i => decide (0 ≤ (Q i).eval₂ (φ a) x)) = true} × X) ≃ₜ
        {z : X × ℝ | C (fun i => decide (0 ≤ (Q i).eval₂ (φ z.1) z.2)) = true},
      ∀ y, (F y).val.1 = y.2 := by
  classical
  obtain ⟨E, hbase, hEroots, _⟩ := s2v_t11b_finite_sections_ambient_straightening ψ hψ hordered
  let S : Set (X × ℝ) := {z | C (fun i => decide (0 ≤ (Q i).eval₂ (φ z.1) z.2)) = true}
  have hconstant : ∀ b r, E.symm (b, r) ∈ S ↔ E.symm (a, r) ∈ S := by
    intro b r
    change C (fun i => decide (0 ≤ (Q i).eval₂ (φ (E.symm (b, r)).1) (E.symm (b, r)).2)) = true ↔
      C (fun i => decide (0 ≤ (Q i).eval₂ (φ (E.symm (a, r)).1) (E.symm (a, r)).2)) = true
    rw [s2v_t11b_ambient_inverse_base E hbase (b, r), s2v_t11b_ambient_inverse_base E hbase (a, r)]
    have hsign : (fun i => decide (0 ≤ (Q i).eval₂ (φ b) (E.symm (b, r)).2)) =
        (fun i => decide (0 ≤ (Q i).eval₂ (φ a) (E.symm (a, r)).2)) := by
      funext i
      by_cases hi : Q i = 0
      · simp only [hi, Polynomial.eval₂_zero]
      · exact Bool.decide_congr (s2v_t11b_parameter_atom_sign_at_normalized_height φ hφ P (Q i)
          hP hi (hdiv i hi) ψ hroots hsimple E hbase hEroots r b a)
    rw [hsign]
  obtain ⟨D, e, he⟩ := s2v_t11b_normalized_membership_product E hbase S a hconstant
  let R := s2v_t11b_productSubsetFiberChart S a
  let A := s2v_t11b_actualFiberProduct (fun z : S => z.val.1) e he a
  refine ⟨(R.symm.prodCongr (Homeomorph.refl X)).trans A, ?_⟩
  intro y
  exact s2v_t11b_actualFiberProduct_projection (fun z : S => z.val.1) e he a (R.symm y.1, y.2)

end HodgeLean.Foundations.Program
