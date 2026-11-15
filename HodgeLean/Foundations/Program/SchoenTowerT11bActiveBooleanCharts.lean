import HodgeLean.Foundations.Program.SchoenTowerT11bSimultaneousRoots
import HodgeLean.Foundations.Program.SchoenTowerT11bEnumeratedAtomCoordinates

/-! Actual Boolean fiber charts from finite simultaneous active-atom refinements.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every active atom pattern has a finite Boolean cover giving actual-fiber charts on all its connected subregions, with no original simplicity or degree premise.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, simultaneous active Boolean chart step. -/
theorem s2v_t11b_active_boolean_finite_charts {n k : ℕ}
    (Q : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) (s : Fin k → Bool)
    (C : (Fin k → Bool) → Bool) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ t, t ∈ (s2v_t11b_activeAtomFormula Q s).realize → ∃ i, t ∈ (c i).realize) ∧
      ∀ i (K : Set (EuclideanSpace ℝ (Fin n))), K ⊆ (c i).realize → IsPreconnected K → ∀ a : K,
      ∃ F : ({x : ℝ | C (fun j => decide (0 ≤ (Q j).eval₂ (MvPolynomial.eval (fun v => a.val v)) x)) = true} × K) ≃ₜ
        {z : K × ℝ | C (fun j => decide (0 ≤ (Q j).eval₂ (MvPolynomial.eval (fun v => z.1.val v)) z.2)) = true},
        ∀ y, (F y).val.1 = y.2 := by
  classical
  obtain ⟨m, c, hcover, hroots⟩ := s2v_t11b_simultaneous_finite_root_pieces (s2v_t11b_activeFamily Q s)
  refine ⟨m, fun i => .inter (s2v_t11b_activeAtomFormula Q s) (c i), ?_, ?_⟩
  · intro t ht
    have hn : ∀ j, (s2v_t11b_activeFamily Q s j).map (MvPolynomial.eval (fun v => t v)) ≠ 0 := by
      intro j
      cases j with
      | none => exact s2v_t11b_activeCarrier_specialize_ne_zero Q s t ht
      | some j => exact ((s2v_t11b_activeAtomFormula_realize Q s t).mp ht j.val).mp j.property
    obtain ⟨i, hi⟩ := hcover t hn
    exact ⟨i, ht, hi⟩
  · intro i K hsub hK a
    haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
    have hactive : ∀ t : K, t.val ∈ (s2v_t11b_activeAtomFormula Q s).realize := fun t => (hsub t.property).1
    have hroot := hroots i K (fun t ht => (hsub ht).2) hK a
    obtain ⟨r, ψ, hc, hm, hr⟩ := hroot none
    obtain ⟨E, hbase, hEroots, _⟩ := s2v_t11b_finite_sections_ambient_straightening ψ hc hm
    let φ : K → MvPolynomial (Fin n) ℝ →+* ℝ := fun t => MvPolynomial.eval (fun v => t.val v)
    let S : Set (K × ℝ) := {z | C (fun j => decide (0 ≤ (Q j).eval₂ (φ z.1) z.2)) = true}
    have hconstant : ∀ b u, E.symm (b, u) ∈ S ↔ E.symm (a, u) ∈ S := by
      intro b u
      change C (fun j => decide (0 ≤ (Q j).eval₂ (φ (E.symm (b, u)).1) (E.symm (b, u)).2)) = true ↔
        C (fun j => decide (0 ≤ (Q j).eval₂ (φ (E.symm (a, u)).1) (E.symm (a, u)).2)) = true
      rw [s2v_t11b_ambient_inverse_base E hbase (b, u), s2v_t11b_ambient_inverse_base E hbase (a, u)]
      have hsign : (fun j => decide (0 ≤ (Q j).eval₂ (φ b) (E.symm (b, u)).2)) =
          (fun j => decide (0 ≤ (Q j).eval₂ (φ a) (E.symm (a, u)).2)) := by
        funext j
        by_cases hj : s j = true
        · obtain ⟨v, χ, hχ, _, hχroots⟩ := hroot (some ⟨j, hj⟩)
          have hcontained : ∀ t : K, ∀ x, (Q j).eval₂ (φ t) x = 0 → ∃ l, x = ψ l t := by
            intro t x hx
            apply (hr t x).mp
            exact (s2v_t11b_activeCarrier_zero_iff Q s (φ t) x).mpr ⟨j, hj, hx⟩
          have hF : Continuous (fun z : K × ℝ => (Q j).eval₂ (φ z.1) z.2) :=
            s2v_t11b_ringHom_family_section_continuous (fun z : K × ℝ => φ z.1)
              (fun q => (s2v_t11b_mv_parameter_eval_contDiff q).continuous.comp
                (continuous_subtype_val.comp continuous_fst)) (Q j) Prod.snd continuous_snd
          exact Bool.decide_congr (s2v_t11b_enumerated_atom_normalized_sign ψ hc
            (fun t => (hm t).injective) (fun t x => (Q j).eval₂ (φ t) x) hF χ hχ hχroots
            hcontained E hbase hEroots u b a)
        · have hz : ∀ t : K, (Q j).map (φ t) = 0 := by
            intro t
            by_contra hn
            exact hj (((s2v_t11b_activeAtomFormula_realize Q s t.val).mp (hactive t) j).mpr hn)
          simp only [Polynomial.eval₂_eq_eval_map, hz, Polynomial.eval_zero]
      rw [hsign]
    obtain ⟨D, e, he⟩ := s2v_t11b_normalized_membership_product E hbase S a hconstant
    let R := s2v_t11b_productSubsetFiberChart S a
    let A := s2v_t11b_actualFiberProduct (fun z : S => z.val.1) e he a
    refine ⟨(R.symm.prodCongr (Homeomorph.refl K)).trans A, ?_⟩
    intro y
    exact s2v_t11b_actualFiberProduct_projection (fun z : S => z.val.1) e he a (R.symm y.1, y.2)


/-- Every finite Boolean polynomial family has a finite cover of its whole parameter space giving actual-fiber charts on every connected subregion of a piece.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite Boolean cylindrical refinement step. -/
theorem s2v_t11b_boolean_finite_connected_subregion_charts {n k : ℕ}
    (Q : Fin k → Polynomial (MvPolynomial (Fin n) ℝ)) (C : (Fin k → Bool) → Bool) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ t : EuclideanSpace ℝ (Fin n), ∃ i, t ∈ (c i).realize) ∧
      ∀ i (K : Set (EuclideanSpace ℝ (Fin n))), K ⊆ (c i).realize → IsPreconnected K → ∀ a : K,
      ∃ F : ({x : ℝ | C (fun j => decide (0 ≤ (Q j).eval₂ (MvPolynomial.eval (fun v => a.val v)) x)) = true} × K) ≃ₜ
        {z : K × ℝ | C (fun j => decide (0 ≤ (Q j).eval₂ (MvPolynomial.eval (fun v => z.1.val v)) z.2)) = true},
        ∀ y, (F y).val.1 = y.2 := by
  classical
  choose m c hcover hcharts using (fun s : Fin k → Bool => s2v_t11b_active_boolean_finite_charts Q s C)
  let J := (s : Fin k → Bool) × Fin (m s)
  let E := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun i => c (E i).1 (E i).2, ?_, ?_⟩
  · intro t
    obtain ⟨s, hs, _⟩ := s2v_t11b_activeAtomFormula_partition Q t
    obtain ⟨i, hi⟩ := hcover s t hs
    refine ⟨E.symm ⟨s, i⟩, ?_⟩
    change t ∈ (c (E (E.symm (⟨s, i⟩ : J))).1 (E (E.symm (⟨s, i⟩ : J))).2).realize
    rw [E.apply_symm_apply]
    exact hi
  · intro i K hsub hK a
    exact hcharts (E i).1 (E i).2 K hsub hK a

end HodgeLean.Foundations.Program
