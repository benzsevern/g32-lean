import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPreparedRoots
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCylinderCompatibility
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMonicAtomRootUnion

/-! Normalized Boolean families have marked cylindrical partitions with a common monic root constraint. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_normalized_sign_partition {n m h : ℕ}
    (B : Fin m → s2v_t11b_Formula (n + 1))
    (hB : ∀ j p, p ∈ (B j).atoms → p ≠ 0 →
      IsUnit (MvPolynomial.finSuccEquiv ℝ n p).leadingCoeff)
    (D : Fin h → s2v_t11b_Formula n) :
    ∃ Q : Polynomial (MvPolynomial (Fin n) ℝ), Q.Monic ∧
    ∃ l : ℕ, ∃ C : Fin l → s2v_t11b_Formula n,
      (∀ i, IsConnected (C i).realize) ∧
      Pairwise (fun i j => Disjoint (C i).realize (C j).realize) ∧
      (⋃ i, (C i).realize) = Set.univ ∧
      (∀ i j, (C i).realize ⊆ (D j).realize ∨ Disjoint (C i).realize (D j).realize) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (C i).realize → ℝ,
        (∀ q, Continuous (ψ q)) ∧ (∀ a, StrictMono (fun q => ψ q a)) ∧
        (∀ a t, Q.eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0 ↔ ∃ q, t = ψ q a) ∧
        ∃ g : Fin r → s2v_t11b_Formula (n + 1),
        ∃ band : Fin (r + 1) → s2v_t11b_Formula (n + 1),
          (∀ q y, y ∈ (g q).realize ↔ ∃ a : (C i).realize,
            (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a) ∧
          (∀ q y, y ∈ (band q).realize ↔ ∃ a : (C i).realize,
            (∀ v, y v.succ = a.val v) ∧
            (∀ j : Fin r, j.val < q.val → ψ j a < y 0) ∧
            (∀ j : Fin r, q.val ≤ j.val → y 0 < ψ j a)) ∧
          (∀ q, (band q).realize.Nonempty) ∧ (∀ q, (g q).realize.Nonempty) ∧
          Pairwise (fun q t => Disjoint (band q).realize (band t).realize) ∧
          Pairwise (fun q t => Disjoint (g q).realize (g t).realize) ∧
          (∀ q t, Disjoint (band q).realize (g t).realize) ∧
          (∀ y, ((∃ q, y ∈ (band q).realize) ∨ (∃ q, y ∈ (g q).realize)) ↔
            ∃ a : (C i).realize, ∀ v, y v.succ = a.val v) ∧
          (∀ q j, (g q).realize ⊆ (B j).realize ∨ Disjoint (g q).realize (B j).realize) ∧
          (∀ q j, (band q).realize ⊆ (B j).realize ∨ Disjoint (band q).realize (B j).realize) := by
  classical
  obtain ⟨Q, hQ, hQroots⟩ := s2v_hardt6rb_monic_atom_root_union B hB
  let atoms := Finset.univ.biUnion (fun j : Fin m => (B j).atoms)
  let enum := (Fintype.equivFin {p // p ∈ atoms}).symm
  let P : Fin (Fintype.card {p // p ∈ atoms} + 1) →
      Polynomial (MvPolynomial (Fin n) ℝ) :=
    Fin.cons Q (fun j => MvPolynomial.finSuccEquiv ℝ n (enum j).val)
  have hatoms : ∀ j p, p ∈ (B j).atoms →
      ∃ a, MvPolynomial.finSuccEquiv ℝ n p = P a := by
    intro j p hp
    have hm : p ∈ atoms := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp⟩
    refine ⟨((Fintype.equivFin {p // p ∈ atoms}) ⟨p, hm⟩).succ, ?_⟩
    simp only [P, Fin.cons_succ, enum, Equiv.symm_apply_apply]
  have hinQ (x : Fin n → ℝ) (t : ℝ)
      (hr : ∃ j, (P j).map (MvPolynomial.eval x) ≠ 0 ∧
        (P j).eval₂ (MvPolynomial.eval x) t = 0) : Q.eval₂ (MvPolynomial.eval x) t = 0 := by
    obtain ⟨j, hj, ht⟩ := hr
    revert hj ht
    refine Fin.cases (fun _ ht => ht) (fun a hne ht => ?_) j
    have hp0 : (enum a).val ≠ 0 := by
      intro he
      apply hne
      simp only [P, Fin.cons_succ, he, map_zero, Polynomial.map_zero]
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (enum a).property
    apply (hQroots x t).mpr ⟨j, (enum a).val, hj, hp0, ?_⟩
    rw [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map]
    exact ht
  obtain ⟨l, C, hc, hd, hu, hD, r, ψ, hψ, hm, hr, hz, hs, g, band, hg, hb⟩ :=
    s2v_hardt6rb_prepared_roots P D
  refine ⟨Q, hQ, l, C, hc, hd, hu, hD, ?_⟩
  intro i
  have hroots (a : (C i).realize) (t : ℝ) :
      Q.eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0 ↔ ∃ q, t = ψ i q a := by
    constructor
    · intro ht
      exact (hr i a t).mp ⟨0, Polynomial.map_monic_ne_zero hQ, ht⟩
    · intro ht
      exact hinQ _ _ ((hr i a t).mpr ht)
  obtain ⟨hbn, hgn, hbd, hgd, hbg, hcover, _⟩ :=
    s2v_hardt_cad3_cylinder_partition (C i) (ψ i) (hm i) (hc i).nonempty
      (g i) (hg i) (band i) (hb i)
  obtain ⟨hgB, hbB⟩ := s2v_hardt6rb_cylinder_compatibility P (C i) (hc i)
    (ψ i) (hψ i) (hm i) (hz i) (hr i) (hs i) (g i) (band i) (hg i) (hb i) B hatoms
  exact ⟨r i, ψ i, hψ i, hm i, hroots, g i, band i, hg i, hb i,
    hbn, hgn, hbd, hgd, hbg, hcover, hgB, hbB⟩

end HodgeLean.Foundations.Program
