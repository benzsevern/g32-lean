import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBooleanFamilyCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbNormalizedSignPartition

/-! One constructed root presentation retains the original carrier, partition and marks in common coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_marked_root_presentation {n m q : ℕ}
    (f : s2v_t11b_Formula (n + 1))
    (b : Fin m → s2v_t11b_Formula (n + 1))
    (a : Fin q → s2v_t11b_Formula (n + 1)) :
    ∃ e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)),
    ∃ F : s2v_t11b_Formula (n + 1),
    ∃ J : s2v_t11b_Formula ((n + 1) + (n + 1)),
      F.realize = e ⁻¹' f.realize ∧
      (∀ z, z ∈ J.realize ↔ ∃ x : EuclideanSpace ℝ (Fin (n + 1)),
        (∀ i, z (Fin.castAdd (n + 1) i) = x i) ∧
        (∀ i, z (Fin.natAdd (n + 1) i) = e x i)) ∧
      ∃ Q : Polynomial (MvPolynomial (Fin n) ℝ), Q.Monic ∧
      ∃ t : ℕ, ∃ C : Fin t → s2v_t11b_Formula n,
        (∀ j, IsConnected (C j).realize) ∧
        Pairwise (fun i j => Disjoint (C i).realize (C j).realize) ∧
        (⋃ j, (C j).realize) = Set.univ ∧
        ∃ r : Fin t → ℕ, ∃ ψ : (j : Fin t) → Fin (r j) → (C j).realize → ℝ,
          (∀ j i, Continuous (ψ j i)) ∧
          (∀ j x, StrictMono (fun i => ψ j i x)) ∧
          (∀ j i (x : (C j).realize),
            Q.eval₂ (MvPolynomial.eval (fun k => x.val k)) (ψ j i x) = 0) ∧
          (∀ j (x : (C j).realize) z,
            Q.eval₂ (MvPolynomial.eval (fun k => x.val k)) z = 0 ↔ ∃ i, z = ψ j i x) ∧
          ∃ g : (j : Fin t) → Fin (r j) → s2v_t11b_Formula (n + 1),
          ∃ band : (j : Fin t) → Fin (r j + 1) → s2v_t11b_Formula (n + 1),
            (∀ j i z, z ∈ (g j i).realize ↔ ∃ x : (C j).realize,
              (∀ k, z k.succ = x.val k) ∧ z 0 = ψ j i x) ∧
            (∀ j i z, z ∈ (band j i).realize ↔ ∃ x : (C j).realize,
              (∀ k, z k.succ = x.val k) ∧
              (∀ k : Fin (r j), k.val < i.val → ψ j k x < z 0) ∧
              (∀ k : Fin (r j), i.val ≤ k.val → z 0 < ψ j k x)) ∧
            (∀ j i, (g j i).realize ⊆ e ⁻¹' f.realize ∨ Disjoint (g j i).realize (e ⁻¹' f.realize)) ∧
            (∀ j i, (band j i).realize ⊆ e ⁻¹' f.realize ∨ Disjoint (band j i).realize (e ⁻¹' f.realize)) ∧
            (∀ j i k, (g j i).realize ⊆ e ⁻¹' (a k).realize ∨ Disjoint (g j i).realize (e ⁻¹' (a k).realize)) ∧
            (∀ j i k, (band j i).realize ⊆ e ⁻¹' (a k).realize ∨ Disjoint (band j i).realize (e ⁻¹' (a k).realize)) ∧
            (∀ j i k, (g j i).realize ⊆ e ⁻¹' (b k).realize ∨ Disjoint (g j i).realize (e ⁻¹' (b k).realize)) ∧
            (∀ j i k, (band j i).realize ⊆ e ⁻¹' (b k).realize ∨ Disjoint (band j i).realize (e ⁻¹' (b k).realize)) := by
  classical
  let family : Fin (q + m + 1) → s2v_t11b_Formula (n + 1) := Fin.cons f (Fin.append a b)
  obtain ⟨e, N, hN, hunit, J, Jinv, hJ, hJinv⟩ := s2v_hardt6rb_boolean_family_coordinates family
  have hF : (N 0).realize = e ⁻¹' f.realize := by
    simpa only [family, Fin.cons_zero] using hN 0
  have hA (k : Fin q) : (N (Fin.castAdd m k).succ).realize = e ⁻¹' (a k).realize := by
    simpa only [family, Fin.cons_succ, Fin.append_left] using hN (Fin.castAdd m k).succ
  have hB (k : Fin m) : (N (Fin.natAdd q k).succ).realize = e ⁻¹' (b k).realize := by
    simpa only [family, Fin.cons_succ, Fin.append_right] using hN (Fin.natAdd q k).succ
  obtain ⟨Q, hQ, t, C, hC, hd, hu, _, hsections⟩ :=
    s2v_hardt6rb_normalized_sign_partition N hunit (fun i : Fin 0 => Fin.elim0 i)
  choose r ψ hψ hm hr g band hg hb hbn hgn hbd hgd hbg hcover hgN hbN using hsections
  refine ⟨e, N 0, J, hF, hJ, Q, hQ, t, C, hC, hd, hu, r, ψ, hψ, hm,
    (fun j i x => (hr j x _).mpr ⟨i, rfl⟩), hr, g, band, hg, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i
    simpa only [hF] using hgN j i 0
  · intro j i
    simpa only [hF] using hbN j i 0
  · intro j i k
    simpa only [hA k] using hgN j i (Fin.castAdd m k).succ
  · intro j i k
    simpa only [hA k] using hbN j i (Fin.castAdd m k).succ
  · intro j i k
    simpa only [hB k] using hgN j i (Fin.natAdd q k).succ
  · intro j i k
    simpa only [hB k] using hbN j i (Fin.natAdd q k).succ

end HodgeLean.Foundations.Program
