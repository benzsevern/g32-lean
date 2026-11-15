import HodgeLean.Foundations.Program.SchoenTowerHardtCad4Pre

/-! Connected root preparation retains uniform section signs and prescribed base marks. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_prepared_roots {n k h : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (D : Fin h → s2v_t11b_Formula n) :
    ∃ l : ℕ, ∃ C : Fin l → s2v_t11b_Formula n,
      (∀ i, IsConnected (C i).realize) ∧
      Pairwise (fun i j => Disjoint (C i).realize (C j).realize) ∧
      (⋃ i, (C i).realize) = Set.univ ∧
      (∀ i j, (C i).realize ⊆ (D j).realize ∨ Disjoint (C i).realize (D j).realize) ∧
      ∃ r : Fin l → ℕ, ∃ ψ : (i : Fin l) → Fin (r i) → (C i).realize → ℝ,
        (∀ i q, Continuous (ψ i q)) ∧
        (∀ i a, StrictMono (fun q => ψ i q a)) ∧
        (∀ i a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
          ∃ q, t = ψ i q a) ∧
        (∀ i j, (∀ a : (C i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
          (∀ a : (C i).realize,
          (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
        (∀ i q j, (∀ a : (C i).realize,
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ i q a) < 0) ∨
          (∀ a : (C i).realize,
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ i q a) = 0) ∨
          (∀ a : (C i).realize,
          0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ i q a))) ∧
        ∃ g : (i : Fin l) → Fin (r i) → s2v_t11b_Formula (n + 1),
        ∃ band : (i : Fin l) → Fin (r i + 1) → s2v_t11b_Formula (n + 1),
          (∀ i q y, y ∈ (g i q).realize ↔ ∃ a : (C i).realize,
            (∀ v, y v.succ = a.val v) ∧ y 0 = ψ i q a) ∧
          (∀ i q y, y ∈ (band i q).realize ↔ ∃ a : (C i).realize,
            (∀ v, y v.succ = a.val v) ∧
            (∀ j : Fin (r i), j.val < q.val → ψ i j a < y 0) ∧
            (∀ j : Fin (r i), q.val ≤ j.val → y 0 < ψ i j a)) := by
  classical
  obtain ⟨b, B, hB, hdis, hcover, hD, hz, hlift⟩ :=
    s2v_hardt_cad4_pre_root_lift P D
  choose r ψ hψ hm hr g band hg hb hbn hgn using hlift
  obtain ⟨s, S, hSu, hSd, hSn, hSs, l, C, dim, chart, forward, inverse,
    hn, hd, hu, hc, hdim, hF, hI, hrespect, hsignRespect,
    parent, into, roots, hinto, hroots, hcont, hmono, hroot, hzero, hsign⟩ :=
    s2v_hardt_cad4_sub_prepare (fun {k} F => s2v_hardt_cad4_pre_ambient F)
      P B hB hdis hcover r ψ hψ hm g hg hz hr
  have hsub (i : Fin l) : (C i).realize ⊆ (B (parent i)).realize := by
    intro x hx
    have he := hinto i ⟨x, hx⟩
    have hm := (into i ⟨x, hx⟩).property
    rw [he] at hm
    exact hm
  have hmarks (i : Fin l) (j : Fin h) :
      (C i).realize ⊆ (D j).realize ∨ Disjoint (C i).realize (D j).realize := by
    rcases hD (parent i) j with hij | hij
    · exact Or.inl ((hsub i).trans hij)
    · exact Or.inr (hij.mono_left (hsub i))
  choose G hG using fun i => s2v_hardt_cad2_section_formulas P (C i) (hc i)
    (roots i) (hcont i) (hmono i) (hroot i) (C i) (fun _ hx => hx)
  choose A hA using fun i => s2v_hardt_cad3_band_formulas (C i) (roots i)
    (hmono i) (G i) (hG i)
  exact ⟨l, C, hc, hd, hu, hmarks, (fun i => r (parent i)), roots,
    hcont, hmono, hroot, hzero, hsign, G, A, hG, hA⟩

end HodgeLean.Foundations.Program
