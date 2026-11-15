import HodgeLean.Foundations.Program.SchoenTowerHardtCellCharts
import HodgeLean.Foundations.Program.SchoenTowerHardt1Proofs
import HodgeLean.Foundations.Program.SchoenTowerT11bActiveAtoms
import HodgeLean.Foundations.Program.SchoenTowerHardt3Graphs

/-! Root preparation and graph transport interfaces. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad2_root_partition_aux {n k b : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (B : Fin b → s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ c : Fin m → s2v_t11b_Formula n,
      (∀ i, IsConnected (c i).realize) ∧
      Pairwise (fun i j => Disjoint (c i).realize (c j).realize) ∧
      (⋃ i, (c i).realize) = Set.univ ∧
      (∀ i j, (c i).realize ⊆ (B j).realize ∨
        Disjoint (c i).realize (B j).realize) ∧
      (∀ i j, (∀ a : (c i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
        (∀ a : (c i).realize,
        (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0)) ∧
      ∀ i, ∃ r : ℕ, ∃ ψ : Fin r → (c i).realize → ℝ,
        (∀ q, Continuous (ψ q)) ∧ (∀ a, StrictMono (fun q => ψ q a)) ∧
        ∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
          (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
          ∃ q, t = ψ q a := by
  classical
  choose m c hc hr using fun s : Fin k → Bool =>
    s2v_t11b_finite_pieces_ordered_roots (s2v_t11b_activeCarrier P s)
  let J := (s : Fin k → Bool) × Fin (m s) × (Fin b → Bool)
  let f : J → s2v_t11b_Formula n := fun j =>
    .inter (.inter (s2v_t11b_activeAtomFormula P j.1) (c j.1 j.2.1))
      (s2v_t11b_refinementFormula B j.2.2)
  let E := (Fintype.equivFin J).symm
  have hcover : ∀ x : EuclideanSpace ℝ (Fin n), ∃ i, x ∈ (f (E i)).realize := by
    intro x
    obtain ⟨s, hs, _⟩ := s2v_t11b_activeAtomFormula_partition P x
    obtain ⟨i, hi⟩ := hc s x (s2v_t11b_activeCarrier_specialize_ne_zero P s x hs)
    obtain ⟨t, ht, _⟩ := s2v_t11b_refinement_partition B x
    refine ⟨E.symm ⟨s, i, t⟩, ?_⟩
    change x ∈ (f (E (E.symm ⟨s, i, t⟩))).realize
    rw [E.apply_symm_apply]
    exact ⟨⟨hs, hi⟩, ht⟩
  obtain ⟨l, d, hd, hdc, hdisj, hsub⟩ :=
    s2v_hardt1_connected_boolean_refinement_aux (fun i => f (E i)) hcover
  choose z hz using hsub
  have ha : ∀ i x, x ∈ (d i).realize →
      x ∈ (s2v_t11b_activeAtomFormula P (E (z i)).1).realize :=
    fun i x hx => (hz i hx).1.1
  refine ⟨l, d, hd, hdisj, ?_, ?_, ?_, ?_⟩
  · exact Set.eq_univ_of_forall (fun x => Set.mem_iUnion.mpr (hdc x))
  · intro i j
    by_cases ht : (E (z i)).2.2 j = true
    · left
      intro x hx
      exact ((s2v_t11b_realize_refinementFormula B _ x).mp (hz i hx).2 j).mp ht
    · right
      apply Set.disjoint_left.mpr
      intro x hx hB
      exact ht (((s2v_t11b_realize_refinementFormula B _ x).mp (hz i hx).2 j).mpr hB)
  · intro i j
    by_cases ht : (E (z i)).1 j = true
    · right
      intro a
      exact ((s2v_t11b_activeAtomFormula_realize P _ a.val).mp (ha i a.val a.property) j).mp ht
    · left
      intro a
      by_contra hn
      exact ht (((s2v_t11b_activeAtomFormula_realize P _ a.val).mp (ha i a.val a.property) j).mpr hn)
  · intro i
    obtain ⟨x, hx⟩ := (hd i).nonempty
    obtain ⟨r, ψ, hψ, hm, hroot⟩ := hr (E (z i)).1 (E (z i)).2.1
      (d i).realize (fun x hx => (hz i hx).1.2) (hd i).isPreconnected ⟨x, hx⟩
    refine ⟨r, ψ, hψ, hm, ?_⟩
    intro a t
    rw [← hroot a t, s2v_t11b_activeCarrier_zero_iff]
    exact exists_congr fun j => and_congr
      (((s2v_t11b_activeAtomFormula_realize P _ a.val).mp (ha i a.val a.property) j).symm)
      Iff.rfl

theorem s2v_hardt_cad2_section_formulas_aux {n k r : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (C : s2v_t11b_Formula n) (hC : IsConnected C.realize)
    (ψ : Fin r → C.realize → ℝ) (hψ : ∀ q, Continuous (ψ q))
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hr : ∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔
      ∃ q, t = ψ q a)
    (D : s2v_t11b_Formula n) (hD : D.realize ⊆ C.realize) :
    ∃ g : Fin r → s2v_t11b_Formula (n + 1), ∀ q y,
      y ∈ (g q).realize ↔ ∃ a : D.realize,
        (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q ⟨a.val, hD a.property⟩ := by
  classical
  obtain ⟨R, hR⟩ := s2v_hardt3_active_root_formula P
  choose g hg using fun q : Fin r => s2v_hardt3_enumeration_graph D R
    (fun q a => ψ q ⟨a.val, hD a.property⟩)
    (fun a => hm ⟨a.val, hD a.property⟩)
    (fun a t => (hR a.val t).trans (hr ⟨a.val, hD a.property⟩ t)) q
  refine ⟨g, ?_⟩
  intro q y
  let a : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun v => y v.succ)
  have he : WithLp.toLp 2 (Fin.cons (y 0) (fun v => a v)) = y := by
    ext v
    exact Fin.cases rfl (fun _ => rfl) v
  have H := hg q a (y 0)
  rw [he] at H
  rw [H]
  constructor
  · rintro ⟨ha, ht⟩
    exact ⟨⟨a, ha⟩, fun _ => rfl, ht⟩
  · rintro ⟨b, hb, ht⟩
    have hab : a = b.val := by ext v; exact hb v
    refine ⟨hab.symm ▸ b.property, ?_⟩
    have hbEq : (⟨a, hab.symm ▸ b.property⟩ : D.realize) = b := Subtype.ext hab
    have hcast := congrArg (fun u : D.realize => ψ q ⟨u.val, hD u.property⟩) hbEq
    exact ht.trans hcast.symm

theorem s2v_hardt_cad2_graph_chart_formulas_aux {n d : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (s : C.realize → ℝ) (hs : Continuous s)
    (g : s2v_t11b_Formula (n + 1))
    (hg : ∀ y, y ∈ g.realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = s a)
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ a : C.realize, ∀ z : EuclideanSpace ℝ (Fin d),
      WithLp.toLp 2 (Fin.append (fun v => a.val v) (fun v => z v)) ∈ G.realize ↔
        z = (e a).val) :
    ∃ E : g.realize ≃ₜ
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1},
    ∃ F : s2v_t11b_Formula ((n + 1) + d),
    ∃ I : s2v_t11b_Formula (d + (n + 1)),
      (∀ a : C.realize, ∀ y : g.realize,
        (∀ v, y.val v.succ = a.val v) → E y = e a) ∧
      (∀ y : g.realize, ∀ z : EuclideanSpace ℝ (Fin d),
        WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
          z = (E y).val) ∧
      (∀ z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1},
        ∀ y : EuclideanSpace ℝ (Fin (n + 1)),
        WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => y v)) ∈ I.realize ↔
          y = (E.symm z).val) := by
  classical
  let base : g.realize → EuclideanSpace ℝ (Fin n) :=
    fun y => WithLp.toLp 2 (fun v => y.val v.succ)
  have hb : ∀ y, base y ∈ C.realize := by
    intro y
    obtain ⟨a, ha, _⟩ := (hg y.val).mp y.property
    have he : base y = a.val := by ext v; exact ha v
    exact he.symm ▸ a.property
  let p : g.realize → C.realize := fun y => ⟨base y, hb y⟩
  have hp : ∀ (a : C.realize) (y : g.realize),
      (∀ v, y.val v.succ = a.val v) → p y = a := by
    intro a y h
    apply Subtype.ext
    ext v
    exact h v
  let lift : C.realize → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun a => WithLp.toLp 2 (Fin.cons (s a) (fun v => a.val v))
  have hl : ∀ a, lift a ∈ g.realize :=
    fun a => (hg _).mpr ⟨a, fun _ => rfl, rfl⟩
  let h : g.realize ≃ₜ C.realize :=
    { toFun := p
      invFun := fun a => ⟨lift a, hl a⟩
      left_inv := by
        intro y
        obtain ⟨a, ha, h0⟩ := (hg y.val).mp y.property
        apply Subtype.ext
        ext v
        refine Fin.cases ?_ (fun j => ?_) v
        · change s (p y) = y.val 0
          rw [hp a y ha]
          exact h0.symm
        · rfl
      right_inv := by
        intro a
        exact hp a ⟨lift a, hl a⟩ (fun _ => rfl)
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
        apply continuous_pi
        intro v
        exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) v.succ).comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
        apply continuous_pi
        intro v
        refine Fin.cases ?_ (fun j => ?_) v
        · exact hs
        · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val }
  let E := h.trans e
  let f : Fin (n + d) → Fin ((n + 1) + d) :=
    Fin.addCases (fun v => v.succ.castAdd d) (fun v => Fin.natAdd (n + 1) v)
  let i : Fin (n + d) → Fin (d + (n + 1)) :=
    Fin.addCases (fun v => Fin.natAdd d v.succ) (fun v => v.castAdd (n + 1))
  let F := s2v_hardt1_rename f G
  let I := s2v_t11b_Formula.inter (s2v_hardt1_rename (Fin.natAdd d) g)
    (s2v_hardt1_rename i G)
  have hF : ∀ (y : g.realize) (z : EuclideanSpace ℝ (Fin d)),
      WithLp.toLp 2 (Fin.append (fun v => y.val v) (fun v => z v)) ∈ F.realize ↔
        z = (E y).val := by
    intro y z
    rw [s2v_hardt1_realize_rename]
    have he : WithLp.toLp 2 (fun v =>
        Fin.append (fun v => y.val v) (fun v => z v) (f v)) =
        WithLp.toLp 2 (Fin.append (fun v => (p y).val v) (fun v => z v)) := by
      ext v
      refine Fin.addCases (fun j => ?_) (fun j => ?_) v <;> simp [f, p, base]
    rw [he]
    exact hG (p y) z
  refine ⟨E, F, I, ?_, hF, ?_⟩
  · intro a y ha
    change e (p y) = e a
    rw [hp a y ha]
  · intro z y
    change (_ ∈ (s2v_hardt1_rename _ g).realize ∧
      _ ∈ (s2v_hardt1_rename _ G).realize) ↔ _
    rw [s2v_hardt1_realize_rename, s2v_hardt1_realize_rename]
    have hy : WithLp.toLp 2 (fun v =>
        Fin.append (fun v => z.val v) (fun v => y v) (Fin.natAdd d v)) = y := by
      ext v
      simp
    rw [hy]
    constructor
    · rintro ⟨hyg, hz⟩
      have he : WithLp.toLp 2 (fun v =>
          Fin.append (fun v => z.val v) (fun v => y v) (i v)) =
          WithLp.toLp 2 (Fin.append (fun v => (p ⟨y, hyg⟩).val v) (fun v => z.val v)) := by
        ext v
        refine Fin.addCases (fun j => ?_) (fun j => ?_) v <;> simp [i, p, base]
      rw [he, hG] at hz
      have hez : E ⟨y, hyg⟩ = z := Subtype.ext hz.symm
      exact congrArg Subtype.val ((E.injective (hez.trans (E.apply_symm_apply z).symm)))
    · intro hyz
      subst y
      refine ⟨(E.symm z).property, ?_⟩
      have he : WithLp.toLp 2 (fun v =>
          Fin.append (fun v => z.val v) (fun v => (E.symm z).val v) (i v)) =
          WithLp.toLp 2 (Fin.append (fun v => (p (E.symm z)).val v) (fun v => z.val v)) := by
        ext v
        refine Fin.addCases (fun j => ?_) (fun j => ?_) v <;> simp [i, p, base]
      rw [he, hG]
      exact congrArg Subtype.val (E.apply_symm_apply z).symm

end HodgeLean.Foundations.Program
