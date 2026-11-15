import HodgeLean.Foundations.Program.SchoenTowerHardtCad5CylindricalOpens
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ConnectedCells
import HodgeLean.Foundations.Program.SchoenTowerHardtCad4Sub

/-! One-base cylindrical lifting with openness retained in full ambient dimension. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_lift_open_cylinder {n k h r : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (Q : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))))
    (i : Fin Q.count) (hopen : Q.dim i = n → IsOpen (Q.cell i).realize)
    (ψ : Fin r → (Q.cell i).realize → ℝ) (hψ : ∀ l, Continuous (ψ l))
    (hm : ∀ a, StrictMono (fun l => ψ l a))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ l y, y ∈ (g l).realize ↔ ∃ a : (Q.cell i).realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ l a)
    (hz : ∀ p, (∀ a : (Q.cell i).realize, (P p).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : (Q.cell i).realize, (P p).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ a t, (∃ p, (P p).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔ ∃ l, t = ψ l a)
    (hs : ∀ l p, (∀ a : (Q.cell i).realize,
        (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ l a) < 0) ∨
      (∀ a : (Q.cell i).realize,
        (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ l a) = 0) ∨
      (∀ a : (Q.cell i).realize,
        0 < (P p).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ l a)))
    (B : Fin h → s2v_t11b_Formula (n + 1))
    (hB : ∀ j p, p ∈ (B j).atoms → ∃ l, MvPolynomial.finSuccEquiv ℝ n p = P l) :
    ∃ L : s2v_hardt_cad5_Partition
      {y : EuclideanSpace ℝ (Fin (n + 1)) | ∃ a : (Q.cell i).realize,
        ∀ v, y v.succ = a.val v},
      (∀ l j, (L.cell l).realize ⊆ (B j).realize ∨ Disjoint (L.cell l).realize (B j).realize) ∧
      (∀ l, L.dim l = n + 1 → IsOpen (L.cell l).realize) := by
  obtain ⟨m, c, dim, e, F, I, hn, hd, hc, hF, hI, ha, hsign,
    kind, hkind, hkindDim, hproj, hfiber⟩ :=
    s2v_hardt_cad4_sub_lift P (Q.cell i) (s2v_hardt_cad5_cell_connected Q i)
      (Q.chart i) (Q.forward i) (Q.forward_eq i) ψ hψ hm g hg hz hr hs B hB
  have hb (l : Fin m) : dim l ≤ n + 1 := by
    have he := hkindDim l
    have hi := Q.bound i
    cases hkl : kind l with
    | inl j =>
      simp only [hkl] at he
      rw [he]
      exact Nat.le_succ_of_le hi
    | inr j =>
      simp only [hkl] at he
      rw [he]
      exact Nat.add_le_add_right hi 1
  let L : s2v_hardt_cad5_Partition
      {y : EuclideanSpace ℝ (Fin (n + 1)) | ∃ a : (Q.cell i).realize,
        ∀ v, y v.succ = a.val v} :=
    { count := m, cell := c, dim := dim, chart := e, forward := F, inverse := I
      nonempty := hn, disjoint := hd, cover := hc, bound := hb
      forward_eq := hF, inverse_eq := hI }
  refine ⟨L, ha, ?_⟩
  intro l hl
  change dim l = n + 1 at hl
  have he := hkindDim l
  have hi := Q.bound i
  cases hkl : kind l with
  | inl j =>
    simp only [hkl] at he
    have hqi : Q.dim i = n + 1 := he.symm.trans hl
    rw [hqi] at hi
    omega
  | inr j =>
    simp only [hkl] at he
    have hqi : Q.dim i = n := Nat.add_right_cancel (he.symm.trans hl)
    have hcell : (c l).realize = {y : EuclideanSpace ℝ (Fin (n + 1)) |
        ∃ a : (Q.cell i).realize, (∀ v, y v.succ = a.val v) ∧
        (∀ p : Fin r, p.val < j.val → ψ p a < y 0) ∧
        (∀ p : Fin r, j.val ≤ p.val → y 0 < ψ p a)} := by
      ext y
      simpa only [hkl, Set.mem_ofPred_eq] using hkind l y
    change IsOpen (c l).realize
    rw [hcell]
    exact s2v_hardt_cad5_band_isOpen (Q.cell i).realize (hopen hqi) ψ hψ j

end HodgeLean.Foundations.Program
