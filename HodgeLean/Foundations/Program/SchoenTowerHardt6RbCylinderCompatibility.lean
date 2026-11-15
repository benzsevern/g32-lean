import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBooleanSignCompatibility
import HodgeLean.Foundations.Program.SchoenTowerHardtCad3

/-! Prepared root graphs and bands respect every Boolean formula in the atom family. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_cylinder_compatibility {n r k h : ℕ}
    (P : Fin k → Polynomial (MvPolynomial (Fin n) ℝ))
    (C : s2v_t11b_Formula n) (hC : IsConnected C.realize)
    (ψ : Fin r → C.realize → ℝ) (hψ : ∀ q, Continuous (ψ q))
    (hm : ∀ a, StrictMono (fun q => ψ q a))
    (hz : ∀ j, (∀ a : C.realize,
      (P j).map (MvPolynomial.eval (fun v => a.val v)) = 0) ∨
      (∀ a : C.realize, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0))
    (hr : ∀ a t, (∃ j, (P j).map (MvPolynomial.eval (fun v => a.val v)) ≠ 0 ∧
      (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) t = 0) ↔ ∃ q, t = ψ q a)
    (hs : ∀ q j, (∀ a, (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) < 0) ∨
      (∀ a, (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a) = 0) ∨
      (∀ a, 0 < (P j).eval₂ (MvPolynomial.eval (fun v => a.val v)) (ψ q a)))
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (band : Fin (r + 1) → s2v_t11b_Formula (n + 1))
    (hg : ∀ q y, y ∈ (g q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ q a)
    (hb : ∀ q y, y ∈ (band q).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧
      (∀ j : Fin r, j.val < q.val → ψ j a < y 0) ∧
      (∀ j : Fin r, q.val ≤ j.val → y 0 < ψ j a))
    (B : Fin h → s2v_t11b_Formula (n + 1))
    (hB : ∀ j p, p ∈ (B j).atoms → ∃ i, MvPolynomial.finSuccEquiv ℝ n p = P i) :
    (∀ q j, (g q).realize ⊆ (B j).realize ∨ Disjoint (g q).realize (B j).realize) ∧
    (∀ q j, (band q).realize ⊆ (B j).realize ∨ Disjoint (band q).realize (B j).realize) := by
  obtain ⟨hbn, hgn, _⟩ := s2v_hardt_cad3_cylinder_partition C ψ hm hC.nonempty g hg band hb
  have hbs := s2v_hardt_cad3_band_signs C ψ hm hC hψ P hz
    (fun a t => (hr a t).symm) band hb
  have evaleq (p : MvPolynomial (Fin (n + 1)) ℝ) (j : Fin k)
      (hp : MvPolynomial.finSuccEquiv ℝ n p = P j)
      (z : EuclideanSpace ℝ (Fin (n + 1))) :
      MvPolynomial.eval (fun v => z v) p =
        (P j).eval₂ (MvPolynomial.eval (fun v => z v.succ)) (z 0) := by
    rw [← hp, s2v_t11b_finSucc_family_eval p (WithLp.toLp 2 (fun v => z v.succ)) (z 0)]
    exact congrArg (fun f => MvPolynomial.eval f p)
      (funext (fun v => Fin.cases rfl (fun _ => rfl) v))
  constructor
  · intro q j
    apply s2v_hardt6rb_boolean_sign_compatibility _ (hgn q)
    intro p hp
    obtain ⟨a, ha⟩ := hB j p hp
    have transfer (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ (g q).realize) :
        ∃ x : C.realize, MvPolynomial.eval (fun v => y v) p =
          (P a).eval₂ (MvPolynomial.eval (fun v => x.val v)) (ψ q x) := by
      obtain ⟨x, hx, ht⟩ := (hg q y).mp hy
      exact ⟨x, by rw [evaleq p a ha y, ht, funext hx]⟩
    rcases hs q a with h | h | h
    · exact Or.inl (fun y hy => by obtain ⟨x, he⟩ := transfer y hy; rw [he]; exact h x)
    · exact Or.inr (Or.inl (fun y hy => by obtain ⟨x, he⟩ := transfer y hy; rw [he]; exact h x))
    · exact Or.inr (Or.inr (fun y hy => by obtain ⟨x, he⟩ := transfer y hy; rw [he]; exact h x))
  · intro q j
    apply s2v_hardt6rb_boolean_sign_compatibility _ (hbn q)
    intro p hp
    obtain ⟨a, ha⟩ := hB j p hp
    rcases hbs q a with h | h | h
    · exact Or.inl (fun y hy => by rw [evaleq p a ha y]; exact h y hy)
    · exact Or.inr (Or.inl (fun y hy => by rw [evaleq p a ha y]; exact h y hy))
    · exact Or.inr (Or.inr (fun y hy => by rw [evaleq p a ha y]; exact h y hy))

end HodgeLean.Foundations.Program
