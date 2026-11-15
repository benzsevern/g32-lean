import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteGcdRepresentatives
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Removing repeated real roots by actual polynomial common-divisor representatives.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A common-divisor representative has the minimum multiplicity of the two actual polynomials at every real root.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, common-root multiplicity step. -/
theorem s2v_t11b_common_divisor_rootMultiplicity (P Q G : Polynomial ℝ)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hG : G ≠ 0)
    (hdiv : ∀ D : Polynomial ℝ, D ∣ G ↔ D ∣ P ∧ D ∣ Q) (x : ℝ) :
    G.rootMultiplicity x = min (P.rootMultiplicity x) (Q.rootMultiplicity x) := by
  apply le_antisymm
  · obtain ⟨hp, hq⟩ := (hdiv _).mp (Polynomial.pow_rootMultiplicity_dvd G x)
    exact le_min ((Polynomial.le_rootMultiplicity_iff hP).mpr hp)
      ((Polynomial.le_rootMultiplicity_iff hQ).mpr hq)
  · apply (Polynomial.le_rootMultiplicity_iff hG).mpr
    apply (hdiv _).mpr
    exact ⟨(Polynomial.le_rootMultiplicity_iff hP).mp (min_le_left _ _),
      (Polynomial.le_rootMultiplicity_iff hQ).mp (min_le_right _ _)⟩


/-- Dividing by a derivative common-divisor representative removes repeated real roots while retaining the actual zero set, even with a nonzero scalar multiplier.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, specialized multiplicity removal step. -/
theorem s2v_t11b_scaled_squarefree_quotient (P G H : Polynomial ℝ) (u : ℝ)
    (hP : P ≠ 0) (hu : u ≠ 0) (he : G * H = Polynomial.C u * P)
    (hdiv : ∀ D : Polynomial ℝ, D ∣ G ↔ D ∣ P ∧ D ∣ P.derivative) :
    (∀ x : ℝ, H.eval x = 0 ↔ P.eval x = 0) ∧
      ∀ x : ℝ, H.eval x = 0 → H.derivative.eval x ≠ 0 := by
  have hcp : Polynomial.C u * P ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hu) hP
  have hgh : G * H ≠ 0 := he ▸ hcp
  have hG : G ≠ 0 := left_ne_zero_of_mul hgh
  have hH : H ≠ 0 := right_ne_zero_of_mul hgh
  have hmult : ∀ x : ℝ, P.eval x = 0 → H.rootMultiplicity x = 1 := by
    intro x hx
    have hd : P.derivative ≠ 0 := by
      intro hz
      have hc := Polynomial.eq_C_of_derivative_eq_zero hz
      have hv := congrArg (fun W : Polynomial ℝ => W.eval x) hc
      rw [hx, Polynomial.eval_C] at hv
      apply hP
      exact hc.trans (by rw [← hv, Polynomial.C_0])
    have hg := s2v_t11b_common_divisor_rootMultiplicity P P.derivative G hP hd hG hdiv x
    rw [Polynomial.derivative_rootMultiplicity_of_root hx] at hg
    rw [min_eq_right (Nat.sub_le _ _)] at hg
    have hm := congrArg (fun W : Polynomial ℝ => W.rootMultiplicity x) he
    rw [Polynomial.rootMultiplicity_mul hgh, Polynomial.rootMultiplicity_mul hcp] at hm
    have hc : (Polynomial.C u).rootMultiplicity x = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_C] using hu)
    rw [hc, zero_add, hg] at hm
    have hp : 0 < P.rootMultiplicity x := (Polynomial.rootMultiplicity_pos hP).mpr hx
    omega
  have hforward : ∀ x : ℝ, H.eval x = 0 → P.eval x = 0 := by
    intro x hx
    have hv := congrArg (fun W : Polynomial ℝ => W.eval x) he
    simp only [Polynomial.eval_mul, Polynomial.eval_C, hx, mul_zero] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_left hu
  refine ⟨fun x => ⟨hforward x, ?_⟩, ?_⟩
  · intro hx
    apply (Polynomial.rootMultiplicity_pos hH).mp
    rw [hmult x hx]
    omega
  · intro x hx hd
    have hlt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hH).mpr ⟨hx, hd⟩
    rw [hmult x (hforward x hx)] at hlt
    exact (lt_irrefl 1) hlt

end HodgeLean.Foundations.Program
