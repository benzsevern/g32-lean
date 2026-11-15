import HodgeLean.Foundations.Program.TorusAlgebraizationB52Twisted
import HodgeLean.Foundations.Program.TorusAlgebraizationB52ExponentialRatio

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_theta_zero_equiv_of_cubic_eval (z w : b5_V Λ F)
    (hpair : ∀ u t : b5_sections Λ F hF Q 3, u.val z * t.val w = u.val w * t.val z)
    (s : b5_sections Λ F hF Q 1) (a : b5_V Λ F) :
    s.val (z + a) = 0 ↔ s.val (w + a) = 0 := by
  constructor
  · intro hz
    by_contra hw
    obtain ⟨u, t, h⟩ := b52_separates_points_of_theta_zero Λ F hF Q s z w a hz hw
    exact h (hpair u t)
  · intro hw
    by_contra hz
    obtain ⟨u, t, h⟩ := b52_separates_points_of_theta_zero Λ F hF Q s w z a hw hz
    exact h (hpair u t).symm

theorem b52_cubic_eval_factor (z w : b5_V Λ F)
    (hpair : ∀ u t : b5_sections Λ F hF Q 3, u.val z * t.val w = u.val w * t.val z)
    (u t : b5_sections Λ F hF Q 3) (hu : u.val z ≠ 0) (ht : t.val w ≠ 0) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ s : b5_sections Λ F hF Q 3, s.val w = C * s.val z := by
  have huw : u.val w ≠ 0 := by
    intro hh
    have hp := hpair u t
    rw [hh, zero_mul] at hp
    exact mul_ne_zero hu ht hp
  refine ⟨u.val w / u.val z, div_ne_zero huw hu, ?_⟩
  intro s
  calc
    s.val w = (u.val w * s.val z) / u.val z :=
      (eq_div_iff hu).mpr (by simpa only [mul_comm] using hpair u s)
    _ = _ := by ring

theorem b52_translation_exponential_of_cubic_eval (z h : b5_V Λ F)
    (hpair : ∀ u t : b5_sections Λ F hF Q 3,
      u.val z * t.val (z + h) = u.val (z + h) * t.val z)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0) :
    ∃ (L : b5_V Λ F →L[ℂ] ℂ) (c : ℂ), c ≠ 0 ∧
      ∀ x, s.val (x + h) = c * Complex.exp (L x) * s.val x := by
  obtain ⟨u, hu⟩ := b52_basepoint_of_nonzero_section Λ F hF Q s hs z
  obtain ⟨t, ht⟩ := b52_basepoint_of_nonzero_section Λ F hF Q s hs (z + h)
  obtain ⟨C, -, hC⟩ := b52_cubic_eval_factor Λ F hF Q z (z + h) hpair u t hu ht
  have hne : ∀ x, s.val x ≠ 0 → s.val (x + h) ≠ 0 := by
    intro x hx
    have he := b52_theta_zero_equiv_of_cubic_eval Λ F hF Q z (z + h) hpair s (x - z)
    have hxz : z + (x - z) = x := by abel
    have hxh : z + h + (x - z) = x + h := by abel
    rw [hxz, hxh] at he
    exact mt he.mpr hx
  let k := z + z + z
  have hprod : ∀ x, s.val x ≠ 0 → ∀ y, s.val y ≠ 0 → s.val (k - x - y) ≠ 0 →
      (s.val (x + h) / s.val x) * (s.val (y + h) / s.val y) *
        (s.val (k - x - y + h) / s.val (k - x - y)) = C := by
    intro x hx y hy hq
    let a := x - z
    let b := y - z
    let c := k - x - y - z
    have habc : a + b + c = 0 := by dsimp [a, b, c, k]; abel
    have hxa : z + a = x := by dsimp [a]; abel
    have hyb : z + b = y := by dsimp [b]; abel
    have hqc : z + c = k - x - y := by dsimp [c]; abel
    have hpa : z + h + a = x + h := by rw [add_right_comm, hxa]
    have hpb : z + h + b = y + h := by rw [add_right_comm, hyb]
    have hpc : z + h + c = k - x - y + h := by rw [add_right_comm, hqc]
    have he := hC (b5_balancedCubeSection Λ F hF Q s s s a b c habc)
    change s.val (z + h + a) * s.val (z + h + b) * s.val (z + h + c) =
      C * (s.val (z + a) * s.val (z + b) * s.val (z + c)) at he
    rw [hpa, hpb, hpc, hxa, hyb, hqc] at he
    field_simp
    linear_combination he
  obtain ⟨a, b, c, habc, ha, hb, hc⟩ := b52_balanced_nonzero s.property.1 hs z
  have heq : k - (z + c) - (z + b) = z + a := by
    calc
      _ = z - (a + b + c) + a := by dsimp [k]; abel
      _ = _ := by rw [habc]; simp
  exact b52_exponential_of_balanced_quotient s.val (fun x ↦ s.val (x + h))
    s.property.1 (s.property.1.comp (differentiable_id.add_const h)) hne k C hprod
    (z + b) (z + c) hb hc (by rwa [heq])

theorem b52_translation_exponent_lattice (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (h : b5_V Λ F) (L : b5_V Λ F →L[ℂ] ℂ) (c : ℂ) (hc : c ≠ 0)
    (htrans : ∀ x, s.val (x + h) = c * Complex.exp (L x) * s.val x) (l : Λ) :
    Complex.exp (L (b5_lattice Λ F l)) =
      Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) h) := by
  obtain ⟨z, hz⟩ : ∃ z, s.val z ≠ 0 := by
    by_contra hn
    exact hs (funext fun z ↦ by simpa using not_not.mp (not_exists.mp hn z))
  have hj : b5_factor Λ F hF Q l z ≠ 0 :=
    mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)
  have he := htrans (z + b5_lattice Λ F l)
  rw [add_right_comm z (b5_lattice Λ F l) h, s.property.2 l (z + h),
    s.property.2 l z, pow_one, pow_one, b5_factor_add_right, htrans z,
    map_add, Complex.exp_add] at he
  have hm : (Complex.exp (L (b5_lattice Λ F l)) -
      Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) h)) *
      (c * Complex.exp (L z) * b5_factor Λ F hF Q l z * s.val z) = 0 := by
    linear_combination -he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) hj) hz))

theorem b52_translation_exponent_eq_H
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (h : b5_V Λ F) (L : b5_V Λ F →L[ℂ] ℂ) (c : ℂ) (hc : c ≠ 0)
    (htrans : ∀ x, s.val (x + h) = c * Complex.exp (L x) * s.val x) :
    ∀ x, L x = (Real.pi : ℂ) * b5_H Λ F hF Q h x := by
  apply b52_linear_eq_H_of_real_lattice Λ F hF Q hherm h L
  intro l
  have he := congrArg norm (b52_translation_exponent_lattice Λ F hF Q s hs h L c hc htrans l)
  simp only [Complex.norm_exp] at he
  exact Real.exp_injective he

theorem b52_cubic_eval_forces_dual_character_one
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (z h : b5_V Λ F)
    (hpair : ∀ u t : b5_sections Λ F hF Q 3,
      u.val z * t.val (z + h) = u.val (z + h) * t.val z)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0)
    (L : b5_V Λ F →L[ℂ] ℂ) (c : ℂ) (hc : c ≠ 0)
    (htrans : ∀ x, s.val (x + h) = c * Complex.exp (L x) * s.val x)
    (d : b5_V Λ F)
    (hd : ∀ l : Λ, ∃ n : ℤ, (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n) :
    Complex.exp (L d - Real.pi * b5_H Λ F hF Q d h) = 1 := by
  have hd₀ : ∀ l : Λ, ∃ n : ℤ, (b5_H Λ F hF Q (b5_lattice Λ F l) 0).im = n := by
    intro l
    exact ⟨0, by simp [b5_H]⟩
  obtain ⟨a₀, b₀, e₀, hab₀, ha₀, hb₀, he₀⟩ :=
    b52_prescribed_sum_nonzero s.property.1 hs z 0
  obtain ⟨a, b, e, habe, ha, hb, he⟩ := b52_prescribed_sum_nonzero s.property.1 hs z d
  let T₀ := b52_dualTwistedCubeSection Λ F hF Q hherm 0 hd₀ s s s a₀ b₀ e₀ hab₀
  let T := b52_dualTwistedCubeSection Λ F hF Q hherm d hd s s s a b e habe
  have hT₀ : T₀.val z ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero ha₀ hb₀) he₀)
  have hT : T.val z ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero ha hb) he)
  let K := c ^ 3 * Complex.exp (L (z + z + z))
  let χ := Complex.exp (L d - Real.pi * b5_H Λ F hF Q d h)
  have hK : K ≠ 0 := mul_ne_zero (pow_ne_zero 3 hc) (Complex.exp_ne_zero _)
  have hshift₀ := b52_dualTwistedCubeSection_translate Λ F hF Q hherm 0 hd₀
    s a₀ b₀ e₀ hab₀ h L c htrans z
  change T₀.val (z + h) = K *
    Complex.exp (L 0 - Real.pi * b5_H Λ F hF Q 0 h) * T₀.val z at hshift₀
  have hexp₀ : Complex.exp (L 0 - Real.pi * b5_H Λ F hF Q 0 h) = 1 := by
    simp [b5_H]
  rw [hexp₀, mul_one] at hshift₀
  have hshift := b52_dualTwistedCubeSection_translate Λ F hF Q hherm d hd
    s a b e habe h L c htrans z
  change T.val (z + h) = K * χ * T.val z at hshift
  have hp := hpair T₀ T
  rw [hshift₀, hshift] at hp
  have hm : (K * T₀.val z * T.val z) * (χ - 1) = 0 := by
    linear_combination hp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (mul_ne_zero (mul_ne_zero hK hT₀) hT))

theorem b52_points_of_nonzero_section
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (s : b5_sections Λ F hF Q 1) (hs : s.val ≠ 0) (z h : b5_V Λ F)
    (hh : ¬ ∃ l : Λ, h = b5_lattice Λ F l) :
    ∃ u t : b5_sections Λ F hF Q 3,
      u.val z * t.val (z + h) ≠ u.val (z + h) * t.val z := by
  by_contra hn
  have hpair : ∀ u t : b5_sections Λ F hF Q 3,
      u.val z * t.val (z + h) = u.val (z + h) * t.val z := by
    intro u t
    by_contra hne
    exact hn ⟨u, t, hne⟩
  obtain ⟨L, c, hc, htrans⟩ :=
    b52_translation_exponential_of_cubic_eval Λ F hF Q z h hpair s hs
  have hL := b52_translation_exponent_eq_H Λ F hF Q hherm s hs h L c hc htrans
  obtain ⟨d, hd, hnd⟩ := b52_dual_lattice_separates Λ F hF Q hpos h hh
  have he := b52_cubic_eval_forces_dual_character_one Λ F hF Q hherm z h hpair
    s hs L c hc htrans d hd
  rw [hL d] at he
  apply hnd
  apply (b52_exp_hermitian_commutator_eq_one_iff Λ F hF Q hherm h d).mp
  convert he using 1 <;> congr 1 <;> ring

end HodgeLean.Foundations.Program
