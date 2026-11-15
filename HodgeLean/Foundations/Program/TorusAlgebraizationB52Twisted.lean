import HodgeLean.Foundations.Program.TorusAlgebraizationB52Dual
import HodgeLean.Foundations.Program.TorusAlgebraizationB52Nonzero

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_triple_translate_automorphy (s t u : b5_sections Λ F hF Q 1)
    (a b c : b5_V Λ F) (l : Λ) (z : b5_V Λ F) :
    s.val (z + b5_lattice Λ F l + a) * t.val (z + b5_lattice Λ F l + b) *
      u.val (z + b5_lattice Λ F l + c) =
    b5_factor Λ F hF Q l z ^ 3 *
      Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) (a + b + c)) *
      (s.val (z + a) * t.val (z + b) * u.val (z + c)) := by
  rw [add_right_comm z (b5_lattice Λ F l) a,
    add_right_comm z (b5_lattice Λ F l) b,
    add_right_comm z (b5_lattice Λ F l) c,
    s.property.2 l (z + a), t.property.2 l (z + b), u.property.2 l (z + c),
    b5_factor_add_right, b5_factor_add_right, b5_factor_add_right]
  simp only [pow_one, b5_H_add_right, mul_add, Complex.exp_add]
  ring

def b52_dualTwistedCubeSection
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (d : b5_V Λ F)
    (hd : ∀ l : Λ, ∃ n : ℤ, (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)
    (s t u : b5_sections Λ F hF Q 1) (a b c : b5_V Λ F) (habc : a + b + c = d) :
    b5_sections Λ F hF Q 3 := by
  refine ⟨fun z ↦ Complex.exp (-(Real.pi * b5_H Λ F hF Q d z)) *
    (s.val (z + a) * t.val (z + b) * u.val (z + c)), ?_, ?_⟩
  · have hg : Differentiable ℂ (fun z ↦ Complex.exp (-(Real.pi * b5_H Λ F hF Q d z))) :=
      (b52_seedForPoint Λ F hF Q d).differentiable.neg.cexp
    exact hg.mul (((s.property.1.comp (differentiable_id.add_const a)).mul
      (t.property.1.comp (differentiable_id.add_const b))).mul
      (u.property.1.comp (differentiable_id.add_const c)))
  · intro l z
    change Complex.exp (-(Real.pi * b5_H Λ F hF Q d (z + b5_lattice Λ F l))) *
      (s.val (z + b5_lattice Λ F l + a) * t.val (z + b5_lattice Λ F l + b) *
        u.val (z + b5_lattice Λ F l + c)) = _
    rw [b52_triple_translate_automorphy, habc, b5_H_add_right, mul_add, neg_add,
      Complex.exp_add]
    have he : Complex.exp (-(Real.pi * b5_H Λ F hF Q d (b5_lattice Λ F l))) *
        Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) d) = 1 := by
      rw [← Complex.exp_add]
      convert (b52_exp_hermitian_commutator_eq_one_iff Λ F hF Q hherm
        (b5_lattice Λ F l) d).mpr (hd l) using 1 <;> congr 1 <;> ring
    calc
      _ = b5_factor Λ F hF Q l z ^ 3 * Complex.exp (-(Real.pi * b5_H Λ F hF Q d z)) *
          (Complex.exp (-(Real.pi * b5_H Λ F hF Q d (b5_lattice Λ F l))) *
            Complex.exp (Real.pi * b5_H Λ F hF Q (b5_lattice Λ F l) d)) *
          (s.val (z + a) * t.val (z + b) * u.val (z + c)) := by ring
      _ = _ := by rw [he]; ring

theorem b52_dualTwistedCubeSection_translate
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (d : b5_V Λ F)
    (hd : ∀ l : Λ, ∃ n : ℤ, (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)
    (s : b5_sections Λ F hF Q 1) (a b e : b5_V Λ F) (habe : a + b + e = d)
    (h : b5_V Λ F) (L : b5_V Λ F →L[ℂ] ℂ) (c : ℂ)
    (htrans : ∀ x, s.val (x + h) = c * Complex.exp (L x) * s.val x)
    (z : b5_V Λ F) :
    let t := b52_dualTwistedCubeSection Λ F hF Q hherm d hd s s s a b e habe
    t.val (z + h) = c ^ 3 * Complex.exp (L (z + z + z)) *
      Complex.exp (L d - Real.pi * b5_H Λ F hF Q d h) * t.val z := by
  change Complex.exp (-(Real.pi * b5_H Λ F hF Q d (z + h))) *
    (s.val (z + h + a) * s.val (z + h + b) * s.val (z + h + e)) =
    c ^ 3 * Complex.exp (L (z + z + z)) *
      Complex.exp (L d - Real.pi * b5_H Λ F hF Q d h) *
      (Complex.exp (-(Real.pi * b5_H Λ F hF Q d z)) *
        (s.val (z + a) * s.val (z + b) * s.val (z + e)))
  rw [add_right_comm z h a, add_right_comm z h b, add_right_comm z h e,
    htrans, htrans, htrans, ← habe]
  simp only [map_add, b5_H_add_right, mul_add, neg_add, sub_eq_add_neg, Complex.exp_add]
  ring

theorem b52_prescribed_sum_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} (hf : Differentiable ℂ f) (hne : f ≠ 0) (z d : E) :
    ∃ a b c : E, a + b + c = d ∧ f (z + a) ≠ 0 ∧ f (z + b) ≠ 0 ∧ f (z + c) ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hn
    exact hne (funext fun x ↦ by simpa using not_not.mp (not_exists.mp hn x))
  obtain ⟨b, c, hbc, hb, hc⟩ := b52_fixed_balanced_nonzero hf hne z (x - z - d)
  refine ⟨x - z, b, c, ?_, ?_, hb, hc⟩
  · calc
      _ = (x - z - d + b + c) + d := by abel
      _ = d := by rw [hbc]; simp
  · have he : z + (x - z) = x := by abel
    rwa [he]

end HodgeLean.Foundations.Program
