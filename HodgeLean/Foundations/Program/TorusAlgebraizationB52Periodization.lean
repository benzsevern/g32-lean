import HodgeLean.Foundations.Program.TorusAlgebraizationDefs

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Sum of lattice translates divided by their automorphy factors. -/
def b52_periodize {L V : Type*} [AddCommGroup L] [AddCommGroup V]
    (ι : L →+ V) (j : L → V → ℂ) (f : V → ℂ) (z : V) : ℂ :=
  ∑' l : L, f (z + ι l) / j l z

theorem b52_periodize_translate {L V : Type*} [AddCommGroup L] [AddCommGroup V]
    (ι : L →+ V) (j : L → V → ℂ)
    (hj : ∀ l m z, j (l + m) z = j l (z + ι m) * j m z)
    (hne : ∀ l z, j l z ≠ 0) (f : V → ℂ) (m : L) (z : V) :
    b52_periodize ι j f (z + ι m) = j m z * b52_periodize ι j f z := by
  unfold b52_periodize
  rw [← (Equiv.addRight m).tsum_eq (f := fun l ↦ f (z + ι l) / j l z),
    ← tsum_mul_left]
  apply tsum_congr
  intro l
  change f (z + ι m + ι l) / j l (z + ι m) =
    j m z * (f (z + ι (l + m)) / j (l + m) z)
  rw [map_add, hj]
  have he : z + ι m + ι l = z + (ι l + ι m) := by abel
  rw [he]
  field_simp [hne l (z + ι m), hne m z]

theorem b52_norm_inv_factor (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) (l : Λ) (z : b5_V Λ F) :
    ‖(b5_factor Λ F hF Q l z)⁻¹‖ =
      Real.exp (-(Real.pi * (b5_H Λ F hF Q (b5_lattice Λ F l) z).re +
        (Real.pi / 2) * (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l)).re)) := by
  rw [norm_inv, b5_factor, norm_mul, (b5_chi Λ Q l).norm_coe, one_mul,
    Complex.norm_exp, ← Real.exp_neg]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div]

#print axioms b52_periodize_translate
#print axioms b52_norm_inv_factor

end HodgeLean.Foundations.Program
