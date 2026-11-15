import HodgeLean.Foundations.Program.TorusAlgebraizationB52Gaussian
import HodgeLean.Foundations.Program.RelativeTorusAlg
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_H_real_bilinear : IsBilinearMap ℝ (b5_H Λ F hF Q) := by
  constructor
  · intro x y z
    simp only [b5_H, map_add]
    ring
  · intro a x y
    simp only [← Complex.coe_smul, b5_H, map_smul, b2a_conj_smul,
      Complex.conj_ofReal, smul_eq_mul]
    ring
  · intro x y z
    simp only [b5_H, map_add, LinearMap.add_apply]
    ring
  · intro a x y
    simp only [← Complex.coe_smul, b5_H, map_smul, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

#print axioms b52_H_real_bilinear

def b52_H_continuousBilinear : b5_V Λ F →L[ℝ] b5_V Λ F →L[ℝ] ℂ :=
  (b52_H_real_bilinear Λ F hF Q).toContinuousBilinearMap

@[simp] theorem b52_H_continuousBilinear_apply (x y : b5_V Λ F) :
    b52_H_continuousBilinear Λ F hF Q x y = b5_H Λ F hF Q x y := rfl

theorem b52_H_diagonal_continuous :
    Continuous (fun x ↦ (b5_H Λ F hF Q x x).re) := by
  have h : Continuous (fun x : b5_V Λ F ↦
      b52_H_continuousBilinear Λ F hF Q x x) :=
    (b52_H_continuousBilinear Λ F hF Q).continuous.clm_apply continuous_id
  simpa only [Function.comp_def, b52_H_continuousBilinear_apply] using
    Complex.continuous_re.comp h

#print axioms b52_H_diagonal_continuous

theorem b52_H_diagonal_smul (a : ℝ) (x : b5_V Λ F) :
    (b5_H Λ F hF Q (a • x) (a • x)).re =
      a ^ 2 * (b5_H Λ F hF Q x x).re := by
  rw [(b52_H_real_bilinear Λ F hF Q).smul_left,
    (b52_H_real_bilinear Λ F hF Q).smul_right]
  simp only [Complex.smul_re, smul_eq_mul]
  ring

#print axioms b52_H_diagonal_smul

theorem b52_H_lower_bound
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ (b5_H Λ F hF Q x x).re := by
  exact b52_quadratic_lower_bound _ (b52_H_diagonal_continuous Λ F hF Q)
    (b52_H_diagonal_smul Λ F hF Q) hpos

#print axioms b52_H_lower_bound

theorem b52_H_re_bound (x y : b5_V Λ F) :
    |(b5_H Λ F hF Q x y).re| ≤
      ‖b52_H_continuousBilinear Λ F hF Q‖ * ‖x‖ * ‖y‖ := by
  apply (Complex.abs_re_le_norm _).trans
  simpa only [b52_H_continuousBilinear_apply] using
    (b52_H_continuousBilinear Λ F hF Q).le_opNorm₂ x y

#print axioms b52_H_re_bound

theorem b52_summable_H_exponential
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (L : Submodule ℤ (b5_V Λ F)) [DiscreteTopology L]
    (a : ℝ) (ha : 0 < a) (b : ℝ) (z : b5_V Λ F) :
    Summable (fun l : L ↦ Real.exp
      (-a * (b5_H Λ F hF Q l l).re - b * (b5_H Λ F hF Q l z).re)) := by
  have hp : ∀ x : b5_V Λ F, -b * (b5_H Λ F hF Q x z).re ≤
      (|b| * ‖b52_H_continuousBilinear Λ F hF Q‖ * ‖z‖) * ‖x‖ := by
    intro x
    calc
      _ ≤ |(-b) * (b5_H Λ F hF Q x z).re| := le_abs_self _
      _ = |b| * |(b5_H Λ F hF Q x z).re| := by rw [abs_mul, abs_neg]
      _ ≤ |b| * (‖b52_H_continuousBilinear Λ F hF Q‖ * ‖x‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (b52_H_re_bound Λ F hF Q x z) (abs_nonneg _)
      _ = _ := by ring
  have hs := b52_summable_positive_quadratic L
    (fun x ↦ a * (b5_H Λ F hF Q x x).re)
    (continuous_const.mul (b52_H_diagonal_continuous Λ F hF Q))
    (fun c x ↦ by rw [b52_H_diagonal_smul]; ring)
    (fun x hx ↦ mul_pos ha (hpos x hx))
    (fun x ↦ -b * (b5_H Λ F hF Q x z).re)
    (|b| * ‖b52_H_continuousBilinear Λ F hF Q‖ * ‖z‖) hp
  simpa only [neg_mul, sub_eq_add_neg] using hs

#print axioms b52_summable_H_exponential

include hF in
theorem b52_lattice_discrete : DiscreteTopology (b5_lattice Λ F).range := by
  haveI := b2_latticeMap_discrete F hF
  have hd : IsDiscrete ((b2_latticeMap Λ F).range : Set ((ℂ ⊗[ℤ] Λ) ⧸ F)) :=
    isDiscrete_iff_discreteTopology.mpr inferInstance
  have hi := hd.image (b2_coordHomeomorph Λ F).isEmbedding.isInducing
  apply isDiscrete_iff_discreteTopology.mp
  convert hi using 1
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨b2_latticeMap Λ F l, ⟨l, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, rfl⟩

#print axioms b52_lattice_discrete

include hF in
theorem b52_lattice_injective : Function.Injective (b5_lattice Λ F) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : b5_lattice Λ F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  change (b2_coord _) (b2_latticeMap Λ F (x - y)) = 0 at hz
  have hm : b2_latticeMap Λ F (x - y) = 0 := by
    apply (b2_coord _).injective
    simpa only [map_zero] using hz
  have hmem : (1 : ℂ) ⊗ₜ[ℤ] (x - y) ∈ F :=
    (Submodule.Quotient.mk_eq_zero F).mp hm
  apply b2a_incl_injective
  simpa only [TensorProduct.tmul_zero] using b2a_incl_eq_zero_of_mem hF hmem

#print axioms b52_lattice_injective

theorem b52_summable_norm_inv_factor
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (z : b5_V Λ F) : Summable (fun l : Λ ↦ ‖(b5_factor Λ F hF Q l z)⁻¹‖) := by
  haveI := b52_lattice_discrete Λ F hF
  let ι := (b5_lattice Λ F).rangeRestrict
  have hi : Function.Injective ι := by
    intro x y hxy
    exact b52_lattice_injective Λ F hF (congrArg Subtype.val hxy)
  have hs := (b52_summable_H_exponential Λ F hF Q hpos (b5_lattice Λ F).range
    (Real.pi / 2) (by positivity) Real.pi z).comp_injective hi
  convert hs using 1
  ext l
  rw [b52_norm_inv_factor]
  change Real.exp _ = Real.exp
    (-(Real.pi / 2) * (b5_H Λ F hF Q (b5_lattice Λ F l) (b5_lattice Λ F l)).re -
      Real.pi * (b5_H Λ F hF Q (b5_lattice Λ F l) z).re)
  congr 1
  ring

#print axioms b52_summable_norm_inv_factor

end HodgeLean.Foundations.Program
