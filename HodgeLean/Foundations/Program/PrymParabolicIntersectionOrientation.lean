import HodgeLean.Foundations.Program.PrymParabolicIntersectionHomology
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceFundamentalClass

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

/-- Linear part of the wedge in coordinates `(a₁,a₂)` on the region `a₀ ≥ a₂`.
Source: `hg5_wedge`, G32 v0.16, Figure 1. -/
def hga_wedgeUpperMatrix (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v + 11 / 2, 2 * u + 11; -10, -20]

/-- Linear part of the wedge in coordinates `(a₁,a₂)` on the region `a₀ ≤ a₂`.
Source: `hg5_wedge`, G32 v0.16, Figure 1. -/
def hga_wedgeLowerMatrix (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v - 2 * u - 11 / 2, -2 * u - 11; -10, -20]

theorem hga_wedgeUpperMatrix_det (u v : ℝ) :
    (hga_wedgeUpperMatrix u v).det = -20 * (v - u) := by
  rw [Matrix.det_fin_two]
  change (v + 11 / 2) * (-20) - (2 * u + 11) * (-10) = _
  ring

theorem hga_wedgeLowerMatrix_det (u v : ℝ) :
    (hga_wedgeLowerMatrix u v).det = -20 * (v - u) := by
  rw [Matrix.det_fin_two]
  change (v - 2 * u - 11 / 2) * (-20) - (-2 * u - 11) * (-10) = _
  ring

theorem hga_wedge_upper_coords (u v : ℝ) (a : StdSimplex ℝ (Fin 3))
    (ha : a.weights 2 ≤ a.weights 0) :
    (hg5_wedge u v a).re = -11 / 2 + (v + 11 / 2) * a.weights 1 +
      (2 * u + 11) * a.weights 2 ∧
    (hg5_wedge u v a).im = 10 - 10 * a.weights 1 - 20 * a.weights 2 := by
  have hw := hg5_sum3 a
  simp only [hg5_wedge_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add, add_zero, abs_of_nonneg (sub_nonneg.mpr ha)]
  constructor
  · linear_combination -(u + 11 / 2) * hw
  · linarith

theorem hga_wedge_lower_coords (u v : ℝ) (a : StdSimplex ℝ (Fin 3))
    (ha : a.weights 0 ≤ a.weights 2) :
    (hg5_wedge u v a).re = 2 * u + 11 / 2 + (v - 2 * u - 11 / 2) * a.weights 1 -
      (2 * u + 11) * a.weights 2 ∧
    (hg5_wedge u v a).im = 10 - 10 * a.weights 1 - 20 * a.weights 2 := by
  have hw := hg5_sum3 a
  simp only [hg5_wedge_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add, add_zero, abs_of_nonpos (sub_nonpos.mpr ha)]
  constructor
  · linear_combination (u + 11 / 2) * hw
  · linarith

theorem hga_wedgeUpperMatrix_det_neg (u v : ℝ) (h : u < v) :
    (hga_wedgeUpperMatrix u v).det < 0 := by
  rw [hga_wedgeUpperMatrix_det]
  nlinarith

theorem hga_wedgeLowerMatrix_det_neg (u v : ℝ) (h : u < v) :
    (hga_wedgeLowerMatrix u v).det < 0 := by
  rw [hga_wedgeLowerMatrix_det]
  nlinarith

theorem hga_finite_A_determinants_neg (i : Fin 13) (hi : i.val < 12) :
    (hga_wedgeUpperMatrix (hg3_waist i) (hg5_markRe ⟨i.val, hi⟩)).det < 0 ∧
      (hga_wedgeLowerMatrix (hg3_waist i) (hg5_markRe ⟨i.val, hi⟩)).det < 0 := by
  exact ⟨hga_wedgeUpperMatrix_det_neg _ _ (hg5_waist_lt_mark_self i hi),
    hga_wedgeLowerMatrix_det_neg _ _ (hg5_waist_lt_mark_self i hi)⟩

theorem hga_finite_B_determinants_pos (i : Fin 13) (hi : i.val < 12) :
    0 < (hga_wedgeUpperMatrix (hg3_waist (finRotate 13 i)) (hg5_markRe ⟨i.val, hi⟩)).det ∧
      0 < (hga_wedgeLowerMatrix (hg3_waist (finRotate 13 i)) (hg5_markRe ⟨i.val, hi⟩)).det := by
  have h : hg5_markRe ⟨i.val, hi⟩ < hg3_waist (finRotate 13 i) := by
    rw [hg5_waist_succ i hi]
    exact hg5_mark_lt_waist_succ i hi
  rw [hga_wedgeUpperMatrix_det, hga_wedgeLowerMatrix_det]
  constructor <;> nlinarith

theorem hga_complex_basis_coordinate (z : ℂ) (i : Fin (Module.finrank ℂ ℂ)) :
    (Module.finBasis ℂ ℂ).equivFun z i =
      z * (Module.finBasis ℂ ℂ).equivFun 1 i := by
  have h := LinearEquiv.map_smul (Module.finBasis ℂ ℂ).equivFun z (1 : ℂ)
  simpa only [smul_eq_mul, Pi.smul_apply, mul_one] using congrFun h i

theorem hga_b3_orient_one_I : b3_orient ℂ 1 Complex.I =
    ∑ i, Complex.normSq ((Module.finBasis ℂ ℂ).equivFun 1 i) := by
  unfold b3_orient
  apply Finset.sum_congr rfl
  intro i _
  rw [hga_complex_basis_coordinate Complex.I i]
  simp only [starRingEnd_apply]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, zero_mul, one_mul, zero_add, zero_sub,
    Complex.normSq_apply, Complex.star_def]
  ring

theorem hga_b3_orient_one_I_pos : 0 < b3_orient ℂ 1 Complex.I := by
  rw [hga_b3_orient_one_I]
  have hn : (Module.finBasis ℂ ℂ).equivFun (1 : ℂ) ≠ 0 := by
    intro h
    have hz := (Module.finBasis ℂ ℂ).equivFun.injective
      (h.trans (map_zero (Module.finBasis ℂ ℂ).equivFun).symm)
    exact one_ne_zero hz
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  exact Finset.sum_pos' (fun j _ ↦ Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

theorem hga_b3_orient_complex (v w : ℂ) :
    b3_orient ℂ v w = b3_orient ℂ 1 Complex.I * (star v * w).im := by
  rw [hga_b3_orient_one_I, Finset.sum_mul]
  unfold b3_orient
  apply Finset.sum_congr rfl
  intro i _
  rw [hga_complex_basis_coordinate v i, hga_complex_basis_coordinate w i]
  simp only [starRingEnd_apply]
  simp only [Complex.star_def, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem hga_affine_triangle_injective {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (e : T → ℂ) (z : ℂ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hσ : ∀ a, e (σ a) = z + (ρ : ℂ) *
      (((a.weights 1 : ℝ) : ℂ) + ((a.weights 2 : ℝ) : ℂ) * Complex.I)) :
    Function.Injective σ := by
  intro a b hab
  have he : e (σ a) = e (σ b) := congrArg e hab
  rw [hσ a, hσ b] at he
  have hcoords := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hρ) (add_left_cancel he)
  have h1 := congrArg Complex.re hcoords
  have h2 := congrArg Complex.im hcoords
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h1
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at h2
  have ha := hg5_sum3 a
  have hb := hg5_sum3 b
  apply hg5_simplex_ext <;> linarith

open scoped Manifold ContDiff in
theorem hga_fundClass_sign_dichotomy {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] [T2Space T] [CompactSpace T] [ConnectedSpace T]
    [IsManifold 𝓘(ℂ, ℂ) 1 T] (F : hg8_DeltaMap b4b_root T)
    (he : ∃ e : Homology ℤ (TopCat.of T) 2 ≃ₗ[ℤ] ℤ, e (hga_fundClass F) = 1) :
    ∃ w : Homology ℤ (TopCat.of T) 2,
      (∀ x : T, (relativeHomologyProjection ℤ (pointComplementPair x) 2).hom w =
        b6m_surfaceLocalClass ℤ x) ∧ (hga_fundClass F = w ∨ hga_fundClass F = -w) := by
  obtain ⟨e, he⟩ := he
  obtain ⟨w, hw, hgen⟩ := b6m_surface_fundamental_generator ℤ (C := T)
  have hv : Function.Surjective (fun n : ℤ ↦ n • w) := by
    intro z
    obtain ⟨n, hn⟩ := hgen.2 z
    refine ⟨n, ?_⟩
    exact (int_smul_eq_zsmul (ModuleCat.isModule (Homology ℤ (TopCat.of T) 2)) n w).symm.trans hn
  exact ⟨w, hw, hga_generator_eq_or_neg e _ w he hv⟩

open scoped Manifold ContDiff in
set_option backward.isDefEq.respectTransparency false in
theorem hga_global_orientation_of_one_local_value {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] [T2Space T] [CompactSpace T] [ConnectedSpace T]
    [IsManifold 𝓘(ℂ, ℂ) 1 T] (F : hg8_DeltaMap b4b_root T)
    (he : ∃ e : Homology ℤ (TopCat.of T) 2 ≃ₗ[ℤ] ℤ, e (hga_fundClass F) = 1)
    (y : T) (hy : (relativeHomologyProjection ℤ (pointComplementPair y) 2).hom
      (hga_fundClass F) = -b6m_surfaceLocalClass ℤ y) :
    ∀ x : T, (relativeHomologyProjection ℤ (pointComplementPair x) 2).hom
      (hga_fundClass F) = -b6m_surfaceLocalClass ℤ x := by
  obtain ⟨w, hw, hsign⟩ := hga_fundClass_sign_dichotomy F he
  rcases hsign with hc | hc
  · rw [hc, hw y] at hy
    have hi := (b6m_surfaceLocalClass_smul_bijective ℤ y).1
    have hn : (1 : ℤ) = -1 := hi (by
      simpa only [one_smul, neg_smul, one_zsmul, neg_one_zsmul] using hy)
    norm_num at hn
  · intro x
    rw [hc]
    exact (map_neg _ w).trans (congrArg Neg.neg (hw x))

open scoped Manifold ContDiff in
set_option backward.isDefEq.respectTransparency false in
theorem hga_surface_class_of_one_local_value {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] [T2Space T] [CompactSpace T] [ConnectedSpace T]
    [IsManifold 𝓘(ℂ, ℂ) 1 T] (c : Homology ℤ (TopCat.of T) 2) (r : ℤ)
    (y : T) (hy : (relativeHomologyProjection ℤ (pointComplementPair y) 2).hom c =
      r • b6m_surfaceLocalClass ℤ y) :
    ∀ x : T, (relativeHomologyProjection ℤ (pointComplementPair x) 2).hom c =
      r • b6m_surfaceLocalClass ℤ x := by
  obtain ⟨w, hw, hgen⟩ := b6m_surface_fundamental_generator ℤ (C := T)
  obtain ⟨n, rfl⟩ := hgen.2 c
  erw [LinearMap.map_smul, hw] at hy
  have hn : n = r := (b6m_surfaceLocalClass_smul_bijective ℤ y).1 (by
    convert hy using 1 <;> exact int_smul_eq_zsmul _ _ _)
  intro x
  erw [LinearMap.map_smul, hw]
  rw [hn]
  exact int_smul_eq_zsmul _ _ _

#print axioms hga_surface_class_of_one_local_value

#print axioms hga_wedgeUpperMatrix_det
#print axioms hga_wedgeLowerMatrix_det
#print axioms hga_wedge_upper_coords
#print axioms hga_wedge_lower_coords
#print axioms hga_wedgeUpperMatrix_det_neg
#print axioms hga_wedgeLowerMatrix_det_neg
#print axioms hga_finite_A_determinants_neg
#print axioms hga_finite_B_determinants_pos
#print axioms hga_complex_basis_coordinate
#print axioms hga_b3_orient_one_I
#print axioms hga_b3_orient_one_I_pos
#print axioms hga_b3_orient_complex
#print axioms hga_affine_triangle_injective
#print axioms hga_fundClass_sign_dichotomy
#print axioms hga_global_orientation_of_one_local_value

end HodgeLean.Foundations.Program
