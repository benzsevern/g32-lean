import HodgeLean.Foundations.Program.PrymParabolicIntersectionReflection

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

/-- A deformation from conjugation to the centred finite wedge coordinates.
Source: the barycentric formula `hg5_wedge`. -/
def hga_wedgeDeformation (u v t : ℝ) (z : ℂ) : ℂ :=
  (((1 - t + t * (v - u)) * z.re -
      t * (u + 11 / 2) * |t * z.re + (1 + t) * z.im| : ℝ) : ℂ) +
    ((-(1 + 9 * t) * (t * z.re + (1 + t) * z.im) : ℝ) : ℂ) * Complex.I

theorem hga_wedgeDeformation_eq_zero (u v : ℝ) (huv : u < v)
    (t : unitInterval) (z : ℂ) : hga_wedgeDeformation u v t z = 0 ↔ z = 0 := by
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  have ha : 0 < 1 - (t : ℝ) + (t : ℝ) * (v - u) := by
    by_cases h : (t : ℝ) = 0
    · simp [h]
    · have ht : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm h)
      nlinarith [mul_pos ht (sub_pos.mpr huv)]
  have hb : 0 < 1 + 9 * (t : ℝ) := by linarith
  have hc : 0 < 1 + (t : ℝ) := by linarith
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [hga_wedgeDeformation, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_add, sub_zero, add_zero, Complex.zero_re,
      Complex.add_im, Complex.mul_im, mul_one, Complex.zero_im] at hr hi
    have hs : (t : ℝ) * z.re + (1 + (t : ℝ)) * z.im = 0 :=
      (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr hb.ne')
    rw [hs, abs_zero, mul_zero, sub_zero] at hr
    have hzre : z.re = 0 := (mul_eq_zero.mp hr).resolve_left ha.ne'
    rw [hzre, mul_zero, zero_add] at hs
    exact Complex.ext hzre ((mul_eq_zero.mp hs).resolve_left hc.ne')
  · rintro rfl
    simp [hga_wedgeDeformation]

theorem hga_continuous_wedgeDeformation (u v : ℝ) :
    Continuous (fun p : ℝ × ℂ ↦ hga_wedgeDeformation u v p.1 p.2) := by
  unfold hga_wedgeDeformation
  fun_prop

/-- The centred wedge deformation on punctured complex coordinates.
Source: `hga_wedgeDeformation_eq_zero`. -/
def hga_wedgePairMap (u v : ℝ) (huv : u < v) (t : unitInterval) :
    puncturedPair ℂ 1 ⟶ puncturedPair ℂ 1 :=
  hga_complexScalarPairMap
    ⟨hga_wedgeDeformation u v t,
      hga_continuous_wedgeDeformation u v |>.comp (continuous_const.prodMk continuous_id)⟩
    (fun z hz h ↦ hz ((hga_wedgeDeformation_eq_zero u v huv t z).mp h))

set_option backward.isDefEq.respectTransparency false in
/-- The wedge coordinates are homotopic to conjugation through punctured maps.
Source: `hga_wedgeDeformation_eq_zero`. -/
def hga_wedgePairHomotopy (u v : ℝ) (huv : u < v) :
    TopPair.Homotopy hga_complexConjPairMap (hga_wedgePairMap u v huv 1) where
  fst :=
    { toFun := fun p i ↦ hga_wedgeDeformation u v (p.1 : ℝ) (p.2 i)
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact (hga_continuous_wedgeDeformation u v).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            ((continuous_apply i).comp continuous_snd))
      map_zero_left := fun z ↦ by
        funext i
        change hga_wedgeDeformation u v 0 (z i) = star (z i)
        apply Complex.ext <;> simp [hga_wedgeDeformation]
      map_one_left := fun z ↦ rfl }
  snd :=
    { toFun := fun p ↦ ⟨fun i ↦ hga_wedgeDeformation u v (p.1 : ℝ) (p.2.1 i), by
        intro h
        apply p.2.2
        funext i
        exact (hga_wedgeDeformation_eq_zero u v huv p.1 (p.2.1 i)).mp (congrFun h i)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        exact (hga_continuous_wedgeDeformation u v).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk
            ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        funext i
        change hga_wedgeDeformation u v 0 (z.1 i) = star (z.1 i)
        apply Complex.ext <;> simp [hga_wedgeDeformation]
      map_one_left := fun z ↦ rfl }
  w := rfl

theorem hga_wedgePairMap_standardLocalClass (u v : ℝ) (huv : u < v) :
    relativeHomologyMap ℤ 2 (hga_wedgePairMap u v huv 1)
      (standardComplexLocalClass ℤ 1) = -standardComplexLocalClass ℤ 1 := by
  rw [← (hga_wedgePairHomotopy u v huv).relativeHomologyMap_apply_eq (R := ℤ)
    2 (standardComplexLocalClass ℤ 1)]
  exact hga_complexConj_standardLocalClass

open scoped Topology in
theorem hga_triangleRetraction_eventually_weights :
    ∀ᶠ w : ℂ in 𝓝 0, ∀ i : Fin 3, (hga_triangleRetraction w).weights i =
      (![(1 : ℝ) / 3 - w.re - w.im, 1 / 3 + w.re, 1 / 3 + w.im] : Fin 3 → ℝ) i := by
  have hc0 : Continuous (fun w : ℂ ↦ (1 : ℝ) / 3 - w.re - w.im) := by fun_prop
  have hc1 : Continuous (fun w : ℂ ↦ (1 : ℝ) / 3 + w.re) := by fun_prop
  have hc2 : Continuous (fun w : ℂ ↦ (1 : ℝ) / 3 + w.im) := by fun_prop
  have h0 := (isOpen_lt continuous_const hc0).mem_nhds
    (show (0 : ℝ) < (1 : ℝ) / 3 - (0 : ℂ).re - (0 : ℂ).im by norm_num)
  have h1 := (isOpen_lt continuous_const hc1).mem_nhds
    (show (0 : ℝ) < (1 : ℝ) / 3 + (0 : ℂ).re by norm_num)
  have h2 := (isOpen_lt continuous_const hc2).mem_nhds
    (show (0 : ℝ) < (1 : ℝ) / 3 + (0 : ℂ).im by norm_num)
  filter_upwards [h0, h1, h2] with w hw0 hw1 hw2
  let v : Fin 3 → ℝ := ![(1 : ℝ) / 3 - w.re - w.im, 1 / 3 + w.re, 1 / 3 + w.im]
  have hv : ∑ i, v i = 1 := by simp [v, Fin.sum_univ_three] <;> ring
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    fin_cases i
    · exact hw0.le
    · exact hw1.le
    · exact hw2.le
  exact fun i ↦ hga_normalize_barycentric_nonnegative v hv hv0 i

open scoped Topology in
theorem hga_wedgeExtension_eventually (u v : ℝ) :
    ∀ᶠ w : ℂ in 𝓝 0, hga_triangleExtension (hg5_wedge u v) w =
      hga_wedgeDeformation u v 1 w +
        hg5_wedge u v (hga_triangleRetraction 0) := by
  filter_upwards [hga_triangleRetraction_eventually_weights] with w hw
  apply Complex.ext <;>
    simp [hga_triangleExtension, hg5_wedge, hga_wedgeDeformation, hw,
      hga_triangleRetraction_zero_weights] <;> ring
  rw [show -w.re - w.im * 2 = -(w.re + w.im * 2) by ring, abs_neg]
  ring

set_option backward.isDefEq.respectTransparency false in
open scoped Topology in
theorem hga_wedgeExtension_localClass (u v : ℝ) (huv : u < v) :
    relativeHomologyMap ℤ 2
      (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap (hg5_wedge u v)
        (hg5_wedge_injective u v huv.ne) (hga_triangleRetraction 0)
        hga_triangleRetraction_zero_weights)
      (standardComplexLocalClass ℤ 1) =
    -relativeHomologyMap ℤ 2
      (hga_complexLinePairIso.hom ≫ translationPointComplementPairMap ℂ
        (hg5_wedge u v (hga_triangleRetraction 0)))
      (standardComplexLocalClass ℤ 1) := by
  let N := hga_complexLinePairIso.hom ≫ translationPointComplementPairMap ℂ
    (hg5_wedge u v (hga_triangleRetraction 0))
  have hm : relativeHomologyMap ℤ 2
      (hga_complexLinePairIso.hom ≫ hga_triangleExtension_pairMap (hg5_wedge u v)
        (hg5_wedge_injective u v huv.ne) (hga_triangleRetraction 0)
        hga_triangleRetraction_zero_weights) =
      relativeHomologyMap ℤ 2 (hga_wedgePairMap u v huv 1 ≫ N) := by
    apply hga_local_maps_eq_of_eventuallyEq ℤ _ 1 2
    have he := ((continuous_apply (0 : Fin 1)).tendsto (0 : Fin 1 → ℂ)).eventually
      (hga_wedgeExtension_eventually u v)
    filter_upwards [he] with z hz
    change hga_triangleExtension (hg5_wedge u v) (z 0) =
      hga_wedgeDeformation u v 1 (z 0) + hg5_wedge u v (hga_triangleRetraction 0)
    exact hz
  rw [hm, relativeHomologyMap_comp, LinearMap.comp_apply,
    hga_wedgePairMap_standardLocalClass, map_neg]

#print axioms hga_wedgeExtension_localClass

#print axioms hga_wedgeExtension_eventually

#print axioms hga_triangleRetraction_eventually_weights

#print axioms hga_wedgePairMap_standardLocalClass

#print axioms hga_wedgePairMap
#print axioms hga_wedgePairHomotopy

#print axioms hga_continuous_wedgeDeformation

#print axioms hga_wedgeDeformation
#print axioms hga_wedgeDeformation_eq_zero
end HodgeLean.Foundations.Program
