import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! Explicit coordinates for bands between continuous sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Normalize a band between two ordered continuous sections to the unit open interval.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, band cells in the CAD construction. -/
def s2v_t11b_bandHomeomorph {X : Type*} [TopologicalSpace X]
    (l u : X → ℝ) (hl : Continuous l) (hu : Continuous u) (hlu : ∀ x, l x < u x) :
    {z : X × ℝ | l z.1 < z.2 ∧ z.2 < u z.1} ≃ₜ (X × Set.Ioo (0 : ℝ) 1) where
  toFun z := (z.val.1, ⟨(z.val.2 - l z.val.1) / (u z.val.1 - l z.val.1), by
    have h := sub_pos.mpr (hlu z.val.1)
    exact ⟨div_pos (sub_pos.mpr z.property.1) h,
      (div_lt_one h).mpr (sub_lt_sub_right z.property.2 _)⟩⟩)
  invFun z := ⟨(z.1, l z.1 + z.2.val * (u z.1 - l z.1)), by
    have h := sub_pos.mpr (hlu z.1)
    constructor
    · nlinarith [mul_pos z.2.property.1 h]
    · nlinarith [mul_lt_mul_of_pos_right z.2.property.2 h]⟩
  left_inv z := by
    apply Subtype.ext
    refine Prod.ext (by rfl) ?_
    dsimp
    have h := ne_of_gt (sub_pos.mpr (hlu z.val.1))
    field_simp [h]
    <;> ring
  right_inv z := by
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    dsimp
    have h := ne_of_gt (sub_pos.mpr (hlu z.1))
    field_simp [h]
    <;> ring
  continuous_toFun := by
    apply Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
    apply Continuous.subtype_mk
    exact ((continuous_snd.comp continuous_subtype_val).sub
      (hl.comp (continuous_fst.comp continuous_subtype_val))).div
      ((hu.comp (continuous_fst.comp continuous_subtype_val)).sub
        (hl.comp (continuous_fst.comp continuous_subtype_val)))
      (fun z => ne_of_gt (sub_pos.mpr (hlu z.val.1)))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk ((hl.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).mul
        ((hu.comp continuous_fst).sub (hl.comp continuous_fst))))

/-- The affine normalization also gives one ambient map across both boundary sections.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, two-section cylindrical coordinates. -/
def s2v_t11b_ambientBandHomeomorph {X : Type*} [TopologicalSpace X]
    (l u : X → ℝ) (hl : Continuous l) (hu : Continuous u) (hlu : ∀ x, l x < u x) :
    (X × ℝ) ≃ₜ (X × ℝ) where
  toFun z := (z.1, (z.2 - l z.1) / (u z.1 - l z.1))
  invFun z := (z.1, l z.1 + z.2 * (u z.1 - l z.1))
  left_inv z := by
    refine Prod.ext (by rfl) ?_
    dsimp
    have h := ne_of_gt (sub_pos.mpr (hlu z.1))
    field_simp [h]
    <;> ring
  right_inv z := by
    refine Prod.ext (by rfl) ?_
    dsimp
    have h := ne_of_gt (sub_pos.mpr (hlu z.1))
    field_simp [h]
    <;> ring
  continuous_toFun := continuous_fst.prodMk
    ((continuous_snd.sub (hl.comp continuous_fst)).div
      ((hu.comp continuous_fst).sub (hl.comp continuous_fst))
      (fun z => ne_of_gt (sub_pos.mpr (hlu z.1))))
  continuous_invFun := continuous_fst.prodMk
    ((hl.comp continuous_fst).add (continuous_snd.mul
      ((hu.comp continuous_fst).sub (hl.comp continuous_fst))))

/-- The same ambient map preserves the base and sends the two sections to zero and one.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, two-section cylindrical coordinates. -/
theorem s2v_t11b_ambientBandHomeomorph_sections {X : Type*} [TopologicalSpace X]
    (l u : X → ℝ) (hl : Continuous l) (hu : Continuous u) (hlu : ∀ x, l x < u x) :
    (∀ z, (s2v_t11b_ambientBandHomeomorph l u hl hu hlu z).1 = z.1) ∧
      (∀ x, s2v_t11b_ambientBandHomeomorph l u hl hu hlu (x, l x) = (x, 0)) ∧
      (∀ x, s2v_t11b_ambientBandHomeomorph l u hl hu hlu (x, u x) = (x, 1)) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro x
    change (x, (l x - l x) / (u x - l x)) = (x, 0)
    rw [sub_self, zero_div]
  · intro x
    change (x, (u x - l x) / (u x - l x)) = (x, 1)
    rw [div_self (ne_of_gt (sub_pos.mpr (hlu x)))]

end HodgeLean.Foundations.Program
