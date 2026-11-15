import HodgeLean.Foundations.Program.SchoenTowerT11bDefs

/-! Fibers and restrictions of product coordinates.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A product chart identifies every fiber with its model fiber.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, fiber identification. -/
def s2v_t11b_fiberHomeomorph {X F B : Type*}
    [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace B]
    (p : X → B) (e : X ≃ₜ F × B) (he : ∀ x, (e x).2 = p x) (b : B) :
    {x : X | p x = b} ≃ₜ F where
  toFun x := (e x.val).1
  invFun a := ⟨e.symm (a, b), by change p (e.symm (a, b)) = b; rw [← he, e.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [Homeomorph.apply_symm_apply]
    exact Prod.ext rfl ((he x.val).trans x.property).symm
  right_inv a := by simp
  continuous_toFun := continuous_fst.comp (e.continuous.comp continuous_subtype_val)
  continuous_invFun := (e.symm.continuous.comp
    (continuous_id.prodMk continuous_const)).subtype_mk _

/-- Restrict product coordinates to any subset of the base.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, restriction of trivializations. -/
def s2v_t11b_restrictProduct {X F B : Type*}
    [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace B]
    (p : X → B) (e : X ≃ₜ F × B) (he : ∀ x, (e x).2 = p x) (U : Set B) :
    {x : X | p x ∈ U} ≃ₜ (F × U) where
  toFun x := ((e x.val).1, ⟨p x.val, x.property⟩)
  invFun z := ⟨e.symm (z.1, z.2.val), by
    change p (e.symm (z.1, z.2.val)) ∈ U
    rw [← he, e.apply_symm_apply]
    exact z.2.property⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [Homeomorph.apply_symm_apply]
    exact Prod.ext rfl (he x.val).symm
  right_inv z := by
    apply Prod.ext
    · simp only [Homeomorph.apply_symm_apply]
    · apply Subtype.ext
      change p (e.symm (z.1, z.2.val)) = z.2.val
      rw [← he, e.apply_symm_apply]
  continuous_toFun :=
    (continuous_fst.comp (e.continuous.comp continuous_subtype_val)).prodMk
      (((e.continuous.snd.congr he).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (e.symm.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- Replace the abstract model of a product chart by a specified actual fiber.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, choice of model fiber. -/
def s2v_t11b_actualFiberProduct {X F B : Type*}
    [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace B]
    (p : X → B) (e : X ≃ₜ F × B) (he : ∀ x, (e x).2 = p x) (b : B) :
    ({x : X | p x = b} × B) ≃ₜ X :=
  ((s2v_t11b_fiberHomeomorph p e he b).prodCongr (Homeomorph.refl B)).trans e.symm

/-- The actual-fiber product chart retains the specified base coordinate.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, commuting projection. -/
theorem s2v_t11b_actualFiberProduct_projection {X F B : Type*}
    [TopologicalSpace X] [TopologicalSpace F] [TopologicalSpace B]
    (p : X → B) (e : X ≃ₜ F × B) (he : ∀ x, (e x).2 = p x) (b : B)
    (z : {x : X | p x = b} × B) :
    p (s2v_t11b_actualFiberProduct p e he b z) = z.2 := by
  change p (e.symm ((e z.1.val).1, z.2)) = z.2
  rw [← he, e.apply_symm_apply]

/-- The radius-r link is an actual fiber of a distance product chart containing r.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, choice of model fiber. -/
def s2v_t11b_linkModel {n : ℕ} {F : Type*} [TopologicalSpace F]
    (S : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (R r : ℝ) (hr : 0 < r) (hrr : r < R)
    (e : {y : EuclideanSpace ℝ (Fin n) | y ∈ S ∧ dist y x ∈ Set.Ioo (0 : ℝ) R}
      ≃ₜ (F × Set.Ioo (0 : ℝ) R))
    (he : ∀ y, (e y).2.val = dist y.val x) :
    s2v_t11b_link S x r ≃ₜ F where
  toFun y := (e ⟨y.val, y.property.1, by rw [y.property.2]; exact ⟨hr, hrr⟩⟩).1
  invFun a := ⟨(e.symm (a, ⟨r, hr, hrr⟩)).val, by
    refine ⟨(e.symm (a, ⟨r, hr, hrr⟩)).property.1, ?_⟩
    change dist (e.symm (a, ⟨r, hr, hrr⟩)).val x = r
    rw [← he, e.apply_symm_apply]⟩
  left_inv y := by
    apply Subtype.ext
    have hy : (e ⟨y.val, y.property.1, by rw [y.property.2]; exact ⟨hr, hrr⟩⟩).2 =
        (⟨r, hr, hrr⟩ : Set.Ioo (0 : ℝ) R) := by
      apply Subtype.ext
      exact (he _).trans y.property.2
    change (e.symm ((e _).1, ⟨r, hr, hrr⟩)).val = y.val
    rw [← hy, Prod.mk.eta, e.symm_apply_apply]
  right_inv a := by
    change (e (e.symm (a, ⟨r, hr, hrr⟩))).1 = a
    rw [e.apply_symm_apply]
  continuous_toFun := continuous_fst.comp (e.continuous.comp
    (continuous_subtype_val.subtype_mk _))
  continuous_invFun := (continuous_subtype_val.comp (e.symm.continuous.comp
    (continuous_id.prodMk continuous_const))).subtype_mk _

/-- Restrict a distance product chart to a smaller positive interval.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.17, restriction of trivializations. -/
def s2v_t11b_smallerInterval {n : ℕ} {F : Type*} [TopologicalSpace F]
    (S : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (R r : ℝ) (hrr : r < R)
    (e : {y : EuclideanSpace ℝ (Fin n) | y ∈ S ∧ dist y x ∈ Set.Ioo (0 : ℝ) R}
      ≃ₜ (F × Set.Ioo (0 : ℝ) R))
    (he : ∀ y, (e y).2.val = dist y.val x) :
    (F × Set.Ioo (0 : ℝ) r) ≃ₜ
      {y : EuclideanSpace ℝ (Fin n) | y ∈ S ∧ dist y x ∈ Set.Ioo (0 : ℝ) r} where
  toFun z := ⟨(e.symm (z.1, ⟨z.2.val, z.2.property.1, z.2.property.2.trans hrr⟩)).val, by
    refine ⟨(e.symm _).property.1, ?_⟩
    rw [← he, e.apply_symm_apply]
    exact z.2.property⟩
  invFun y := ((e ⟨y.val, y.property.1, y.property.2.1,
      y.property.2.2.trans hrr⟩).1, ⟨dist y.val x, y.property.2⟩)
  left_inv z := by
    apply Prod.ext
    · change (e (e.symm (z.1, ⟨z.2.val, z.2.property.1,
        z.2.property.2.trans hrr⟩))).1 = z.1
      rw [e.apply_symm_apply]
    · apply Subtype.ext
      change dist (e.symm _).val x = z.2.val
      rw [← he, e.apply_symm_apply]
  right_inv y := by
    apply Subtype.ext
    have hy : (e ⟨y.val, y.property.1, y.property.2.1,
        y.property.2.2.trans hrr⟩).2 =
        (⟨dist y.val x, y.property.2.1, y.property.2.2.trans hrr⟩ : Set.Ioo (0 : ℝ) R) := by
      apply Subtype.ext
      exact he _
    change (e.symm ((e _).1, _)).val = y.val
    rw [← hy, Prod.mk.eta, e.symm_apply_apply]
  continuous_toFun := (continuous_subtype_val.comp (e.symm.continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))).subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp (e.continuous.comp (continuous_subtype_val.subtype_mk _))).prodMk
      ((continuous_subtype_val.dist continuous_const).subtype_mk _)

/-- Assemble a chart from an actual sphere link and the smaller radius interval.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.17 and 1.19. -/
def s2v_t11b_radialAssembly {n : ℕ} {F : Type*} [TopologicalSpace F]
    (S : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (R r : ℝ) (hr : 0 < r) (hrr : r < R)
    (e : {y : EuclideanSpace ℝ (Fin n) | y ∈ S ∧ dist y x ∈ Set.Ioo (0 : ℝ) R}
      ≃ₜ (F × Set.Ioo (0 : ℝ) R))
    (he : ∀ y, (e y).2.val = dist y.val x) :
    (s2v_t11b_link S x r × Set.Ioo (0 : ℝ) r) ≃ₜ
      {y : EuclideanSpace ℝ (Fin n) | y ∈ S ∧ dist y x ∈ Set.Ioo (0 : ℝ) r} :=
  ((s2v_t11b_linkModel S x R r hr hrr e he).prodCongr
    (Homeomorph.refl _)).trans (s2v_t11b_smallerInterval S x R r hrr e he)

/-- The assembled chart preserves the actual distance coordinate.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.19, radius compatibility. -/
theorem s2v_t11b_radialAssembly_radius {n : ℕ} {F : Type*} [TopologicalSpace F]
    (S : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (R r : ℝ) (hr : 0 < r) (hrr : r < R)
    (e : {y : EuclideanSpace ℝ (Fin n) | y ∈ S ∧ dist y x ∈ Set.Ioo (0 : ℝ) R}
      ≃ₜ (F × Set.Ioo (0 : ℝ) R))
    (he : ∀ y, (e y).2.val = dist y.val x)
    (z : s2v_t11b_link S x r × Set.Ioo (0 : ℝ) r) :
    dist (s2v_t11b_radialAssembly S x R r hr hrr e he z).val x = z.2.val := by
  change dist (e.symm (_, ⟨z.2.val, z.2.property.1, z.2.property.2.trans hrr⟩)).val x = z.2.val
  rw [← he, e.apply_symm_apply]

end HodgeLean.Foundations.Program
