import HodgeLean.Foundations.Program.SchoenTowerT11bKink

/-! Ambient coordinates joining variable-slope affine half-lines continuously.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Continuous positive slopes give ambient product coordinates fixing the lower half-line.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
def s2v_t11b_halfLineCoordinates {X : Type*} [TopologicalSpace X]
    (a : ℝ) (c : X → ℝ) (hc : Continuous c) (hpositive : ∀ x, 0 < c x) :
    (X × ℝ) ≃ₜ (X × ℝ) where
  toFun z := (z.1, s2v_t11b_positiveKink a (c z.1) z.2)
  invFun z := (z.1, s2v_t11b_positiveKink a (c z.1)⁻¹ z.2)
  left_inv z := Prod.ext rfl (s2v_t11b_positiveKink_left_inv a (c z.1) (hpositive z.1) z.2)
  right_inv z := by
    refine Prod.ext (by rfl) ?_
    simpa only [inv_inv] using
      s2v_t11b_positiveKink_left_inv a (c z.1)⁻¹ (inv_pos.mpr (hpositive z.1)) z.2
  continuous_toFun := continuous_fst.prodMk ((s2v_t11b_positiveKink_continuous a).comp
    ((hc.comp continuous_fst).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk ((s2v_t11b_positiveKink_continuous a).comp
    (((hc.inv₀ (fun x => ne_of_gt (hpositive x))).comp continuous_fst).prodMk continuous_snd))

/-- Normalize a continuous section above a fixed boundary while fixing the lower half-line.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
def s2v_t11b_upperSectionCoordinates {X : Type*} [TopologicalSpace X]
    (a : ℝ) (u : X → ℝ) (hu : Continuous u) (hau : ∀ x, a < u x) :
    (X × ℝ) ≃ₜ (X × ℝ) :=
  s2v_t11b_halfLineCoordinates a (fun x => (u x - a)⁻¹)
    ((hu.sub continuous_const).inv₀ (fun x => ne_of_gt (sub_pos.mpr (hau x))))
    (fun x => inv_pos.mpr (sub_pos.mpr (hau x)))

/-- Upper-section normalization preserves the base, fixes lower points, normalizes the section and preserves order.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, compatible band-coordinate step. -/
theorem s2v_t11b_upperSectionCoordinates_spec {X : Type*} [TopologicalSpace X]
    (a : ℝ) (u : X → ℝ) (hu : Continuous u) (hau : ∀ x, a < u x) :
    (∀ z, (s2v_t11b_upperSectionCoordinates a u hu hau z).1 = z.1) ∧
      (∀ b x, x ≤ a → s2v_t11b_upperSectionCoordinates a u hu hau (b, x) = (b, x)) ∧
      (∀ b, s2v_t11b_upperSectionCoordinates a u hu hau (b, u b) = (b, a + 1)) ∧
      ∀ b, StrictMono (fun x => (s2v_t11b_upperSectionCoordinates a u hu hau (b, x)).2) := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro b x hx
    refine Prod.ext (by rfl) ?_
    exact s2v_t11b_positiveKink_of_le a (u b - a)⁻¹ x hx
  · intro b
    refine Prod.ext (by rfl) ?_
    change s2v_t11b_positiveKink a (u b - a)⁻¹ (u b) = a + 1
    rw [s2v_t11b_positiveKink_of_ge a (u b - a)⁻¹ (u b) (hau b).le,
      inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr (hau b)))]
  · intro b
    exact s2v_t11b_positiveKink_strictMono a (u b - a)⁻¹
      (inv_pos.mpr (sub_pos.mpr (hau b)))

end HodgeLean.Foundations.Program
