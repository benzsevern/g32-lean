import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalChart
import Mathlib.Tactic.FieldSimp

/-! # The actual affine chart in the global projective normal model -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified normalized projective chart is continuous for the actual quotient topology. -/
theorem continuous_normalProjectiveChart (k : ℕ) : Continuous (normalProjectiveChart k) := by
  have hc : Continuous (fun z : Fin k → ℂ =>
      (⟨(1, z), by intro h; exact one_ne_zero (congrArg (fun v : ℂ × (Fin k → ℂ) => v.1) h)⟩ :
        {v : ℂ × (Fin k → ℂ) // v ≠ 0})) :=
    (continuous_const.prodMk continuous_id).subtype_mk _
  exact isQuotientMap_quotient_mk'.continuous.comp hc

#print axioms continuous_normalProjectiveChart

/-- Affine coordinates of a homogeneous normal vector in the first projective chart. -/
def homogeneousNormalChartCoordinate (k : ℕ) (v : ℂ × (Fin k → ℂ)) : Fin k → ℂ :=
  v.1⁻¹ • v.2

/-- The affine coordinate formula is unchanged by every nonzero homogeneous rescaling. -/
theorem homogeneousNormalChartCoordinate_smul (k : ℕ) (v : ℂ × (Fin k → ℂ))
    (a : ℂ) (ha : a ≠ 0) :
    homogeneousNormalChartCoordinate k (a • v) = homogeneousNormalChartCoordinate k v := by
  funext j
  simp [homogeneousNormalChartCoordinate, smul_eq_mul, mul_inv_rev, mul_assoc, ha]

#print axioms homogeneousNormalChartCoordinate_smul

/-- The actual affine coordinate function descended to projective lines. -/
def normalProjectiveAffineCoordinate (k : ℕ)
    (p : Projectivization ℂ (ℂ × (Fin k → ℂ))) : Fin k → ℂ :=
  Projectivization.lift (fun v => homogeneousNormalChartCoordinate k v.1)
    (by
      intro v w a ha
      have ha0 : a ≠ 0 := by
        intro hzero
        apply v.2
        rw [ha, hzero, zero_smul]
      rw [ha]
      exact homogeneousNormalChartCoordinate_smul k w.1 a ha0) p

/-- Descended affine coordinates agree with the actual homogeneous formula. -/
theorem normalProjectiveAffineCoordinate_mk (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    normalProjectiveAffineCoordinate k (Projectivization.mk ℂ v hv) =
      homogeneousNormalChartCoordinate k v := by
  rfl

#print axioms normalProjectiveAffineCoordinate_mk

/-- The affine coordinate map is the exact inverse on the specified normalized chart. -/
theorem normalProjectiveAffineCoordinate_chart (k : ℕ) (z : Fin k → ℂ) :
    normalProjectiveAffineCoordinate k (normalProjectiveChart k z) = z := by
  unfold normalProjectiveChart
  rw [normalProjectiveAffineCoordinate_mk]
  simp [homogeneousNormalChartCoordinate]

#print axioms normalProjectiveAffineCoordinate_chart

/-- The first chart consists exactly of the lines with nonzero leading homogeneous coordinate. -/
theorem normalProjectiveChart_range_mk (k : ℕ) (v : ℂ × (Fin k → ℂ)) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ Set.range (normalProjectiveChart k) ↔ v.1 ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    unfold normalProjectiveChart at hz
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hz
    have hh := congrArg (fun w : ℂ × (Fin k → ℂ) => w.1) ha
    change a * v.1 = 1 at hh
    intro hzero
    rw [hzero, mul_zero] at hh
    exact zero_ne_one hh
  · intro hv0
    refine ⟨v.1⁻¹ • v.2, ?_⟩
    unfold normalProjectiveChart
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨v.1⁻¹, ?_⟩
    apply Prod.ext
    · change v.1⁻¹ * v.1 = 1
      exact inv_mul_cancel₀ hv0
    · rfl

#print axioms normalProjectiveChart_range_mk

/-- The specified affine chart image is open in the actual projective quotient topology. -/
theorem isOpen_normalProjectiveChart_range (k : ℕ) : IsOpen (Set.range (normalProjectiveChart k)) := by
  change IsOpen ((fun v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} =>
    Projectivization.mk ℂ v.1 v.2) ⁻¹' Set.range (normalProjectiveChart k))
  have he : (fun v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} =>
      Projectivization.mk ℂ v.1 v.2) ⁻¹' Set.range (normalProjectiveChart k) =
      {v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} | v.1.1 ≠ 0} := by
    ext v
    exact normalProjectiveChart_range_mk k v.1 v.2
  rw [he]
  exact isOpen_ne.preimage (continuous_fst.comp continuous_subtype_val)

#print axioms isOpen_normalProjectiveChart_range

/-- The inverse affine coordinates are continuous on the actual open projective chart. -/
theorem continuous_normalProjectiveAffineCoordinate_on_chart (k : ℕ) :
    Continuous (fun p : Set.range (normalProjectiveChart k) => normalProjectiveAffineCoordinate k p.1) := by
  let π : {v : ℂ × (Fin k → ℂ) // v ≠ 0} → Projectivization ℂ (ℂ × (Fin k → ℂ)) :=
    fun v => Projectivization.mk ℂ v.1 v.2
  have hπ : Topology.IsQuotientMap π := isQuotientMap_quotient_mk'
  apply (hπ.restrictPreimage_isOpen (isOpen_normalProjectiveChart_range k)).continuous_iff.mpr
  let D := {v : {v : ℂ × (Fin k → ℂ) // v ≠ 0} // π v ∈ Set.range (normalProjectiveChart k)}
  change Continuous (fun v : D => v.1.1.1⁻¹ • v.1.1.2)
  have hc : Continuous (fun v : D => v.1.1) := continuous_subtype_val.comp continuous_subtype_val
  have h0 (v : D) : v.1.1.1 ≠ 0 :=
    (normalProjectiveChart_range_mk k v.1.1 v.1.2).mp v.2
  exact ((continuous_fst.comp hc).inv₀ h0).smul (continuous_snd.comp hc)

#print axioms continuous_normalProjectiveAffineCoordinate_on_chart

/-- The actual affine normal chart as a homeomorphism onto its open projective image. -/
def normalProjectiveChartHomeomorph (k : ℕ) :
    (Fin k → ℂ) ≃ₜ Set.range (normalProjectiveChart k) where
  toFun z := ⟨normalProjectiveChart k z, ⟨z, rfl⟩⟩
  invFun p := normalProjectiveAffineCoordinate k p.1
  left_inv := normalProjectiveAffineCoordinate_chart k
  right_inv p := by
    rcases p with ⟨p, ⟨z, rfl⟩⟩
    apply Subtype.ext
    exact congrArg (normalProjectiveChart k) (normalProjectiveAffineCoordinate_chart k z)
  continuous_toFun := (continuous_normalProjectiveChart k).subtype_mk (fun z => ⟨z, rfl⟩)
  continuous_invFun := continuous_normalProjectiveAffineCoordinate_on_chart k

#print axioms normalProjectiveChartHomeomorph
/-- The specified affine base chart retains precisely the distinguished projective zero. -/
theorem normalProjectiveChart_eq_base_iff (k : ℕ) (z : Fin k → ℂ) :
    normalProjectiveChart k z = normalProjectiveBase k ↔ z = 0 := by
  have h0 : normalProjectiveBase k = normalProjectiveChart k 0 := rfl
  rw [h0]
  constructor
  · intro h
    have hh := congrArg (normalProjectiveAffineCoordinate k) h
    simpa only [normalProjectiveAffineCoordinate_chart] using hh
  · rintro rfl
    rfl

#print axioms normalProjectiveChart_eq_base_iff
end HodgeLean.Foundations.Program.G32Native.EulerModel
