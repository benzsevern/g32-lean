import HodgeLean.Foundations.Program.G32Native.EulerModel.GlobalNormalDerivative
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Other.AlgebraicTopology.Singular.Cohomology

/-! # A punctured homotopy for the normalized section coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The positive real interpolation between the constant and Hermitian chart factors. -/
def normalChartScale (k : ℕ) (t : unitInterval) (z : Fin k → ℂ) : ℝ :=
  (1 - t.val) + t.val * (normalLengthSq k (1, z))⁻¹

/-- Every intermediate chart factor is strictly positive, including both endpoints. -/
theorem normalChartScale_pos (k : ℕ) (t : unitInterval) (z : Fin k → ℂ) :
    0 < normalChartScale k t z := by
  have hN : 0 < normalLengthSq k (1, z) := normalLengthSq_pos k _ (by
    intro h
    exact one_ne_zero (congrArg (fun v : ℂ × (Fin k → ℂ) => v.1) h))
  by_cases ht : t.val = 0
  · simp [normalChartScale, ht]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2)
      (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) (inv_pos.mpr hN))

#print axioms normalChartScale_pos

/-- The positive chart factor is jointly continuous in the interpolation and normal coordinates. -/
theorem continuous_normalChartScale (k : ℕ) :
    Continuous (fun tz : unitInterval × (Fin k → ℂ) => normalChartScale k tz.1 tz.2) := by
  have hN : Continuous (fun tz : unitInterval × (Fin k → ℂ) => normalLengthSq k (1, tz.2)) := by
    unfold normalLengthSq
    fun_prop
  have hn (tz : unitInterval × (Fin k → ℂ)) : normalLengthSq k (1, tz.2) ≠ 0 :=
    ne_of_gt (normalLengthSq_pos k _ (by
      intro h
      exact one_ne_zero (congrArg (fun v : ℂ × (Fin k → ℂ) => v.1) h)))
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_fst).mul (hN.inv₀ hn))

#print axioms continuous_normalChartScale

/-- The interpolated normal vector in its fixed local frame. -/
def normalChartVector (k : ℕ) (t : unitInterval) (z : Fin k → ℂ) : Fin k → ℂ :=
  (normalChartScale k t z : ℂ) • (-normalConjugation k z)

/-- The interpolation never introduces a new zero in the normal coordinates. -/
theorem normalChartVector_zero_iff (k : ℕ) (t : unitInterval) (z : Fin k → ℂ) :
    normalChartVector k t z = 0 ↔ z = 0 := by
  have hs : (normalChartScale k t z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (normalChartScale_pos k t z))
  constructor
  · intro h
    have hv : -normalConjugation k z = 0 := (smul_eq_zero.mp h).resolve_left hs
    apply (normalConjugation_involutive k).injective
    simpa only [map_zero] using neg_eq_zero.mp hv
  · rintro rfl
    simp [normalChartVector]

#print axioms normalChartVector_zero_iff

/-- The interpolated normal vector is jointly continuous. -/
theorem continuous_normalChartVector (k : ℕ) :
    Continuous (fun tz : unitInterval × (Fin k → ℂ) => normalChartVector k tz.1 tz.2) := by
  exact (Complex.continuous_ofReal.comp (continuous_normalChartScale k)).smul
    ((-normalConjugation k).toContinuousLinearMap.continuous.comp continuous_snd)

#print axioms continuous_normalChartVector

/-- The interpolation starts at signed conjugation and ends at the actual global section's chart coordinates. -/
theorem normalChartVector_endpoints (k : ℕ) (z : Fin k → ℂ) :
    normalChartVector k 0 z = -normalConjugation k z ∧
    normalChartVector k 1 z =
      (projectiveNormalSectionVector k (normalProjectiveChart k z)).2 := by
  constructor
  · simp [normalChartVector, normalChartScale]
  · rw [projectiveNormalSectionVector_chart]
    simp [normalChartVector, normalChartScale]

#print axioms normalChartVector_endpoints

/-- Each interpolated chart map preserves the punctured normal-coordinate space. -/
def normalChartPairMap (k : ℕ) (t : unitInterval) :
    TopPair.ofSubset (X := TopCat.of (Fin k → ℂ)) ({0} : Set _)ᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (Fin k → ℂ)) ({0} : Set _)ᶜ :=
  TopPair.ofHom
    (TopCat.ofHom ⟨normalChartVector k t,
      (continuous_normalChartVector k).comp (continuous_const.prodMk continuous_id)⟩)
    (TopCat.ofHom ⟨fun z => ⟨normalChartVector k t z.1, by
      intro h
      exact z.2 ((normalChartVector_zero_iff k t z.1).mp h)⟩, by
      apply Continuous.subtype_mk
      exact (continuous_normalChartVector k).comp (continuous_const.prodMk continuous_subtype_val)⟩)
    (by ext; rfl)

#print axioms normalChartPairMap

/-- The actual section coordinates and signed linear coordinates are homotopic as punctured pair maps. -/
def normalChartPairHomotopy (k : ℕ) :
    TopPair.Homotopy (normalChartPairMap k 0) (normalChartPairMap k 1) where
  fst :=
    { toFun := fun tz => normalChartVector k tz.1 tz.2
      continuous_toFun := continuous_normalChartVector k
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  snd :=
    { toFun := fun tz => ⟨normalChartVector k tz.1 tz.2.1, by
        intro h
        exact tz.2.2 ((normalChartVector_zero_iff k tz.1 tz.2.1).mp h)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_normalChartVector k).comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  w := rfl

#print axioms normalChartPairHomotopy

/-- The actual section coordinates have the same local supported cohomology action as signed conjugation. -/
theorem normalChartPairMap_cohomology_eq (k n : ℕ) :
    relativeCohomologyMap ℚ n (normalChartPairMap k 0) =
      relativeCohomologyMap ℚ n (normalChartPairMap k 1) := by
  exact congrArg ModuleCat.Hom.hom
    ((HomologicalComplex.linearDualHomotopy
      (TopPair.Homotopy.relativeChainHomotopy (R := ℚ) (normalChartPairHomotopy k))).homologyMap_eq n)

#print axioms normalChartPairMap_cohomology_eq
end HodgeLean.Foundations.Program.G32Native.EulerModel
