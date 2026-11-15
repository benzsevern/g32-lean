import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalSchemeAffineTopology
import HodgeLean.Foundations.Analytic.Analytification

/-! # Native holomorphic coordinates of the actual normal base chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual inverse affine-chart coordinates are holomorphic in the native analytification. -/
theorem normalSchemeAffineChart_coordinate_holomorphic (k : ℕ)
    [LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))]
    [QuasiCompact (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))]
    [IsSeparated (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))]
    (j : Fin k) :
    (f4_analytification
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))).IsHolFun
        (fun q : (normalSchemeAffineChart k).source => normalSchemeAffineChart k q j) := by
  have he : (fun q : (normalSchemeAffineChart k).source => normalSchemeAffineChart k q j) =
      (fun q : (normalSchemeAffineChart k).source => Point.evaluate (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1
        (normalAffineCoordinateSection k j) q.1) := by
    funext q
    exact normalSchemeAffineChart_coordinate k j q q.2
  rw [he]
  have hsub : (normalSchemeAffineChart k).source ⊆
      Point.overOpen (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1 := by
    rw [normalSchemeAffineChart_source, normalSchemeAffineParam_range]
  exact anb_isHolFun_restrict
    (f4_analytification (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))).atlas hsub
    (f4_isHolFun_evaluate
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_standardProjectiveAffineOpen (0 : Fin (k + 1))).1
      (normalAffineCoordinateSection k j))

#print axioms normalSchemeAffineChart_coordinate_holomorphic
/-- The point chart's ordered complex coordinates, with no tangential directions. -/
def normalPointProductCoordinates (k : ℕ) :
    (Fin k → ℂ) ≃ₜ ((Fin 0 → ℂ) × (Fin k → ℂ)) where
  toFun z := (0, z)
  invFun v := v.2
  left_inv _ := rfl
  right_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  continuous_toFun := continuous_const.prodMk continuous_id
  continuous_invFun := continuous_snd

/-- The actual native projective chart as a point-support flattening chart. -/
def normalSchemePointChart (k : ℕ) :
    OpenPartialHomeomorph
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
      ((Fin 0 → ℂ) × (Fin k → ℂ)) :=
  (normalSchemeAffineChart k).trans (normalPointProductCoordinates k).toOpenPartialHomeomorph

#print axioms normalPointProductCoordinates
#print axioms normalSchemePointChart
/-- Adding the zero tangential directions retains the exact native affine chart source. -/
theorem normalSchemePointChart_source (k : ℕ) :
    (normalSchemePointChart k).source = (normalSchemeAffineChart k).source := by
  simp only [normalSchemePointChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]

#print axioms normalSchemePointChart_source
/-- The actual point-support chart satisfies the native holomorphic chart predicate. -/
theorem normalSchemePointChart_holomorphic (k : ℕ)
    [LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))]
    [QuasiCompact (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))]
    [IsSeparated (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))] :
    a3b4_IsHolChart (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
      (normalSchemePointChart k) := by
  constructor
  · intro j
    exact j.elim0
  · intro j
    have hsub : (normalSchemePointChart k).source ⊆ (normalSchemeAffineChart k).source := by
      rw [normalSchemePointChart_source]
    exact anb_isHolFun_restrict
      (f4_analytification (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))).atlas
      hsub (normalSchemeAffineChart_coordinate_holomorphic k j)

#print axioms normalSchemePointChart_holomorphic
/-- The actual native point-support chart retains the ordered affine normal parameters. -/
theorem normalSchemePointChart_param (k : ℕ) (z : Fin k → ℂ) :
    normalSchemePointChart k (normalSchemeAffineParam k z) = (0, z) := by
  change (0, normalSchemeAffineChart k (normalSchemeAffineParam k z)) = (0, z)
  rw [normalSchemeAffineChart_param]

#print axioms normalSchemePointChart_param
end HodgeLean.Foundations.Program.G32Native.EulerModel
