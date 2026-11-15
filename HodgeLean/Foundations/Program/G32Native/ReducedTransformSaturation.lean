import HodgeLean.Foundations.Program.G32Native.ReducedTransformSupport
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Transform
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Transform.Defs

/-! Comparison of reduced transforms with saturation on locally Noetherian schemes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Reduced closure is the radical of the saturation of the two pulled ideals. -/
theorem g32l4_reducedTransform_eq_radical_saturate {X Y : Scheme}
    [IsLocallyNoetherian X] (f : X ⟶ Y) (D K : Y.IdealSheafData) :
    s2c_strictTransform f D K = ((D.comap f).saturate (K.comap f)).radical := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  unfold s2c_strictTransform
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.IdealSheafData.coe_support_saturate,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  rfl

/-- The comparison with the ported transform along a map uses the radical explicitly. -/
theorem g32l4_reducedTransform_eq_radical_strictTransformAlong {X Y : Scheme}
    [IsLocallyNoetherian X] (f : X ⟶ Y) (D K : Y.IdealSheafData) :
    s2c_strictTransform f D K = (D.strictTransformAlong f (K.comap f)).radical :=
  g32l4_reducedTransform_eq_radical_saturate f D K

end HodgeLean.Foundations.Program
