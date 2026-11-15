import HodgeLean.Ported.Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp

/-! Keep the original labels on the strict-transform branch family. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The original labelled family, with every branch replaced by its saturation strict transform. -/
def g32l4_strictTransformFamily {X : Scheme}
    (E : Scheme.DivisorFamily X) (K : X.IdealSheafData) : Scheme.DivisorFamily K.blowUp where
  ι := E.ι
  fintype := E.fintype
  linearOrder := E.linearOrder
  component := fun i => (E.component i).strictTransform K

end HodgeLean.Foundations.Program
