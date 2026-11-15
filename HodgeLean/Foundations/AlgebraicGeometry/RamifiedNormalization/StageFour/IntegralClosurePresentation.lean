import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageTwo.Defs

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original integral elements retain their values when the ring-homomorphism presentation is replaced by the given algebra structure. -/
def normalizedChartIntegralClosureEquiv
    {A L : Type*} [CommRing A] [Field L] [Algebra A L] :
    normalizedChart (algebraMap A L) ≃+* integralClosure A L where
  toFun x := ⟨x.val, by
    have hx := x.property
    change _root_.IsIntegral A x.val
    change _root_.IsIntegral A x.val at hx
    exact hx⟩
  invFun x := ⟨x.val, by
    change _root_.IsIntegral A x.val
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
