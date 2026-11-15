import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.TensorWithFrame

/-! Normalize tensor sections against an actual local line frame. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
namespace HodgeLean.Foundations.Program

/-- Tensoring with a given line frame is a linear equivalence on sections of its open. -/
def g32l4_tensorFrameEquiv {X : Scheme.{0}} (F L : X.Modules)
    (s : Γ(L, ⊤)) (V : X.Opens) (hs : IsFrameOn s V) :
    Γ(F, V) ≃ₗ[Γ(X, V)] Γ(F ⊗ L, V) :=
  LinearEquiv.ofBijective
    { toFun := fun m => tensorSections m (L.presheaf.map (homOfLE le_top).op s)
      map_add' := fun m m' => tensorSections_add_left m m' _
      map_smul' := fun a m => tensorSections_smul_left a m _ }
    (hs.bijective_tensorSections F le_top le_rfl)

end HodgeLean.Foundations.Program
