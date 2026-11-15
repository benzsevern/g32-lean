import HodgeLean.Foundations.Program.G32Native.UnionConormalIdealKernelArrow

/-! # The ideal kernel arrow after extension of scalars -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Program.G32Native

/-- Kernel equality identifies the first tensor map with ideal inclusion. -/
def unionConormalIdealKernelArrowIso
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    (p : R →+* A) (q : R →+* B) (J : Ideal R)
    (hP : RingHom.ker p = RingHom.ker q ⊓ J) :
    Arrow.mk ((ModuleCat.extendScalars q).map (unionConormalIdealKernelArrow p q J hP)) ≅
      Arrow.mk ((ModuleCat.extendScalars q).map
        (ModuleCat.ofHom (Submodule.inclusion
          (show RingHom.ker q ⊓ J ≤ RingHom.ker q from inf_le_left)))) := by
  let e : ModuleCat.of R (RingHom.ker p) ≅ ModuleCat.of R ↥(RingHom.ker q ⊓ J) :=
    (LinearEquiv.ofEq _ _ hP).toModuleIso
  let e₀ : Arrow.mk (unionConormalIdealKernelArrow p q J hP) ≅
      Arrow.mk (ModuleCat.ofHom (Submodule.inclusion
        (show RingHom.ker q ⊓ J ≤ RingHom.ker q from inf_le_left))) :=
    Arrow.isoMk ((ModuleCat.extendScalarsId R).app _ ≪≫ e) (Iso.refl _) (by
      apply ModuleCat.hom_ext
      rfl)
  exact (ModuleCat.extendScalars q).mapArrow.mapIso e₀

end HodgeLean.Foundations.Program.G32Native
