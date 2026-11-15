import HodgeLean.Foundations.Program.G32Native.FreeSheafRank

/-! Uniqueness of local frame ranks at a common point. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A frame pulls back to a frame of the same rank on any smaller neighbourhood. -/
def g32l4_frame_on_smaller_open {X : Scheme} (M : X.Modules) {U V : X.Opens}
    (h : U ≤ V) {n : ℕ}
    (e : Scheme.Modules.restrict M V.ι ≅
      (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin n) : V.toScheme.Modules)) :
    Scheme.Modules.restrict M U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin n) : U.toScheme.Modules) := by
  let f := X.homOfLE h
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.pullbackComp f V.ι).symm.app M ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app M ≪≫ e) ≪≫
    SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (Fin n)

/-- Two local frames of one sheaf at the same point have equal finite ranks. -/
theorem g32l4_local_frame_rank_unique {X : Scheme} (M : X.Modules) (x : X)
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V) {m n : ℕ}
    (eU : Scheme.Modules.restrict M U.ι ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin m) : U.toScheme.Modules))
    (eV : Scheme.Modules.restrict M V.ι ≅
      (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin n) : V.toScheme.Modules)) :
    m = n := by
  let W : X.Opens := U ⊓ V
  let eU' := g32l4_frame_on_smaller_open M (show W ≤ U from inf_le_left) eU
  let eV' := g32l4_frame_on_smaller_open M (show W ≤ V from inf_le_right) eV
  exact g32l4_free_rank_unique_at (X := W.toScheme) ⟨x, hxU, hxV⟩ (eU'.symm ≪≫ eV')

end HodgeLean.Foundations.Program
