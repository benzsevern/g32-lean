import HodgeLean.Foundations.Program.G32Native.LocalFrameRank

/-! Pull back a local frame along a scheme morphism. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A frame pulls back to the inverse image of its open neighbourhood. -/
def g32l4_pullback_frame_on_preimage {X Y : Scheme}
    (f : X ⟶ Y) (M : Y.Modules) (V : Y.Opens) (r : ℕ)
    (e : Scheme.Modules.restrict M V.ι ≅
      (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin r) : V.toScheme.Modules)) :
    Scheme.Modules.restrict ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ V).ι ≅
      (SheafOfModules.free (R := (f ⁻¹ᵁ V).toScheme.ringCatSheaf) (Fin r) :
        (f ⁻¹ᵁ V).toScheme.Modules) := by
  let g := f ∣_ V
  let : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward g).IsRightAdjoint
  exact (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app
      ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ V).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f V).symm).app M ≪≫
    (Scheme.Modules.pullbackComp g V.ι).symm.app M ≪≫
    (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app M ≪≫ e) ≪≫
    SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom (Fin r)

/-- Local frames pass to any sheaf identified with a pullback. -/
theorem g32l4_local_frames_of_pullback_iso {X Y : Scheme}
    (f : X ⟶ Y) (M : Y.Modules) (N : X.Modules) (r : ℕ)
    (e : (Scheme.Modules.pullback f).obj M ≅ N)
    (h : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ Nonempty
      (Scheme.Modules.restrict M V.ι ≅
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Fin r) : V.toScheme.Modules))) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty
      (Scheme.Modules.restrict N U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin r) : U.toScheme.Modules)) := by
  intro x
  obtain ⟨V, hx, ⟨b⟩⟩ := h (f x)
  refine ⟨f ⁻¹ᵁ V, hx, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).mapIso e.symm ≪≫
    g32l4_pullback_frame_on_preimage f M V r b

end HodgeLean.Foundations.Program
