import HodgeLean.Foundations.BundleResolution.ModuleTopology

/-! # Local algebraic frames for the analytification construction

Local generators with invertible presentation maps give frames on scheme
opens, both in the over site and after actual scheme pullback.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace HodgeLean.Foundations.BundleResolution

theorem i1_module_localFrame {X : Scheme.{0}} (M : X.Modules) [M.IsLocallyFree] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ (I : Type),
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  let := hq
  obtain ⟨W, f, hW, hxW⟩ := q.coversTop ⊤ x (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff q.X f).mp hW
  exact ⟨q.X i, leOfHom g hxW, (q.generators i).I, ⟨asIso (q.generators i).π⟩⟩

theorem i1_module_localFrame_pullback {X : Scheme.{0}} (M : X.Modules) [M.IsLocallyFree] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ (I : Type),
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
        (Scheme.Modules.pullback U.ι).obj M) := by
  obtain ⟨U, hx, I, ⟨e⟩⟩ := i1_module_localFrame M x
  let F := (Scheme.Modules.overEquiv U).functor
  refine ⟨U, hx, I, ⟨?_⟩⟩
  exact SheafOfModules.mapFreeIso F I (Iso.refl _) ≪≫ F.mapIso e ≪≫
    (Scheme.Modules.overFunctorEquiv U).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
end HodgeLean.Foundations.BundleResolution
