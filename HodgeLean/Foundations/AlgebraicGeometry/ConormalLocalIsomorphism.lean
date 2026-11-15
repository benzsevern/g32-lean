import HodgeLean.Foundations.AlgebraicGeometry.ConormalFramesDefs
import Mathlib.Topology.Sheaves.Stalks

/-! # Detecting module isomorphisms on open neighborhoods
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- A module morphism invertible after pullback on neighborhoods of every point is invertible. -/
lemma moduleMap_isIso_of_open_neighborhoods {X : Scheme.{0}} {M N : X.Modules}
    (a : M ⟶ N)
    (h : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map a)) :
    IsIso a := by
  let ψ : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X) ⟶
      ⟨N.presheaf, N.isSheaf⟩ := ⟨a.mapPresheaf⟩
  have hs (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map a.mapPresheaf) := by
    obtain ⟨U, hx, hU⟩ := h x
    have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a) :=
      (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) a).mpr hU
    have hv : IsIso ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U.toScheme ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat (⟨x, hx⟩ : U)).map a) := by
      change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (⟨x, hx⟩ : U)).map
        ((Scheme.Modules.toPresheaf U.toScheme).map ((Scheme.Modules.restrictFunctor U.ι).map a)))
      infer_instance
    exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι ⟨x, hx⟩) a).mp hv
  have : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ψ.hom) := hs
  have : IsIso ψ := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ψ
  have : IsIso ((Scheme.Modules.toPresheaf X).map a) :=
    (TopCat.Sheaf.forget AddCommGrpCat X).map_isIso ψ
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf X)

end AlgebraicGeometry.Conormal
