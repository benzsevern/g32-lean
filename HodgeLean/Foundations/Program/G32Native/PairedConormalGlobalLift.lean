import HodgeLean.Foundations.Program.G32Native.PairedConormalCechNaturality
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.ModuleSheafAffSES
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.AffineExactSequenceSections

/-! # Global lifting through the actual module-sheaf sequence -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {R : Type*} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
    [IsSeparated f] (K : X.OrderedAffineCover)

/-- First cohomology vanishing lifts actual global sections through the original arrow. -/
theorem conormal_global_surjective_of_cech_vanishing
    (S : ShortComplex X.Modules) (hs : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [Subsingleton ((Scheme.Modules.toOModulePresheaf f S.X₁).HSucc K 0)] :
    Function.Surjective (S.g.app ⊤) := by
  intro x
  let T := Scheme.Modules.toOModulePresheafAffSES f S hs
  obtain ⟨c, hc⟩ := T.H0Map_proj_surjective_of_subsingleton_H1 K
    (conormalCechGlobalCocycle f K S.X₃ x)
  obtain ⟨y, hy⟩ := conormalCechGlobal_exists f K S.X₂ c
  refine ⟨y, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, S.X₃.isSheaf⟩ K.U ⊤
    (fun _ => homOfLE le_top) (by rw [K.iSup_eq_top])
  intro i
  have hn := congrArg (fun p : Γ(S.X₂, ⊤) ⟶ Γ(S.X₃, K.U i) => p y)
    (S.g.mapPresheaf.naturality (homOfLE (le_top : K.U i ≤ ⊤)).op)
  change S.g.app (K.U i) (S.X₂.presheaf.map (homOfLE le_top).op y) =
    S.X₃.presheaf.map (homOfLE le_top).op (S.g.app ⊤ y) at hn
  rw [← hn, hy i, conormalCechVertex_naturality f K S.g c i]
  change conormalCechVertexSection (Scheme.Modules.toOModulePresheaf f S.X₃) K
    ((T.proj.H0Map K) c).val i = _
  rw [hc, conormalCechGlobal_vertex]

end HodgeLean.Foundations.Program.G32Native
