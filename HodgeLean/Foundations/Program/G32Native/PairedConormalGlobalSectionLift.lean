import HodgeLean.Foundations.Program.G32Native.PairedConormalCechSections
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.ModuleSheafAffSES
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.AffineExactSequenceSections

/-! # Global lifting through an actual module-sheaf short exact sequence -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Vanishing of the actual kernel Cech group lifts actual global quotient
sections, through the original sheaf morphism. -/
theorem paired_global_sections_surjective_of_cech_h1
    {R : Type} [CommRing R] {X : Scheme} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (K : X.OrderedAffineCover) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [Subsingleton ((Scheme.Modules.toOModulePresheaf π S.X₁).HSucc K 0)] :
    Function.Surjective (S.g.app ⊤) := by
  intro z
  let F₂ := Scheme.Modules.toOModulePresheaf π S.X₂
  let F₃ := Scheme.Modules.toOModulePresheaf π S.X₃
  let T := Scheme.Modules.toOModulePresheafAffSES π S hS
  let z₀ : F₃.H0 K :=
    ⟨pairedCechRestriction F₃ K z, pairedCechRestriction_cocycle F₃ K z⟩
  obtain ⟨c, hc⟩ := T.H0Map_proj_surjective_of_subsingleton_H1 K z₀
  obtain ⟨s, hs⟩ := paired_cech_zero_glue K S.X₂ c.val c.property
  refine ⟨s, ?_⟩
  apply (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    S.X₃ (fun v : K.Idx 0 => K.inter v) ⊤ (fun _ => le_top)
      (by rw [paired_cech_vertex_cover K])).1
  intro v
  have hp := congrFun (congrArg Subtype.val hc) v
  change S.g.app (K.inter v) (c.val v) = F₃.res (le_top : K.inter v ≤ ⊤) z at hp
  have hn := OModulePresheaf.Hom.naturality_apply
    (Scheme.Modules.toOModulePresheafHom π S.g) (le_top : K.inter v ≤ ⊤) s
  change F₃.res (le_top : K.inter v ≤ ⊤) (S.g.app ⊤ s) =
    F₃.res (le_top : K.inter v ≤ ⊤) z
  exact hn.symm.trans ((congrArg (S.g.app (K.inter v)) (hs v)).trans hp)

end HodgeLean.Foundations.Program.G32Native
