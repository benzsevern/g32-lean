import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Sections.SectionsGluing

/-! # Gluing natural local linear comparisons -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

abbrev pairedC3ModuleRestrict {X : Scheme.{0}} (M : X.Modules) {V W : X.Opens} (h : W ≤ V) :=
  M.presheaf.map (homOfLE h).op

/-- Restriction of module sections respects composition of inclusions. -/
theorem paired_c3_module_restrict_comp {X : Scheme.{0}} (M : X.Modules)
    {V W T : X.Opens} (h : W ≤ V) (g : T ≤ W) (s : Γ(M, V)) :
    pairedC3ModuleRestrict M g (pairedC3ModuleRestrict M h s) =
      pairedC3ModuleRestrict M (g.trans h) s := by
  dsimp only [pairedC3ModuleRestrict]
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

/-- Natural section comparisons on every subopen of each chart, agreeing
where two charts are available.
Source: Hartshorne, Algebraic Geometry, II.1, the sheaf gluing condition. -/
structure PairedC3LocalModuleComparison {X : Scheme.{0}} (M N : X.Modules)
    {ι : Type} (U : ι → X.Opens) where
  equiv (i : ι) (V : X.Opens) (hV : V ≤ U i) : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V)
  restrict (i : ι) (V W : X.Opens) (h : W ≤ V) (hV : V ≤ U i) (s : Γ(M, V)) :
    equiv i W (h.trans hV) (pairedC3ModuleRestrict M h s) =
      pairedC3ModuleRestrict N h (equiv i V hV s)
  agree (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(M, V)) :
    equiv i V hi s = equiv j V hj s

variable {X : Scheme.{0}} {M N : X.Modules} {ι : Type} {U : ι → X.Opens}
    (D : PairedC3LocalModuleComparison M N U) (hU : ⨆ i, U i = ⊤)

/-- The chartwise images of a section form a matching family. -/
theorem paired_c3_local_module_images_match (V : X.Opens) (s : Γ(M, V)) (i j : ι) :
    pairedC3ModuleRestrict N (inf_le_left : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ V ⊓ U i)
        (D.equiv i (V ⊓ U i) inf_le_right (pairedC3ModuleRestrict M inf_le_left s)) =
      pairedC3ModuleRestrict N (inf_le_right : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ V ⊓ U j)
        (D.equiv j (V ⊓ U j) inf_le_right (pairedC3ModuleRestrict M inf_le_left s)) := by
  rw [← D.restrict i _ _ inf_le_left inf_le_right,
    ← D.restrict j _ _ inf_le_right inf_le_right,
    paired_c3_module_restrict_comp, paired_c3_module_restrict_comp]
  exact D.agree i j _ _ _ _

include hU

/-- Gluing the matching local images gives a section on the original open. -/
theorem paired_c3_local_module_image_exists (V : X.Opens) (s : Γ(M, V)) :
    ∃ t : Γ(N, V), ∀ i, pairedC3ModuleRestrict N (inf_le_left : V ⊓ U i ≤ V) t =
      D.equiv i (V ⊓ U i) inf_le_right (pairedC3ModuleRestrict M inf_le_left s) := by
  have hV : V ≤ ⨆ i, V ⊓ U i := by rw [← inf_iSup_eq, hU, inf_top_eq]
  exact (N.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    (fun i : ι => V ⊓ U i) V (fun _ => inf_le_left) hV).2 _
      (paired_c3_local_module_images_match D V s)

/-- The section obtained from the specified local images. -/
def pairedC3LocalModuleImage (V : X.Opens) (s : Γ(M, V)) : Γ(N, V) :=
  (paired_c3_local_module_image_exists D hU V s).choose

/-- Its restriction recovers the specified chartwise linear image. -/
theorem paired_c3_local_module_image_restrict (V : X.Opens) (s : Γ(M, V)) (i : ι) :
    pairedC3ModuleRestrict N (inf_le_left : V ⊓ U i ≤ V) (pairedC3LocalModuleImage D hU V s) =
      D.equiv i (V ⊓ U i) inf_le_right (pairedC3ModuleRestrict M inf_le_left s) :=
  (paired_c3_local_module_image_exists D hU V s).choose_spec i

/-- The same formula on every smaller open contained in a chart. -/
theorem paired_c3_local_module_image_restrict_of_le
    (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : W ≤ U i) (s : Γ(M, V)) :
    pairedC3ModuleRestrict N h (pairedC3LocalModuleImage D hU V s) =
      D.equiv i W hi (pairedC3ModuleRestrict M h s) := by
  have hh := congrArg (pairedC3ModuleRestrict N (le_inf h hi))
    (paired_c3_local_module_image_restrict D hU V s i)
  rw [paired_c3_module_restrict_comp, ← D.restrict i _ _ (le_inf h hi) inf_le_right,
    paired_c3_module_restrict_comp] at hh
  exact hh

/-- Local equality on the chart cover detects equality of global sections. -/
theorem paired_c3_module_eq_of_chart_restrict {V : X.Opens} (s t : Γ(N, V))
    (h : ∀ i, pairedC3ModuleRestrict N (inf_le_left : V ⊓ U i ≤ V) s =
      pairedC3ModuleRestrict N inf_le_left t) : s = t := by
  have hV : V ≤ ⨆ i, V ⊓ U i := by rw [← inf_iSup_eq, hU, inf_top_eq]
  exact (N.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    (fun i : ι => V ⊓ U i) V (fun _ => inf_le_left) hV).1 s t h

end HodgeLean.Foundations.Program.G32Native
