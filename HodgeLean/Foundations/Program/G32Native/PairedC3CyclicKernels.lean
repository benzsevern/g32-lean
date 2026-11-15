import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Sections.SectionsGluing
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Kernels of two generating sections of the same module -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The actual ring-linear map on sections of a map out of the unit. -/
def pairedC3UnitAppLinear {X : Scheme.{0}} {Q : X.Modules}
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ Q) (U : X.Opens) :
    Γ(X, U) →ₗ[Γ(X, U)] Γ(Q, U) := (q.val.app (op U)).hom

/-- A scalar killing a generating section kills every section obtained
from any other map out of the structure module. -/
theorem paired_c3_cyclic_annihilator {X : Scheme.{0}} {Q : X.Modules}
    (q : SheafOfModules.unit X.ringCatSheaf ⟶ Q) [Epi q]
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ Q)
    (U : X.Opens) (r : Γ(X, U)) (hr : pairedC3UnitAppLinear q U r = 0) :
    pairedC3UnitAppLinear f U r = 0 := by
  have hl := (Scheme.Modules.Hom.epi_iff_locallySurjective q).mp inferInstance
  have hlocal : ∀ x : {x : X // x ∈ U}, ∃ V : X.Opens, ∃ hVU : V ≤ U,
      x.val ∈ V ∧ ∃ t : Γ(X, V),
        pairedC3UnitAppLinear q V t =
          Q.presheaf.map (homOfLE hVU).op (pairedC3UnitAppLinear f U 1) := by
    intro x
    obtain ⟨V, hVU, hx, t, ht⟩ := hl U (pairedC3UnitAppLinear f U 1) x.val x.property
    exact ⟨V, hVU, hx, t, ht⟩
  choose V hVU hx t ht using hlocal
  have hcover : U ≤ ⨆ x, V x := by
    intro x hxU
    exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible Q V U hVU hcover).1
  intro x
  rw [map_zero]
  let rV : Γ(X, V x) := X.presheaf.map (homOfLE (hVU x)).op r
  have hrV : pairedC3UnitAppLinear q (V x) rV = 0 := by
    have hn := PresheafOfModules.naturality_apply q.val (homOfLE (hVU x)).op r
    change pairedC3UnitAppLinear q (V x) rV =
      Q.presheaf.map (homOfLE (hVU x)).op (pairedC3UnitAppLinear q U r) at hn
    rw [hr, map_zero] at hn
    exact hn
  have hf1 : pairedC3UnitAppLinear f (V x) 1 =
      Q.presheaf.map (homOfLE (hVU x)).op (pairedC3UnitAppLinear f U 1) := by
    have hn := PresheafOfModules.naturality_apply f.val (homOfLE (hVU x)).op
      (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from (1 : Γ(X, U)))
    change pairedC3UnitAppLinear f (V x)
      (X.presheaf.map (homOfLE (hVU x)).op 1) = _ at hn
    rw [map_one] at hn
    exact hn
  have hfr := PresheafOfModules.naturality_apply f.val (homOfLE (hVU x)).op r
  change pairedC3UnitAppLinear f (V x) rV =
    Q.presheaf.map (homOfLE (hVU x)).op (pairedC3UnitAppLinear f U r) at hfr
  rw [← hfr]
  calc
    pairedC3UnitAppLinear f (V x) rV = rV • pairedC3UnitAppLinear f (V x) 1 := by
      simpa only [smul_eq_mul, mul_one] using (pairedC3UnitAppLinear f (V x)).map_smul rV 1
    _ = rV • pairedC3UnitAppLinear q (V x) (t x) := by rw [hf1, ht x]
    _ = (t x) • pairedC3UnitAppLinear q (V x) rV := by
      rw [← (pairedC3UnitAppLinear q (V x)).map_smul rV (t x),
        ← (pairedC3UnitAppLinear q (V x)).map_smul (t x) rV]
      congr 1
      exact mul_comm _ _
    _ = 0 := by rw [hrV, smul_zero]

end HodgeLean.Foundations.Program.G32Native
