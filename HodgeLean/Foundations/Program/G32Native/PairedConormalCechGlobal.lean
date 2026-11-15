import HodgeLean.Foundations.Program.G32Native.PairedConormalCechVertices
import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Actual global sections of ordered degree-zero cocycles -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program.G32Native
variable {R : Type*} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
    (K : X.OrderedAffineCover) (M : X.Modules)

/-- Restriction of a section on the whole space gives a zero cocycle. -/
def conormalCechPresheafCocycle (F : OModulePresheaf f) (x : F.obj ⊤) : F.H0 K := by
  refine ⟨fun s => F.res le_top x, ?_⟩
  apply funext
  intro s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul,
    OModulePresheaf.res_res, add_neg_cancel, Pi.zero_apply]

abbrev conormalCechGlobalCocycle (x : Γ(M, ⊤)) :
    (Scheme.Modules.toOModulePresheaf f M).H0 K :=
  conormalCechPresheafCocycle f K (Scheme.Modules.toOModulePresheaf f M) x

/-- Every zero cocycle glues to an actual global module-sheaf section. -/
theorem conormalCechGlobal_exists (c : (Scheme.Modules.toOModulePresheaf f M).H0 K) :
    ∃ x : Γ(M, ⊤), ∀ i : K.ι,
      M.presheaf.map (homOfLE (le_top : K.U i ≤ ⊤)).op x =
        conormalCechVertexSection (Scheme.Modules.toOModulePresheaf f M) K c.val i := by
  apply ExistsUnique.exists
  apply TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ K.U ⊤
    (fun _ => homOfLE le_top) (by rw [K.iSup_eq_top])
  intro i j
  exact conormalCechVertexSection_compatible _ K c i j

end HodgeLean.Foundations.Program.G32Native
