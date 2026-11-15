import HodgeLean.Foundations.Program.G32Native.PairedC3FiniteLocalLifts
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalSection

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- A finite free arrow lifts locally through an epimorphism on the original slice site.
Source: Hartshorne, Algebraic Geometry, II.5, local generators. -/
theorem paired_c3_free_arrow_local_lift {X : Scheme.{0}} {M N : X.Modules}
    (p : M ⟶ N) [Epi p] {I : Type} [Finite I]
    (q : SheafOfModules.free I ⟶ N) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ l : SheafOfModules.free I ⟶ M.over V,
      l ≫ p.over V =
        SheafOfModules.mapFree (SheafOfModules.overFunctor X.ringCatSheaf V) I (𝟙 _) ≫
          q.over V := by
  let s : I → Γ(N, ⊤) := fun i => (N.freeHomEquiv q i).val (op ⊤)
  obtain ⟨V, hV, hxV, t, ht⟩ := paired_c3_finite_local_lifts p ⊤ s x trivial
  let l : SheafOfModules.free I ⟶ M.over V :=
    (M.over V).freeHomEquiv.symm (fun i => paired_module_overSection M V (t i))
  refine ⟨V, hxV, l, ?_⟩
  apply Sigma.hom_ext
  intro i
  change SheafOfModules.ιFree i ≫ (l ≫ p.over V) =
    SheafOfModules.ιFree i ≫ (SheafOfModules.mapFree
      (SheafOfModules.overFunctor X.ringCatSheaf V) I (𝟙 _) ≫ q.over V)
  rw [SheafOfModules.ιFree_mapFree_assoc, Category.id_comp]
  apply (N.over V).unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  change SheafOfModules.sectionsMap (p.over V)
      ((M.over V).freeHomEquiv l i) = _
  simp only [l, Equiv.apply_symm_apply]
  apply Subtype.ext
  funext W
  change p.app W.unop.left (M.presheaf.map W.unop.hom.op (t i)) =
    ((N.freeHomEquiv q i).val (op W.unop.left))
  have hn := ConcreteCategory.congr_hom (p.val.naturality W.unop.hom.op) (t i)
  change p.app W.unop.left (M.presheaf.map W.unop.hom.op (t i)) =
    N.presheaf.map W.unop.hom.op (p.app V (t i)) at hn
  rw [hn, ht]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact (N.freeHomEquiv q i).property _

end HodgeLean.Foundations.Program.G32Native
