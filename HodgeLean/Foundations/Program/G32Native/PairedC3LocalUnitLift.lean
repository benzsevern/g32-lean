import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Frames.IsFrameOnPullbackIsoUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3FiniteLocalLift

/-! # Local section lifts as morphism lifts on the original open subscheme -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry.Scheme.Modules.FrameBridge

/-- A lift of a unit section on an open defines a morphism lift after
restriction to that same open, without quasicoherence assumptions. -/
theorem paired_c3_local_unit_lift {X : Scheme} {M N : X.Modules}
    (g : M ⟶ N) (u : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ N)
    (U : X.Opens) (t : Γ(M, U))
    (ht : g.app U t = (Scheme.Modules.Hom.app u) U (1 : Γ(X, U))) :
    ∃ l : (Scheme.Modules.restrictFunctor U.ι).obj
        (SheafOfModules.unit X.ringCatSheaf) ⟶
        (Scheme.Modules.restrictFunctor U.ι).obj M,
      l ≫ (Scheme.Modules.restrictFunctor U.ι).map g =
        (Scheme.Modules.restrictFunctor U.ι).map u := by
  rw [← restrictFunctor'_eq U]
  refine ⟨smulSectionHom M U t, ?_⟩
  apply Scheme.Modules.hom_ext
  intro V
  ext r
  let W := U.ι ''ᵁ V
  let rX : Γ(X, W) := r
  have hWU : W ≤ U := image_le U V
  have hg := ConcreteCategory.congr_hom
    (g.mapPresheaf.naturality (homOfLE hWU).op) t
  change g.app W (M.presheaf.map (homOfLE hWU).op t) =
    N.presheaf.map (homOfLE hWU).op (g.app U t) at hg
  have hu := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf u).naturality (homOfLE hWU).op) (1 : Γ(X, U))
  change (Scheme.Modules.Hom.app u) W (X.presheaf.map (homOfLE hWU).op (1 : Γ(X, U))) =
    N.presheaf.map (homOfLE hWU).op ((Scheme.Modules.Hom.app u) U (1 : Γ(X, U))) at hu
  rw [map_one] at hu
  change g.app W (rX • M.presheaf.map (homOfLE hWU).op t) = (Scheme.Modules.Hom.app u) W rX
  rw [Scheme.Modules.Hom.app_smul, hg, ht, ← hu]
  have hr := Scheme.Modules.Hom.app_smul u rX (1 : Γ(X, W))
  simpa only [smul_eq_mul, mul_one] using hr.symm

#print axioms paired_c3_local_unit_lift
/-- A finite family of original unit morphisms lifts simultaneously after
restriction to one neighborhood through an arbitrary epimorphism. -/
theorem paired_c3_finite_local_unit_lift {X : Scheme} {M N : X.Modules}
    (g : M ⟶ N) [Epi g] {I : Type} [Finite I]
    (u : I → ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ N)) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ i,
      ∃ l : (Scheme.Modules.restrictFunctor U.ι).obj
          (SheafOfModules.unit X.ringCatSheaf) ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj M,
        l ≫ (Scheme.Modules.restrictFunctor U.ι).map g =
          (Scheme.Modules.restrictFunctor U.ι).map (u i) := by
  obtain ⟨U, hU, hx, t, ht⟩ := paired_c3_finite_local_lift g ⊤
    (fun i => Scheme.Modules.Hom.app (u i) ⊤ (1 : Γ(X, ⊤))) x (by trivial)
  refine ⟨U, hx, ?_⟩
  intro i
  apply paired_c3_local_unit_lift g (u i) U (t i)
  rw [ht i]
  have hu := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf (u i)).naturality (homOfLE hU).op)
      (1 : Γ(X, ⊤))
  change Scheme.Modules.Hom.app (u i) U
      (X.presheaf.map (homOfLE hU).op (1 : Γ(X, ⊤))) =
    N.presheaf.map (homOfLE hU).op (Scheme.Modules.Hom.app (u i) ⊤ (1 : Γ(X, ⊤))) at hu
  rw [map_one] at hu
  exact hu.symm

#print axioms paired_c3_finite_local_unit_lift
/-- An arbitrary epimorphism with a finite free quotient has a local section
near every point of the original scheme. -/
theorem paired_c3_free_quotient_local_section {X : Scheme} {M N : X.Modules}
    (g : M ⟶ N) [Epi g] (I : Type) [Finite I]
    (e : N ≅ SheafOfModules.free I) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ s : (Scheme.Modules.restrictFunctor U.ι).obj N ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj M,
        s ≫ (Scheme.Modules.restrictFunctor U.ι).map g = 𝟙 _ := by
  obtain ⟨U, hx, hl⟩ := paired_c3_finite_local_unit_lift g
    (fun i : I => SheafOfModules.ιFree i ≫ e.inv) x
  choose l hl using hl
  let F := Scheme.Modules.restrictFunctor U.ι
  let c : Cofan (fun _ : I => F.obj (SheafOfModules.unit X.ringCatSheaf)) :=
    Cofan.mk (F.obj M) l
  let hc := isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)
  let a : F.obj (SheafOfModules.free I) ⟶ F.obj M := hc.desc c
  have ha : a ≫ F.map g = F.map e.inv := by
    apply hc.hom_ext
    intro j
    change F.map (SheafOfModules.ιFree j.as) ≫ (a ≫ F.map g) =
      F.map (SheafOfModules.ιFree j.as) ≫ F.map e.inv
    rw [← Category.assoc]
    have hd : F.map (SheafOfModules.ιFree j.as) ≫ a = l j.as := hc.fac c j
    rw [hd, hl j.as, F.map_comp]
  refine ⟨U, hx, F.map e.hom ≫ a, ?_⟩
  rw [Category.assoc, ha, ← F.map_comp, e.hom_inv_id, F.map_id]

#print axioms paired_c3_free_quotient_local_section
end HodgeLean.Foundations.Program.G32Native
