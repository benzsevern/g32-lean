import HodgeLean.Foundations.BundleResolution.ModuleLocalFrameHelpers
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Fibres of algebraic frames

Pulling a frame to a complex point identifies its fibre with the actual
free complex module. Finite complex fibres force finite frame index sets,
and the specified rank gives frames indexed by `Fin k`.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleResolution
variable {Q : Over (Spec ↧ℂ)}
def i1_freeModuleFibreIso (I : Type) (x : ComplexPoint Q) :
    i1_moduleFibre (SheafOfModules.free (R := Q.left.ringCatSheaf) I) x ≅
      ModuleCat.of ℂ (I →₀ ℂ) := by
  let F := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  letI : (SheafOfModules.pushforward x.left.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward x.left).IsRightAdjoint)
  exact F.mapIso (SheafOfModules.pullbackObjFreeIso x.left.toRingCatSheafHom I) ≪≫
    F.mapIso (tildeFinsupp (R := CommRingCat.of ℂ) I).symm ≪≫ (tilde.isoTop (R := CommRingCat.of ℂ) (ModuleCat.of ℂ (I →₀ ℂ))).symm

def i1_module_openFibreIso (M : Q.left.Modules) (U : Q.left.Opens)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx)).obj
        ((Scheme.Modules.pullback U.ι).obj M)) ≅ i1_moduleFibre M x :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    ((Scheme.Modules.pullbackComp (ComplexPoint.liftToOpen Q U x hx) U.ι).app M ≪≫
      (Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).app M)

def i1_module_frameFibreIso (M : Q.left.Modules) (U : Q.left.Opens) (I : Type)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    ModuleCat.of ℂ (I →₀ ℂ) ≅ i1_moduleFibre M x :=
  (i1_freeModuleFibreIso I (ComplexPoint.asOpenPoint Q U x hx)).symm ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
      ((Scheme.Modules.pullback (ComplexPoint.liftToOpen Q U x hx)).mapIso e) ≪≫
    i1_module_openFibreIso M U x hx

theorem i1_module_localFrame_finiteIndex (M : Q.left.Modules) (U : Q.left.Opens) (I : Type)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U)
    [Module.Finite ℂ (i1_moduleFibre M x)] : Finite I := by
  let b := (Finsupp.basisSingleOne : Module.Basis I ℂ (I →₀ ℂ)).map
    (i1_module_frameFibreIso M U I e x hx).toLinearEquiv
  exact Module.Finite.finite_basis b

theorem i1_module_localFrame_fin (M : Q.left.Modules) [M.IsLocallyFree]
    (k : ℕ) (x : ComplexPoint Q) [Module.Finite ℂ (i1_moduleFibre M x)]
    (hrank : Module.finrank ℂ (i1_moduleFibre M x) = k) :
    ∃ (U : Q.left.Opens), x ∈ Point.overOpen U ∧
      Nonempty (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) ≅
        (Scheme.Modules.pullback U.ι).obj M) := by
  classical
  obtain ⟨U, hx, I, ⟨e⟩⟩ := i1_module_localFrame_pullback M x.underlying
  have hx' : x ∈ Point.overOpen U := hx
  let := i1_module_localFrame_finiteIndex M U I e x hx'
  let := Fintype.ofFinite I
  let b := (Finsupp.basisSingleOne : Module.Basis I ℂ (I →₀ ℂ)).map
    (i1_module_frameFibreIso M U I e x hx').toLinearEquiv
  have hc : Fintype.card I = k := (Module.finrank_eq_card_basis b).symm.trans hrank
  let ei : I ≃ Fin k := Fintype.equivFinOfCardEq hc
  exact ⟨U, hx', ⟨(SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
    ei.toIso.symm ≪≫ e⟩⟩
theorem i1_module_lineFrame_fibre (M : Q.left.Modules) (U : Q.left.Opens)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) PUnit ≅
      (Scheme.Modules.pullback U.ι).obj M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    Module.Finite ℂ (i1_moduleFibre M x) ∧ Module.finrank ℂ (i1_moduleFibre M x) = 1 := by
  let e' := i1_module_frameFibreIso M U PUnit e x hx
  refine ⟨Module.Finite.equiv e'.toLinearEquiv, ?_⟩
  rw [← e'.toLinearEquiv.finrank_eq, Module.finrank_finsupp_self, Fintype.card_unique]

end HodgeLean.Foundations.BundleResolution
