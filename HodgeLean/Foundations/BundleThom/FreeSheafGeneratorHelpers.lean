import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Analysis.Complex.Basic

/-! # Generators under the affine free-sheaf comparison

The comparison preserves the specified summand injections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- The affine free-sheaf comparison sends a standard generator to its sheaf summand.
Source: Hartshorne, Algebraic Geometry, II.5, the sheaf associated to a free module. -/
theorem i1_tildeFinsupp_generator (k : ℕ) (i : Fin k) :
    (tilde.functor (CommRingCat.of ℂ)).map
      (ModuleCat.ofHom (Finsupp.lsingle i : ℂ →ₗ[ℂ] (Fin k →₀ ℂ))) ≫
        (tildeFinsupp (R := CommRingCat.of ℂ) (Fin k)).hom =
      SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) i := by
  let R : CommRingCat.{0} := CommRingCat.of ℂ
  letI := (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  let H : IsColimit ((tilde.functor R).mapCocone (ModuleCat.finsuppCocone R R (Fin k))) :=
    isColimitOfPreserves (tilde.functor R) (ModuleCat.finsuppCoconeIsColimit R R (Fin k))
  let iso : (Discrete.functor fun (_ : Fin k) => ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor fun _ => SheafOfModules.unit (Spec R).ringCatSheaf :=
    Discrete.natIso (fun _ => tildeSelf)
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv iso.symm _).symm H)
    (coproductIsCoproduct _) (Discrete.mk i)
  change (tildeSelf (R := R)).inv ≫
    ((tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (Fin k →₀ R))) ≫
      (tildeFinsupp (R := R) (Fin k)).hom) = SheafOfModules.ιFree i at h
  have hid : (tildeSelf (R := R)).inv ≫
      ((tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (Fin k →₀ R))) ≫
        (tildeFinsupp (R := R) (Fin k)).hom) =
      (tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i : R →ₗ[R] (Fin k →₀ R))) ≫
        (tildeFinsupp (R := R) (Fin k)).hom := Category.id_comp _
  exact hid.symm.trans h

/-- The affine unit comparison takes the scalar one to the unit section.
Source: Hartshorne, Algebraic Geometry, II.5, affine global sections. -/
theorem i1_pointUnitComparison_one :
    ((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
      (ModuleCat.of ℂ ℂ)).hom (1 : ℂ) = (1 : Γ(Spec ↧ℂ, ⊤)) := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv (1 : ℂ) = 1
  exact map_one _

end HodgeLean.Foundations.BundleThom
