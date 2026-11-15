import HodgeLean.Foundations.BundleThom.AnalyticNormalDefs
import HodgeLean.Foundations.Program.SchoenCycleC2SmoothConormalFramesHelpers
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import HodgeLean.Foundations.BundleThom.NormalFibreTopologyHelpers
import HodgeLean.Foundations.BundleThom.FreeSheafGeneratorHelpers

/-! # Coordinates on specialized algebraic conormal frames

Pullback of a local free frame supplies coordinates on the actual conormal fibre.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Global sections of a finite free sheaf on the complex point have their standard coordinates.
Source: Hartshorne, Algebraic Geometry, II.5, affine sheaves and global sections. -/
def i1_freePointCoordinates (k : ℕ) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      (SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k)) ≃ₗ[ℂ] (Fin k → ℂ) := by
  let M : ModuleCat (CommRingCat.of ℂ) := ModuleCat.of ℂ (Fin k →₀ ℂ)
  let e₁ := (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    (tildeFinsupp (R := CommRingCat.of ℂ) (Fin k)).symm
  let e₂ := (tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app M
  exact e₁.toLinearEquiv.trans (e₂.symm.toLinearEquiv.trans
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin k)))

/-- The standard free-sheaf summands give the standard point coordinates.
Source: Hartshorne, Algebraic Geometry, II.5, affine free sheaves. -/
theorem i1_freePointCoordinates_generator (k : ℕ) (i : Fin k) :
    i1_freePointCoordinates k
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        (SheafOfModules.ιFree (R := (Spec ↧ℂ).ringCatSheaf) i)
        (((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
          (ModuleCat.of ℂ ℂ)).hom (1 : ℂ))) = Pi.single i 1 := by
  let G := moduleSpecΓFunctor (R := CommRingCat.of ℂ)
  let η := tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)
  let M : ModuleCat ℂ := ModuleCat.of ℂ (Fin k →₀ ℂ)
  let f : ModuleCat.of ℂ ℂ ⟶ M := ModuleCat.ofHom (Finsupp.lsingle i)
  have hn := ConcreteCategory.congr_hom (η.hom.naturality f) (1 : ℂ)
  change (η.app M).hom (Finsupp.single i 1) =
    G.map ((tilde.functor (CommRingCat.of ℂ)).map f)
      ((η.app (ModuleCat.of ℂ ℂ)).hom (1 : ℂ)) at hn
  rw [← i1_tildeFinsupp_generator k i, Functor.map_comp, ConcreteCategory.comp_apply]
  have hn' := congrArg (fun z => i1_freePointCoordinates k
    (G.map (tildeFinsupp (R := CommRingCat.of ℂ) (Fin k)).hom z)) hn.symm
  apply hn'.trans
  change Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin k)
    ((η.app M).inv ((G.mapIso (tildeFinsupp (R := CommRingCat.of ℂ) (Fin k))).inv
      ((G.mapIso (tildeFinsupp (R := CommRingCat.of ℂ) (Fin k))).hom
        ((η.app M).hom (Finsupp.single i 1))))) = Pi.single i 1
  rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
  ext l
  simp only [Finsupp.linearEquivFunOnFinite_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The specified local frame gives an isomorphism of sheaves on the supplied complex point.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of locally free sheaves. -/
def i1_conormalFramePointIso {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    (Scheme.Modules.pullback x.left).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := (Spec ↧ℂ).ringCatSheaf) (Fin k)) := by
  let a := ComplexPoint.liftToOpen Q U x hx
  letI : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
    (inferInstance : (Scheme.Modules.pushforward a).IsRightAdjoint)
  exact
    ((Scheme.Modules.pullbackComp a U.ι ≪≫
      Scheme.Modules.pullbackCongr (ComplexPoint.liftToOpen_fac Q U x hx)).symm.app _) ≪≫
      (Scheme.Modules.pullback a).mapIso E ≪≫
      SheafOfModules.pullbackObjFreeIso a.toRingCatSheafHom (Fin k)
/-- The scalar coordinate on global sections of the unit sheaf at the complex point.
Source: Hartshorne, Algebraic Geometry, II.5, affine global sections. -/
def i1_unitPointCoordinates :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      (SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf) ≃ₗ[ℂ] ℂ :=
  ((tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app
    (ModuleCat.of ℂ ℂ)).symm.toLinearEquiv

/-- The unit's linear coordinate is the canonical scalar evaluation on affine sections.
Source: Hartshorne, Algebraic Geometry, II.5, affine global sections. -/
theorem i1_unitPointCoordinates_apply
    (v : (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      (SheafOfModules.unit.{0} (Spec ↧ℂ).ringCatSheaf)) :
    i1_unitPointCoordinates v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom v := by
  let η := (tilde.toTildeΓNatIso (R := CommRingCat.of ℂ)).app (ModuleCat.of ℂ ℂ)
  apply η.toLinearEquiv.injective
  have hr : η.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom v) = v :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply v
  exact (η.inv_hom_id_apply v).trans hr.symm

/-- Specialize the specified local conormal frame at the supplied complex point.
Source: Hartshorne, Algebraic Geometry, II.5, pullback of locally free sheaves. -/
def i1_conormalFrameCoordinates {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (U : Q.left.Opens)
    (E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)))
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_conormalFibre j x ≃ₗ[ℂ] (Fin k → ℂ) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).mapIso
    (i1_conormalFramePointIso j k U E x hx)).toLinearEquiv.trans (i1_freePointCoordinates k)

/-- Smooth immersion dimensions give coordinates on each actual conormal fibre.
Source: Hartshorne, Algebraic Geometry, II.8, conormal sequence for smooth immersions. -/
theorem i1_conormalFibre_coordinates_nonempty {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [IsClosedImmersion j] [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV] (x : ComplexPoint Q) :
    Nonempty (i1_conormalFibre j x ≃ₗ[ℂ] (Fin k → ℂ)) := by
  let ι : Q ⟶ Over.mk sV := Over.homMk j hj
  letI : IsClosedImmersion ι.left := ‹IsClosedImmersion j›
  letI : SmoothOfRelativeDimension (k + k) (Over.mk sV).hom :=
    ‹SmoothOfRelativeDimension (k + k) sV›
  obtain ⟨U, hx, ⟨E⟩⟩ :=
    HodgeLean.Foundations.Program.s2e_smooth_closedImmersion_conormal_frames
      Q (Over.mk sV) k k ι x.underlying
  let E' : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k)) :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫ E
  exact ⟨i1_conormalFrameCoordinates j k U E' x hx⟩

/-- Each actual normal fibre has the complex model topology in the expected rank.
Source: Hartshorne, Algebraic Geometry, II.8, normal bundle rank and duality. -/
theorem i1_normalFibre_homeomorph_nonempty {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (k : ℕ) (sV : V ⟶ Spec ↧ℂ) (hj : j ≫ sV = Q.hom)
    [IsClosedImmersion j] [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) sV] (x : ComplexPoint Q) :
    letI := i1_normalFibreTopology j x
    Nonempty (i1_normalFibre j x ≃ₜ (Fin k → ℂ)) := by
  obtain ⟨e⟩ := i1_conormalFibre_coordinates_nonempty j k sV hj x
  exact ⟨i1_normalBasisHomeomorph j x k ((Pi.basisFun ℂ (Fin k)).map e.symm)⟩

end HodgeLean.Foundations.BundleThom
