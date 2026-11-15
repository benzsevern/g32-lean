import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateEliminationKernel
import HodgeLean.Foundations.Program.SchoenCycleS3AffineIdealCotangent
import HodgeLean.Foundations.Program.SchoenCycleS3ConormalIsoTransport

/-! # Actual conormal frames for affine coordinate elimination -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The actual quotient immersion has its labelled discarded-coordinate frame. -/
def pairedC3CoordinateEliminationQuotientFrame {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    let I := RingHom.ker (MvPolynomial.killCompl (R := A) e.injective).toRingHom
    let Q := CommRingCat.of (MvPolynomial ι A ⧸ I)
    s2c_conormal (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      (SheafOfModules.free (R := (Spec Q).ringCatSheaf) {j : ι // j ∉ Set.range e} :
        (Spec Q).Modules) := by
  dsimp only
  rw [paired_c3_coordinate_elimination_kernel]
  exact s2e_affineQuotientConormalIso (R := CommRingCat.of (MvPolynomial ι A)) _ ≪≫
    (tilde.functor _).mapIso (pairedC3CoordinateEliminationConormalBasis (A := A) e).repr.toModuleIso ≪≫
      tildeFinsupp _

/-- Coordinate elimination is surjective through its original renaming section. -/
theorem paired_c3_coordinate_elimination_surjective {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    Function.Surjective (MvPolynomial.killCompl (R := A) e.injective) :=
  fun p => ⟨MvPolynomial.rename e p, MvPolynomial.killCompl_rename_app e.injective p⟩

/-- The original affine projection, with its original source spectrum,
has the actual discarded-coordinate conormal frame. -/
def pairedC3CoordinateEliminationConormalFrame {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    s2c_conormal (Spec.map (CommRingCat.ofHom
      (MvPolynomial.killCompl (R := A) e.injective).toRingHom)) ≅
      (SheafOfModules.free (R := (Spec (CommRingCat.of (MvPolynomial κ A))).ringCatSheaf)
        {j : ι // j ∉ Set.range e} : (Spec (CommRingCat.of (MvPolynomial κ A))).Modules) := by
  let φ := MvPolynomial.killCompl (R := A) e.injective
  let I := RingHom.ker φ.toRingHom
  let E := Ideal.quotientKerAlgEquivOfSurjective (paired_c3_coordinate_elimination_surjective (A := A) e)
  let h : Spec (CommRingCat.of (MvPolynomial κ A)) ≅ Spec (CommRingCat.of (MvPolynomial ι A ⧸ I)) :=
    asIso (Spec.map E.toRingEquiv.toCommRingCatIso.hom)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have he : h.hom ≫ q = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    change Spec.map E.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = _
    rw [← Spec.map_comp]
    congr 1
  exact eqToIso (congrArg s2c_conormal he.symm) ≪≫
    (s2e_sourceIsoConormalIso h.hom q).symm ≪≫
    (Scheme.Modules.pullback h.hom).mapIso (pairedC3CoordinateEliminationQuotientFrame (A := A) e) ≪≫
      SheafOfModules.pullbackObjFreeIso h.hom.toRingCatSheafHom _

end HodgeLean.Foundations.Program.G32Native
