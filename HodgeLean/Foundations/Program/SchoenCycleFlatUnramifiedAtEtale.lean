import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Flat.Localization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TensorProduct IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Flatness and unramifiedness at the actual prime localization of a finitely presented algebra give étaleness at that prime.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.6.1. -/
theorem s2e_isEtaleAt_of_flat_unramified_localization
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)]
    [Algebra.FormallyUnramified R (Localization.AtPrime q)] : Algebra.IsEtaleAt R q := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  letI : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
    (M := Algebra.algebraMapSubmonoid S p.primeCompl) (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      exact IsLocalization.map_units (M := q.primeCompl) Sq
        ⟨algebraMap R S x, by exact hx⟩)
  algebraize [f.toRingHom]
  letI : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  letI : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq])
  letI : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _ (by
      rintro _ ⟨x, hx, rfl⟩
      exact hx)
  letI : Algebra.FinitePresentation Rp Sp := by
    letI : Algebra.IsPushout R Rp S Sp :=
      .symm (Algebra.isPushout_of_isLocalization p.primeCompl _ _ _)
    exact Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv R Rp S Sp)
  letI : Module.Flat Rp Sq := (Module.flat_iff_of_isLocalization Rp p.primeCompl Sq).mpr inferInstance
  letI : Algebra.FormallyUnramified Rp Sq := .of_restrictScalars R Rp Sq
  letI : Algebra.EssFiniteType Sp Sq :=
    Algebra.EssFiniteType.of_isLocalization Sq (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  letI : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.comp Rp Sp Sq
  letI : Algebra.FormallyEtale (ResidueField Rp) (ResidueField Rp ⊗[Rp] Sq) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  letI : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (R := Rp) (S := Sq) (P := Sp) (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  letI : Algebra.FormallySmooth R Sq := .comp R Rp Sq
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

#print axioms s2e_isEtaleAt_of_flat_unramified_localization
end HodgeLean.Foundations.Program
