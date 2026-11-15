import HodgeLean.Ported.Hironaka.Algebra.Proj.BaseChange
import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace

/-! # The native polynomial Proj and the retained projective scheme -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The native polynomial Proj is the same projective scheme over any ring. -/
def pairedNativeProjectiveIso (R : Type) [CommRing R] (k : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) ≅
      ProjectiveSpace (Fin (k + 1)) (Spec (.of R)) := by
  letI : Algebra (ULift.{0} ℤ) R :=
    ((Int.castRingHom R).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  let e := specULiftZIsTerminal.uniqueUpToIso (terminalIsTerminal : IsTerminal (⊤_ Scheme))
  have h := Proj.isPullback_projMap (Fin (k + 1)) (ULift.{0} ℤ) R
  have h' : IsPullback (Proj.projToSpec (Fin (k + 1)) R)
      (Proj.projMap (Fin (k + 1)) (ULift.{0} ℤ) R)
      (terminal.from (Spec (.of R)))
      (terminal.from (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1))
        (ULift.{0} ℤ)))) := by
    apply h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · apply terminalIsTerminal.hom_ext
    · apply terminalIsTerminal.hom_ext
  exact h'.isoPullback

/-- The identification retains the original structural projection to the base. -/
theorem pairedNativeProjectiveIso_toBase (R : Type) [CommRing R] (k : ℕ) :
    (pairedNativeProjectiveIso R k).hom ≫ ProjectiveSpace.toBase (Fin (k + 1))
      (Spec (.of R)) = Proj.projToSpec (Fin (k + 1)) R := by
  simp only [pairedNativeProjectiveIso, ProjectiveSpace.toBase,
    IsPullback.isoPullback_hom_fst]

/-- The same identification retains the integral homogeneous-coordinate map. -/
theorem pairedNativeProjectiveIso_snd (R : Type) [CommRing R] (k : ℕ) :
    letI : Algebra (ULift.{0} ℤ) R :=
      ((Int.castRingHom R).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
    (pairedNativeProjectiveIso R k).hom ≫
      pullback.snd (terminal.from (Spec (.of R)))
        (terminal.from (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1))
          (ULift.{0} ℤ)))) = Proj.projMap (Fin (k + 1)) (ULift.{0} ℤ) R := by
  simp only [pairedNativeProjectiveIso, IsPullback.isoPullback_hom_snd]

/-- Every specified coordinate chart pulls back to the same native coordinate
chart under the actual projective identification. -/
theorem pairedNativeProjectiveIso_coordinateOpen (R : Type) [CommRing R] (k : ℕ)
    (j : Fin (k + 1)) :
    (pairedNativeProjectiveIso R k).hom ⁻¹ᵁ
      (pullback.snd (terminal.from (Spec (.of R)))
        (terminal.from (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1))
          (ULift.{0} ℤ)))) ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) (ULift.{0} ℤ))
            (MvPolynomial.X j)) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R) (MvPolynomial.X j) := by
  letI : Algebra (ULift.{0} ℤ) R :=
    ((Int.castRingHom R).comp (ULift.ringEquiv (R := ℤ)).toRingHom).toAlgebra
  rw [← Scheme.Hom.comp_preimage, pairedNativeProjectiveIso_snd R k]
  simp only [Proj.projMap, Proj.map_preimage_basicOpen, Proj.gradedMap_X]

end HodgeLean.Foundations.Program.G32Native
