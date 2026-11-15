import HodgeLean.Foundations.Program.SchoenCycleCoefficientBranch
import HodgeLean.Foundations.Program.SchoenCycleSymmetricBranchAlgebra

/-! # Scheme image ideals in affine coefficient coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open Scheme.IdealSheafData
namespace HodgeLean.Foundations.Program

/-- On affine spectra the scheme image ideal is the transported ring kernel.
Source: Mathlib, AlgebraicGeometry.Scheme.ker_of_isAffine and
AlgebraicGeometry.Scheme.ΓSpecIso_naturality. -/
theorem s2e_spec_map_image_ideal (R S : CommRingCat) (φ : R ⟶ S) :
    (Spec.map φ).ker = ofIdealTop
      ((RingHom.ker φ.hom).comap (Scheme.ΓSpecIso R).hom.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality]
  rfl

/-- The ring kernel of marked-root insertion is the single top coefficient ideal.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, symmetric products and divisors. -/
theorem s2e_symmetric_marked_root_kernel
    (σ : Type) [Fintype σ] (i : σ) :
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X i : MvPolynomial σ ℂ)})).comp
      (MvPolynomial.symmetricSubalgebra σ ℂ).val.toRingHom) =
    Ideal.span {(⟨MvPolynomial.esymm σ ℂ (Fintype.card σ),
      MvPolynomial.esymm_isSymmetric σ ℂ _⟩ : MvPolynomial.symmetricSubalgebra σ ℂ)} := by
  change (RingHom.ker (Ideal.Quotient.mk _)).comap _ = _
  rw [Ideal.mk_ker]
  exact s2e_symmetric_marked_root_ideal σ i

/-- The affine marked-root scheme image has the top coefficient ideal, with its scheme structure.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, symmetric products and divisors;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15. -/
theorem s2e_affine_symmetric_marked_image_ideal
    (σ : Type) [Fintype σ] (i : σ) :
    let J : Ideal (MvPolynomial σ ℂ) := Ideal.span {(MvPolynomial.X i : MvPolynomial σ ℂ)}
    let φ : MvPolynomial.symmetricSubalgebra σ ℂ →+* (MvPolynomial σ ℂ ⧸ J) :=
      (Ideal.Quotient.mk J).comp (MvPolynomial.symmetricSubalgebra σ ℂ).val.toRingHom
    (Spec.map (CommRingCat.ofHom φ)).ker = ofIdealTop
      ((Ideal.span {(⟨MvPolynomial.esymm σ ℂ (Fintype.card σ),
        MvPolynomial.esymm_isSymmetric σ ℂ _⟩ : MvPolynomial.symmetricSubalgebra σ ℂ)}).comap
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.symmetricSubalgebra σ ℂ))).hom.hom) := by
  dsimp only
  simp only [s2e_spec_map_image_ideal, CommRingCat.hom_ofHom,
    s2e_symmetric_marked_root_kernel]

/-- Marked-root insertion has the top coefficient kernel over every coefficient ring.
Source: Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Chapter I, §2. -/
theorem s2e_symmetric_marked_root_kernel_over_ring
    (R σ : Type) [CommRing R] [Fintype σ] (i : σ) :
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X i : MvPolynomial σ R)})).comp
      (MvPolynomial.symmetricSubalgebra σ R).val.toRingHom) =
    Ideal.span {(⟨MvPolynomial.esymm σ R (Fintype.card σ),
      MvPolynomial.esymm_isSymmetric σ R _⟩ : MvPolynomial.symmetricSubalgebra σ R)} := by
  change (RingHom.ker (Ideal.Quotient.mk _)).comap _ = _
  rw [Ideal.mk_ker]
  exact s2e_symmetric_root_ideal_over_ring R σ i

end HodgeLean.Foundations.Program
