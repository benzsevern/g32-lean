import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.RingHom.Etale

/-! A differential criterion for changing an etale coordinate family.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program
open Algebra KaehlerDifferential

/-- Over a formally smooth base algebra, a bijective differential base-change map makes the relative algebra formally etale. -/
theorem s2v_l1b_formallyEtale_of_bijective_differentials
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hΩ : ∀ x : Ω[T⁄S], x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R S T x
    obtain ⟨z, rfl⟩ := h.surjective y
    exact (KaehlerDifferential.exact_mapBaseChange_map R S T).apply_apply_eq_zero z
  have hH : ∀ x : H1Cotangent S T, x = 0 := by
    intro x
    have hδ : H1Cotangent.δ R S T x = 0 := by
      apply h.injective
      rw [map_zero]
      exact (H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero x
    obtain ⟨y, hy⟩ := (H1Cotangent.exact_map_δ R S T x).mp hδ
    rw [← hy, Subsingleton.elim y 0, map_zero]
  exact ⟨⟨fun x y => (hΩ x).trans (hΩ y).symm⟩,
    ⟨fun x y => (hH x).trans (hH y).symm⟩⟩

/-- A basis consisting of the chosen polynomial coordinate differentials gives formal etaleness of that coordinate map. -/
theorem s2v_l1b_formallyEtale_of_coordinate_basis
    (R T ι : Type*) [CommRing R] [CommRing T]
    [Algebra R T] [Algebra (MvPolynomial ι R) T]
    [IsScalarTower R (MvPolynomial ι R) T] [Algebra.FormallySmooth R T]
    (b : Module.Basis ι T Ω[T⁄R])
    (hb : ∀ i, b i = D R T (algebraMap (MvPolynomial ι R) T (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) T := by
  let B := (KaehlerDifferential.mvPolynomialBasis R ι).baseChange T
  let e := B.equiv b (Equiv.refl ι)
  have he : KaehlerDifferential.mapBaseChange R (MvPolynomial ι R) T = e.toLinearMap := by
    apply B.ext
    intro i
    change KaehlerDifferential.mapBaseChange R (MvPolynomial ι R) T (B i) = e (B i)
    rw [show e (B i) = b i from B.equiv_apply i b (Equiv.refl ι)]
    rw [hb i]
    change KaehlerDifferential.mapBaseChange R (MvPolynomial ι R) T
      (((KaehlerDifferential.mvPolynomialBasis R ι).baseChange T) i) = _
    rw [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, one_smul]
  apply s2v_l1b_formallyEtale_of_bijective_differentials R (MvPolynomial ι R) T
  rw [he]
  exact e.bijective

/-- Finite presentation upgrades the coordinate differential basis criterion to etaleness. -/
theorem s2v_l1b_etale_of_coordinate_basis
    (R T ι : Type*) [CommRing R] [CommRing T]
    [Algebra R T] [Algebra (MvPolynomial ι R) T]
    [IsScalarTower R (MvPolynomial ι R) T] [Algebra.FormallySmooth R T]
    [Algebra.FinitePresentation (MvPolynomial ι R) T]
    (b : Module.Basis ι T Ω[T⁄R])
    (hb : ∀ i, b i = D R T (algebraMap (MvPolynomial ι R) T (MvPolynomial.X i))) :
    Algebra.Etale (MvPolynomial ι R) T := by
  exact ⟨s2v_l1b_formallyEtale_of_coordinate_basis R T ι b hb, inferInstance⟩

/-- An invertible coordinate differential determinant suffices for etaleness of the specified polynomial map. -/
theorem s2v_l1b_etale_of_unit_differential_determinant
    (R T ι : Type*) [CommRing R] [CommRing T] [Fintype ι] [DecidableEq ι]
    [Algebra R T] [Algebra (MvPolynomial ι R) T]
    [IsScalarTower R (MvPolynomial ι R) T] [Algebra.FormallySmooth R T]
    [Algebra.FinitePresentation (MvPolynomial ι R) T]
    (b : Module.Basis ι T Ω[T⁄R])
    (hdet : IsUnit (b.det (fun i =>
      D R T (algebraMap (MvPolynomial ι R) T (MvPolynomial.X i))))) :
    Algebra.Etale (MvPolynomial ι R) T := by
  obtain ⟨hli, hspan⟩ := b.is_basis_iff_det.mpr hdet
  let b' := Module.Basis.mk hli hspan.ge
  exact s2v_l1b_etale_of_coordinate_basis R T ι b' (fun i => Module.Basis.mk_apply _ _ i)

/-- An invertible differential determinant verifies the actual polynomial evaluation homomorphism on a smooth finitely presented algebra. -/
theorem s2v_l1b_evaluation_etale_of_unit_differential_determinant
    {R T ι : Type*} [CommRing R] [CommRing T] [Fintype ι] [DecidableEq ι]
    [Algebra R T] [Algebra.Smooth R T]
    (c : ι → T) (b : Module.Basis ι T Ω[T⁄R])
    (hdet : IsUnit (b.det (fun i => D R T (c i)))) :
    (MvPolynomial.aeval (R := R) c).toRingHom.Etale := by
  let f := (MvPolynomial.aeval (R := R) c).toRingHom
  letI : Algebra (MvPolynomial ι R) T := f.toAlgebra
  letI : IsScalarTower R (MvPolynomial ι R) T :=
    .of_algebraMap_eq fun r => by
      simp only [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq,
        f, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
  letI : Algebra.FinitePresentation (MvPolynomial ι R) T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) T
  apply (RingHom.etale_algebraMap).mpr
  apply s2v_l1b_etale_of_unit_differential_determinant R T ι b
  simpa only [RingHom.algebraMap_toAlgebra, f, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.aeval_X] using hdet

end HodgeLean.Foundations.Program
