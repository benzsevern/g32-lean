import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleCoefficients

/-! # Univariate etale parameter transport

Implication from the actual coefficient-ring polynomial chart to the
corresponding one-variable complex polynomial chart.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Polynomial evaluation is etale after identifying a one-element variable set
with the univariate polynomial ring.
Source: Hartshorne, Algebraic Geometry, III.10, invariance under isomorphism. -/
theorem s2v_l1a_univariate_eval_etale
    {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
    (z : A) (h : (MvPolynomial.eval₂Hom (algebraMap K A)
      (fun _ : Fin 1 => z)).Etale) :
    (Polynomial.aeval (R := K) z).toRingHom.Etale := by
  let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  have heq : (Polynomial.aeval (R := K) z).toRingHom =
      (MvPolynomial.eval₂Hom (algebraMap K A) (fun _ : Fin 1 => z)).comp
        e.symm.toRingHom := by
    apply RingHom.ext
    intro p
    exact (MvPolynomial.eval₂_uniqueAlgEquiv_symm
      (R := K) (σ := Fin 1) (φ := algebraMap K A) (a := fun _ => z)).symm
  rw [heq]
  exact RingHom.Etale.respectsIso.2 _ e.symm.toRingEquiv h

/-- Reversing a coefficient identification preserves etaleness of the actual evaluation map.
Source: Hartshorne, Algebraic Geometry, III.10, invariance under isomorphism. -/
theorem s2v_l1a_etale_eval_change_coefficients_iff
    {R R' A ι : Type} [CommRing R] [CommRing R'] [CommRing A]
    (e : R' ≃+* R) (b : R →+* A) (z : ι → A) :
    (MvPolynomial.eval₂Hom (b.comp e.toRingHom) z).Etale ↔
      (MvPolynomial.eval₂Hom b z).Etale := by
  constructor
  · intro h
    have H := s2v_l1a_etale_eval_change_coefficients e.symm (b.comp e.toRingHom) z h
    have heq : (b.comp e.toRingHom).comp e.symm.toRingHom = b := by
      ext r
      exact congrArg b (e.apply_symm_apply r)
    rw [heq] at H
    exact H
  · exact s2v_l1a_etale_eval_change_coefficients e b z

end HodgeLean.Foundations.Program
