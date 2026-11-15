import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.RingHom.Etale

/-! # Etale polynomial coordinates under coefficient identification

The polynomial evaluation map respects the actual coefficient-ring isomorphism.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program
universe u

/-- Changing the coefficient ring by an actual ring isomorphism preserves etaleness of polynomial evaluation.
Source: Hartshorne, Algebraic Geometry, III.10, etaleness under isomorphism. -/
theorem s2v_l1a_etale_eval_change_coefficients
    {R R' A ι : Type u} [CommRing R] [CommRing R'] [CommRing A]
    (e : R' ≃+* R) (b : R →+* A) (z : ι → A)
    (h : (MvPolynomial.eval₂Hom b z).Etale) :
    (MvPolynomial.eval₂Hom (b.comp e.toRingHom) z).Etale := by
  have heq : MvPolynomial.eval₂Hom (b.comp e.toRingHom) z =
      (MvPolynomial.eval₂Hom b z).comp (MvPolynomial.mapEquiv ι e).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp
  rw [heq]
  exact RingHom.Etale.respectsIso.2 _ (MvPolynomial.mapEquiv ι e) h

/-- Etale ring maps compose through their actual coefficient and target rings.
Source: Hartshorne, Algebraic Geometry, III.10, composition of etale morphisms. -/
theorem s2v_l1a_etale_ringHom_comp
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (g : S →+* A) (hf : f.Etale) (hg : g.Etale) :
    (g.comp f).Etale := by
  rw [RingHom.etale_iff_formallyUnramified_and_smooth] at hf hg ⊢
  exact ⟨hf.1.comp hg.1, hf.2.comp hg.2⟩

end HodgeLean.Foundations.Program
