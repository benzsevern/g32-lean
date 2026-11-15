import HodgeLean.Foundations.Program.SchoenTowerL1aFlatInsertion
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.RingHom.Etale

/-! # Translated ordered parameters for simultaneous branch equations
Translations retain the parameter map and its exact invariant contraction.
HC no distance; AV milestone no distance.
-/

noncomputable section
open MvPolynomial
namespace HodgeLean.Foundations.Program
universe u

/-- Translating every polynomial variable by its chosen scalar is an automorphism. -/
theorem s2v_l1b_translation_coordinates {K ι : Type*} [CommRing K] (a : ι → K) :
    ∃ e : MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K,
      ∀ i, e (X i) = X i - C (a i) := by
  let F : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
    aeval (fun i => X i - C (a i))
  let G : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
    aeval (fun i => X i + C (a i))
  have hFG : F.comp G = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change F (G (X i)) = X i
    simp only [F, G, aeval_X, map_add, aeval_C, algebraMap_eq, sub_add_cancel]
  have hGF : G.comp F = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change G (F (X i)) = X i
    simp only [F, G, aeval_X, map_sub, aeval_C, algebraMap_eq, add_sub_cancel_right]
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, fun i => MvPolynomial.aeval_X _ i⟩

/-- Scalar translations preserve etaleness of the ordered parameter map. -/
theorem s2v_l1b_translation_etale {K B : Type u} {ι : Type} [CommRing K] [CommRing B]
    [Algebra K B] (z : ι → B) (a : ι → K)
    (hEt : (MvPolynomial.aeval (R := K) z).toRingHom.Etale) :
    (MvPolynomial.aeval (R := K) (fun i => z i - algebraMap K B (a i))).toRingHom.Etale := by
  obtain ⟨e, he⟩ := s2v_l1b_translation_coordinates a
  have H := RingHom.Etale.stableUnderComposition e.toRingEquiv.toRingHom
    (MvPolynomial.aeval (R := K) z).toRingHom
    (RingHom.Etale.of_bijective e.bijective) hEt
  have hcomp : (MvPolynomial.aeval (R := K) z).comp e.toAlgHom =
      MvPolynomial.aeval (R := K) (fun i => z i - algebraMap K B (a i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change MvPolynomial.aeval z (e (X i)) = _
    rw [he]
    simp only [map_sub, aeval_X, aeval_C]
  exact congrArg AlgHom.toRingHom hcomp ▸ H

/-- The equation for any scalar branch value contracts to the descended product in the same invariant chart. -/
theorem s2v_l1b_translated_insertion_contraction
    {K B D : Type u} [Field K] [CommRing B] [CommRing D] [Algebra K B]
    (n : ℕ) [MulSemiringAction (Equiv.Perm (Fin n)) B]
    [SMulCommClass (Equiv.Perm (Fin n)) K B]
    (z : Fin n → B) (hz : ∀ g : Equiv.Perm (Fin n), ∀ i, g • z i = z (g i))
    (hEt : (MvPolynomial.aeval (R := K) z).toRingHom.Etale)
    (q : D →+* B) (hq : Function.Injective q)
    (himage : ∀ b : B, b ∈ Set.range q ↔ ∀ g : Equiv.Perm (Fin n), g • b = b)
    (a : K) (c : D) (hc : q c = ∏ i, (z i - algebraMap K B a)) (i₀ : Fin n) :
    (Ideal.span {z i₀ - algebraMap K B a}).comap q = Ideal.span {c} := by
  have ht := s2v_l1b_translation_etale z (fun _ => a) hEt
  let w := fun i => z i - algebraMap K B a
  have hw : ∀ g : Equiv.Perm (Fin n), ∀ i, g • w i = w (g i) := by
    intro g i
    simp only [w, smul_sub, hz, smul_algebraMap]
  have hflat : letI := (MvPolynomial.aeval (R := K) w).toRingHom.toAlgebra
      Module.Flat (MvPolynomial (Fin n) K) B := by
    letI := (MvPolynomial.aeval (R := K) w).toRingHom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mp
      ((RingHom.Etale.iff_flat_and_formallyUnramified.mp ht).1)
  exact s2v_l1a_flat_insertion_contraction n w hw hflat q hq himage c hc i₀

/-- Every scalar value has a unique descended branch product, with all insertion contractions in one chart. -/
theorem s2v_l1b_translated_branch_descent
    {K B D : Type u} [Field K] [CommRing B] [CommRing D] [Algebra K B]
    (n : ℕ) [MulSemiringAction (Equiv.Perm (Fin n)) B]
    [SMulCommClass (Equiv.Perm (Fin n)) K B]
    (z : Fin n → B) (hz : ∀ g : Equiv.Perm (Fin n), ∀ i, g • z i = z (g i))
    (hEt : (MvPolynomial.aeval (R := K) z).toRingHom.Etale)
    (q : D →+* B) (hq : Function.Injective q)
    (himage : ∀ b : B, b ∈ Set.range q ↔ ∀ g : Equiv.Perm (Fin n), g • b = b)
    (a : K) :
    ∃! c : D, q c = ∏ i, (z i - algebraMap K B a) ∧
      ∀ i : Fin n, (Ideal.span {z i - algebraMap K B a}).comap q = Ideal.span {c} := by
  have hfix : ∀ g : Equiv.Perm (Fin n),
      g • (∏ i, (z i - algebraMap K B a)) = ∏ i, (z i - algebraMap K B a) := by
    intro g
    rw [Finset.smul_prod']
    simp_rw [smul_sub, hz, smul_algebraMap]
    exact Equiv.prod_comp g (fun i => z i - algebraMap K B a)
  obtain ⟨c, hc⟩ := (himage _).mpr hfix
  refine ⟨c, ⟨hc, ?_⟩, ?_⟩
  · intro i
    exact s2v_l1b_translated_insertion_contraction n z hz hEt q hq himage a c hc i
  · intro c' hc'
    exact hq (hc'.1.trans hc.symm)

end HodgeLean.Foundations.Program
