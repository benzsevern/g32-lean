import HodgeLean.Foundations.Program.SchoenTowerI2aLinearCoordinates
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Data.Set.Restrict
import Mathlib.Data.Set.Finite.Basic

/-! # Affine polynomial coordinates for branch evaluation functions
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Independent translations are automorphisms of the polynomial coordinates.
Source: Mathlib, MvPolynomial.aeval and AlgEquiv.ofAlgHom. -/
def s2v_i2a_coordinateTranslation
    (k : Type*) [CommRing k] (n : ℕ) (b : Fin n → k) :
    MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.C (b i) + MvPolynomial.X i)
    (MvPolynomial.aeval fun i => MvPolynomial.C (- b i) + MvPolynomial.X i)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, map_neg, MvPolynomial.aeval_C,
        AlgHom.id_apply, MvPolynomial.algebraMap_eq, MvPolynomial.C_neg]
      ring)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, map_neg, MvPolynomial.aeval_C,
        AlgHom.id_apply, MvPolynomial.algebraMap_eq, MvPolynomial.C_neg]
      ring)

example (k : Type*) [CommRing k] (n : ℕ) (b : Fin n → k) (i : Fin n) :
    s2v_i2a_coordinateTranslation k n b (MvPolynomial.X i) =
      MvPolynomial.C (b i) + MvPolynomial.X i := MvPolynomial.aeval_X _ _

/-- Evaluations of a generic monic degree-n polynomial at n distinct constants are polynomial coordinates.
Source: Mathlib, Matrix.det_vandermonde_ne_zero_iff and polynomial affine substitutions. -/
theorem s2v_i2a_branch_evaluation_coordinates
    (k : Type*) [Field k] (n : ℕ) (b : Fin n → k) (hb : Function.Injective b) :
    ∃ e : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k,
      ∀ i, e (MvPolynomial.X i) = MvPolynomial.C (b i ^ n) +
        ∑ j : Fin n, MvPolynomial.C (b i ^ (j : ℕ)) * MvPolynomial.X j := by
  have hdet : IsUnit (Matrix.vandermonde b).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hb)
  let linear := s2v_i2a_matrixCoordinateEquiv k n (Matrix.vandermonde b) hdet
  let shift := s2v_i2a_coordinateTranslation k n (fun i => b i ^ n)
  refine ⟨shift.trans linear, ?_⟩
  intro i
  change linear (shift (MvPolynomial.X i)) = _
  rw [show shift (MvPolynomial.X i) = MvPolynomial.C (b i ^ n) + MvPolynomial.X i from
    MvPolynomial.aeval_X _ _]
  rw [map_add]
  have hC : linear (MvPolynomial.C (b i ^ n)) = MvPolynomial.C (b i ^ n) := linear.commutes _
  rw [hC]
  have hX : linear (MvPolynomial.X i) =
      ∑ j, MvPolynomial.C (Matrix.vandermonde b i j) * MvPolynomial.X j :=
    MvPolynomial.aeval_X _ _
  rw [hX]
  rfl

/-- Distinct branch evaluation functions remain simultaneous etale parameters on an actual etale coefficient chart.
Source: Mathlib, RingHom.Etale.stableUnderComposition and s2v_i2a_branch_evaluation_coordinates. -/
theorem s2v_i2a_etale_branch_evaluation_map
    (k R : Type) [Field k] [CommRing R] [Algebra k R]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    (b : Fin n → k) (hb : Function.Injective b) :
    ∃ c' : MvPolynomial (Fin n) k →ₐ[k] R, c'.toRingHom.Etale ∧
      ∀ i, c' (MvPolynomial.X i) = c (MvPolynomial.C (b i ^ n) +
        ∑ j : Fin n, MvPolynomial.C (b i ^ (j : ℕ)) * MvPolynomial.X j) := by
  obtain ⟨e, he⟩ := s2v_i2a_branch_evaluation_coordinates k n b hb
  refine ⟨c.comp e.toAlgHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition e.toRingHom c.toRingHom
      (RingHom.Etale.of_bijective e.bijective) hc
  · intro i
    change c (e (MvPolynomial.X i)) = _
    rw [he]

/-- A finite set of distinct specified branch values extends to distinct values on every chosen coordinate slot.
Source: Mathlib, Set.Finite.infinite_compl and Function.Injective.extend_of_disjoint. -/
theorem s2v_i2a_extend_branch_values
    {k J : Type*} [Infinite k] [Finite J] (n : ℕ)
    (κ : J ↪ Fin n) (b : J → k) (hb : Function.Injective b) :
    ∃ B : Fin n → k, Function.Injective B ∧ ∀ j, B (κ j) = b j := by
  classical
  have hInf : (Set.range b)ᶜ.Infinite := (Set.finite_range b).infinite_compl
  let E : ℕ ↪ ↥((Set.range b)ᶜ) := Set.Infinite.natEmbedding _ hInf
  let filler (i : Fin n) : k := (E i.val).val
  have hfill : Function.Injective filler :=
    Subtype.val_injective.comp (E.injective.comp Fin.val_injective)
  have hdisjoint : Disjoint (Set.range b) (Set.range filler) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨i, rfl⟩
    exact (E i.val).property hz
  refine ⟨Function.extend κ b filler,
    κ.injective.extend_of_disjoint hb hfill hdisjoint, ?_⟩
  intro j
  exact κ.injective.extend_apply b filler j

/-- Prescribed distinct branch evaluations occupy any specified distinct slots of an etale parameter chart.
Source: Mathlib, infinite-field interpolation and s2v_i2a_etale_branch_evaluation_map. -/
theorem s2v_i2a_etale_selected_branch_evaluations
    (k R : Type) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    (n : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale)
    {J : Type} [Finite J] (κ : J ↪ Fin n) (b : J → k) (hb : Function.Injective b) :
    ∃ c' : MvPolynomial (Fin n) k →ₐ[k] R, c'.toRingHom.Etale ∧
      ∀ i, c' (MvPolynomial.X (κ i)) = c (MvPolynomial.C (b i ^ n) +
        ∑ j : Fin n, MvPolynomial.C (b i ^ (j : ℕ)) * MvPolynomial.X j) := by
  obtain ⟨B, hB, hBb⟩ := s2v_i2a_extend_branch_values n κ b hb
  obtain ⟨c', hc', hcoord⟩ := s2v_i2a_etale_branch_evaluation_map k R n c hc B hB
  refine ⟨c', hc', ?_⟩
  intro i
  rw [hcoord, hBb]

end HodgeLean.Foundations.Program
