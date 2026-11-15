import HodgeLean.Foundations.Program.SchoenTowerI2aSymmetricBranchCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1aFlatInsertion

/-! # Principal branch equations on actual invariant parameter algebras
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Reflection of every root coordinate about one scalar is an actual polynomial coordinate automorphism.
Source: Mathlib, MvPolynomial.aeval and AlgEquiv.ofAlgHom. -/
theorem s2v_i2a_reflected_root_coordinates
    (k : Type*) [CommRing k] (n : ℕ) (b : k) :
    ∃ e : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k,
      ∀ i, e (MvPolynomial.X i) = MvPolynomial.C b - MvPolynomial.X i := by
  let f : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k :=
    MvPolynomial.aeval fun i => MvPolynomial.C b - MvPolynomial.X i
  have hX (i : Fin n) : f (MvPolynomial.X i) = MvPolynomial.C b - MvPolynomial.X i :=
    MvPolynomial.aeval_X _ _
  have hff : f.comp f = AlgHom.id k (MvPolynomial (Fin n) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    change f (f (MvPolynomial.X i)) = MvPolynomial.X i
    rw [hX, map_sub, show f (MvPolynomial.C b) = MvPolynomial.C b from f.commutes b,
      hX, sub_sub_cancel]
  refine ⟨AlgEquiv.ofAlgHom f f hff hff, ?_⟩
  exact hX

/-- Every specified branch value has its actual principal contraction equation on an invariant etale root chart.
Source: Schoen (1988), Lemma 2.2; the checked flat insertion-contraction theorem applied to reflected root parameters. -/
theorem s2v_i2a_branch_product_ideal_contraction
    {k B D : Type} [Field k] [CommRing B] [CommRing D] [Algebra k B]
    (n : ℕ) [MulSemiringAction (Equiv.Perm (Fin n)) B]
    [SMulCommClass (Equiv.Perm (Fin n)) k B]
    (z : Fin n → B) (hz : ∀ g : Equiv.Perm (Fin n), ∀ i, g • z i = z (g i))
    (hEt : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (q : D →+* B) (hq : Function.Injective q)
    (himage : ∀ a : B, a ∈ Set.range q ↔ ∀ g : Equiv.Perm (Fin n), g • a = a)
    (b : k) (c : D) (hc : q c = ∏ i, (algebraMap k B b - z i)) (i₀ : Fin n) :
    (Ideal.span {z i₀ - algebraMap k B b}).comap q = Ideal.span {c} := by
  obtain ⟨e, he⟩ := s2v_i2a_reflected_root_coordinates k n b
  have heq : MvPolynomial.aeval (R := k) (fun i => algebraMap k B b - z i) =
      (MvPolynomial.aeval (R := k) z).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply]
    change algebraMap k B b - z i = (MvPolynomial.aeval (R := k) z) (e (MvPolynomial.X i))
    rw [he, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  have hEt' : (MvPolynomial.aeval (R := k) (fun i => algebraMap k B b - z i)).toRingHom.Etale := by
    rw [heq]
    exact RingHom.Etale.stableUnderComposition e.toRingHom
      (MvPolynomial.aeval (R := k) z).toRingHom (RingHom.Etale.of_bijective e.bijective) hEt
  have hflat : letI := (MvPolynomial.aeval (R := k) (fun i => algebraMap k B b - z i)).toRingHom.toAlgebra
      Module.Flat (MvPolynomial (Fin n) k) B := by
    letI : Algebra (MvPolynomial (Fin n) k) B :=
      (MvPolynomial.aeval (R := k) (fun i => algebraMap k B b - z i)).toRingHom.toAlgebra
    letI : Algebra.Etale (MvPolynomial (Fin n) k) B := hEt'
    infer_instance
  have hcov (g : Equiv.Perm (Fin n)) (i : Fin n) :
      g • (algebraMap k B b - z i) = algebraMap k B b - z (g i) := by
    rw [smul_sub, hz]
    congr 1
    exact (MulSemiringAction.toAlgHom k B g).commutes b
  have H := s2v_l1a_flat_insertion_contraction n (fun i => algebraMap k B b - z i)
    hcov hflat q hq himage c hc i₀
  have hspan : Ideal.span {algebraMap k B b - z i₀} =
      Ideal.span {z i₀ - algebraMap k B b} := by
    rw [← neg_sub (z i₀) (algebraMap k B b), Ideal.span_singleton_neg]
  rw [hspan] at H
  exact H

/-- All present distinct branch values have simultaneous etale coordinates, actual principal contraction equations and zero evaluation at the specified quotient point.
Source: Schoen (1988), Lemma 2.2; the checked symmetric branch products and flat insertion-contraction calculation. -/
theorem s2v_i2a_present_symmetric_branch_parameters
    (k B D : Type) [Field k] [Infinite k] [CommRing B] [Nontrivial B]
    [CommRing D] [Algebra k B] [Algebra k D]
    (n : ℕ) [MulSemiringAction (Equiv.Perm (Fin n)) B]
    [SMulCommClass (Equiv.Perm (Fin n)) k B]
    (z : Fin n → B) (hz : ∀ g : Equiv.Perm (Fin n), ∀ i, g • z i = z (g i))
    (hRootEt : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (c : MvPolynomial (Fin n) k →ₐ[k] D) (hcEt : c.toRingHom.Etale)
    (q : D →ₐ[k] B) (hq : Function.Injective q)
    (himage : ∀ a : B, a ∈ Set.range q ↔ ∀ g : Equiv.Perm (Fin n), g • a = a)
    (hc : ∀ j, q (c (MvPolynomial.X j)) =
      MvPolynomial.aeval (R := k) z (MvPolynomial.esymm (Fin n) k (j.val + 1)))
    (φ : B →ₐ[k] k) {J : Type} [Finite J] (b : J → k) (hb : Function.Injective b)
    (hpresent : ∀ j, ∃ i, φ (z i) = b j) (i₀ : Fin n) :
    ∃ (κ : J ↪ Fin n) (cBranch : MvPolynomial (Fin n) k →ₐ[k] D),
      cBranch.toRingHom.Etale ∧ (∀ j, φ (z (κ j)) = b j) ∧
      ∀ j, (Ideal.span {z i₀ - algebraMap k B (b j)}).comap q.toRingHom =
          Ideal.span {cBranch (MvPolynomial.X (κ j))} ∧
        φ (q (cBranch (MvPolynomial.X (κ j)))) = 0 := by
  obtain ⟨κ, hκ⟩ := s2v_i2a_present_branch_slots n (fun i => φ (z i)) b hb hpresent
  obtain ⟨cBranch, hcBranchEt, hproduct⟩ :=
    s2v_i2a_etale_symmetric_branch_products k B D n c hcEt q z hc κ b hb
  refine ⟨κ, cBranch, hcBranchEt, hκ, ?_⟩
  intro j
  constructor
  · exact s2v_i2a_branch_product_ideal_contraction n z hz hRootEt q.toRingHom hq
      himage (b j) (cBranch (MvPolynomial.X (κ j))) (hproduct j) i₀
  · rw [hproduct, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (κ j))
    have hscalar : φ (algebraMap k B (b j)) = b j := φ.commutes (b j)
    rw [map_sub, hscalar, hκ, sub_self]

end HodgeLean.Foundations.Program
