import HodgeLean.Foundations.Program.SchoenCycleLocalFormalJetRepresentatives
import HodgeLean.Foundations.Program.SchoenCycleLocalAdicCotangent
import Mathlib.LinearAlgebra.Basis.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A formal cotangent basis has simultaneous actual local-ring representatives to every prescribed order at least two, retaining its cotangent basis.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Chapter 10. -/
theorem s2e_formal_cotangent_basis_representatives
    {k R σ : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R]
    (K : ℕ) (hK : 2 ≤ K)
    (B : Module.Basis σ k
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)).Cotangent)
    (z : σ → AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (hz : ∀ i, z i ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (hB : ∀ i, B i = (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)).toCotangent
      ⟨z i, hz i⟩) :
    ∃ (r : σ → R) (hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R)
      (D : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent),
      (∀ i, D i = (IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩) ∧
      ∀ i, AdicCompletion.of (IsLocalRing.maximalIdeal R) R (r i) - z i ∈
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ K := by
  classical
  let I := IsLocalRing.maximalIdeal R
  let A := AdicCompletion I R
  let J := IsLocalRing.maximalIdeal A
  choose r herr using fun i => s2e_local_formal_jet_representative R K (z i)
  have he2 (i : σ) : AdicCompletion.of I R (r i) - z i ∈ J ^ 2 :=
    Ideal.pow_le_pow_right hK (herr i)
  have hrA (i : σ) : AdicCompletion.of I R (r i) ∈ J := by
    have hh := J.add_mem (Ideal.pow_le_self (by decide : (2 : ℕ) ≠ 0) (he2 i)) (hz i)
    simpa only [sub_add_cancel] using hh
  have hr (i : σ) : r i ∈ I := by
    change r i ∈ IsLocalRing.maximalIdeal R
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap R A)]
    exact hrA i
  let F := s2e_local_adic_cotangent_equiv (k := k) (R := R)
  refine ⟨r, hr, B.map F.symm, ?_, herr⟩
  intro i
  apply F.injective
  rw [Module.Basis.map_apply, F.apply_symm_apply, hB]
  change J.toCotangent ⟨z i, hz i⟩ = J.toCotangent ⟨AdicCompletion.of I R (r i), hrA i⟩
  apply J.toCotangent_eq.mpr
  simpa only [neg_sub] using (J ^ 2).neg_mem (he2 i)

#print axioms s2e_formal_cotangent_basis_representatives
end HodgeLean.Foundations.Program
