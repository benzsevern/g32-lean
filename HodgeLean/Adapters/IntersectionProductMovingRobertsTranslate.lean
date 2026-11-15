import HodgeLean.Adapters.IntersectionProductMovingRobertsMain

/-! # General translates and generic secants

Two dimension counts by the linear incidence bound `a3r_generic_linear`:
* `a3r_generic_secant`: for a generic projection `ℓ`, pairs `(w, z) ∈ W × Z` off the diagonal
  with `ℓ(w) = ℓ(z)` have dimension at most `dim W + dim Z - (n + 1)` (affine cones), the secant
  hypothesis of Roberts' main lemma;
* `a3r_generic_translate`: for a generic matrix `M`, every relevant point of `W ∩ M⁻¹(C)` has
  dimension at most `dim C + dim W - (N + 1)`: a general translate of a cone meets `W` properly
  (Kleiman's transversality theorem, dimension part, for the action of matrices on `𝔸^{N+1}`).

Source: Kleiman, *The transversality of a general translate*, Compositio Math. 28 (1974),
287–297, Theorem 2; J. Roberts, *Chow's moving lemma* (1972), proof of the Main Lemma.
HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial TensorProduct

namespace HodgeLean.Adapters

/-- A tensor product of finite-type `ℂ`-algebras is of finite type. -/
instance a3r_finiteType_tensor {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra.FiniteType ℂ A] [Algebra.FiniteType ℂ B] : Algebra.FiniteType ℂ (A ⊗[ℂ] B) :=
  Algebra.FiniteType.trans (S := A) inferInstance inferInstance

section Translate

variable {ρ σ : Type} [Fintype ρ] [Fintype σ] [DecidableEq σ]

/-- For generic `ℓ`, pairs of points of `V(P_W) × V(P_Z)` off the diagonal with the same
projection have the expected dimension: the secant hypothesis of `a3r_roberts_main`. -/
theorem a3r_generic_secant (PW PZ : Ideal (MvPolynomial σ ℂ)) :
    a3r_Generic {a : ρ × σ → ℂ | ∀ (j : σ)
      (𝔓 : Ideal ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ))),
      𝔓.IsPrime → a3r_δD PW PZ j ∉ 𝔓 →
      (∀ i, ∑ k, algebraMap ℂ _ (a3r_mat a i k) * a3r_δD PW PZ k - 0 ∈ 𝔓) →
      ringKrullDim (_ ⧸ 𝔓) + Fintype.card ρ ≤
        ringKrullDim ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ))} := by
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ PW) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ PZ) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  exact (a3r_generic_iInter_fintype _ fun j => a3r_generic_linear (ρ := ρ)
    ((MvPolynomial σ ℂ ⧸ PW) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PZ)) (a3r_δD PW PZ) 0 j).mono
    fun a ha j 𝔓 h𝔓 hj heq => ha j 𝔓 h𝔓 hj heq

/-- Transversality of a general translate, as a dimension count: for a generic matrix `M`, every
relevant point of `W ∩ M⁻¹(C)` has dimension at most `dim C + dim W - dim ℙᴺ` (affine cone
dimensions).
Source: Kleiman, *The transversality of a general translate*, Compositio Math. 28 (1974), 287–297,
Theorem 2 (dimension part, valid in every characteristic); Hartshorne, *Algebraic Geometry*, III,
Theorem 10.8. -/
theorem a3r_generic_translate (IC PW : Ideal (MvPolynomial σ ℂ)) [IC.IsPrime] [PW.IsPrime] :
    a3r_Generic {a : σ × σ → ℂ | ∀ Q : Ideal (MvPolynomial σ ℂ), Q.IsPrime → PW ≤ Q →
      (∀ F ∈ IC, a3r_lin (a3r_mat a) F ∈ Q) → ∀ j, X j ∉ Q →
      ringKrullDim (MvPolynomial σ ℂ ⧸ Q) + Fintype.card σ ≤
        ringKrullDim (MvPolynomial σ ℂ ⧸ IC) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW)} := by
  classical
  set D := (MvPolynomial σ ℂ ⧸ IC) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PW)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ IC) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ PW) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  refine (a3r_generic_iInter_fintype _ fun j => a3r_generic_linear (ρ := σ) D
    (fun k => 1 ⊗ₜ Ideal.Quotient.mk PW (X k)) (fun i => Ideal.Quotient.mk IC (X i) ⊗ₜ 1) j).mono
    fun a ha Q hQ hWQ hCQ j hj => ?_
  -- the point of the incidence algebra
  have hle : IC ≤ Ideal.comap (a3r_lin (a3r_mat a)) Q := fun F hF => hCQ F hF
  let θ₁ : MvPolynomial σ ℂ ⧸ IC →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q := Ideal.quotientMapₐ Q _ hle
  let θ₂ : MvPolynomial σ ℂ ⧸ PW →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q := Ideal.Quotient.factorₐ ℂ hWQ
  let Θ : D →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q :=
    Algebra.TensorProduct.lift θ₁ θ₂ fun _ _ => Commute.all _ _
  have hΘ1 : ∀ F, Θ (Ideal.Quotient.mk IC F ⊗ₜ 1) =
      Ideal.Quotient.mk Q (a3r_lin (a3r_mat a) F) := by
    intro F
    change θ₁ (Ideal.Quotient.mk IC F) * θ₂ 1 = _
    rw [map_one, mul_one]
    rfl
  have hΘ2 : ∀ F, Θ (1 ⊗ₜ Ideal.Quotient.mk PW F) = Ideal.Quotient.mk Q F := by
    intro F
    change θ₁ 1 * θ₂ (Ideal.Quotient.mk PW F) = _
    rw [map_one, one_mul]
    rfl
  have hsurj : Function.Surjective Θ := by
    intro y
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨1 ⊗ₜ Ideal.Quotient.mk PW F, hΘ2 F⟩
  set 𝔓 := RingHom.ker (Θ : D →+* MvPolynomial σ ℂ ⧸ Q)
  have h𝔓 : 𝔓.IsPrime := RingHom.ker_isPrime _
  have hj' : (1 : MvPolynomial σ ℂ ⧸ IC) ⊗ₜ Ideal.Quotient.mk PW (X j) ∉ 𝔓 := by
    rw [RingHom.mem_ker]
    change Θ _ ≠ 0
    rw [hΘ2]
    exact fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have heq : ∀ i, ∑ k, algebraMap ℂ D (a (i, k)) * (1 ⊗ₜ Ideal.Quotient.mk PW (X k)) -
      Ideal.Quotient.mk IC (X i) ⊗ₜ 1 ∈ 𝔓 := by
    intro i
    rw [RingHom.mem_ker]
    change Θ _ = 0
    rw [map_sub, map_sum, hΘ1, a3r_lin_X, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, hΘ2, map_mul]
    rfl
  have hb := ha j 𝔓 h𝔓 hj' heq
  have : Nontrivial (MvPolynomial σ ℂ ⧸ IC) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have : Nontrivial (MvPolynomial σ ℂ ⧸ PW) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have hD : ringKrullDim D = ringKrullDim (MvPolynomial σ ℂ ⧸ IC) +
      ringKrullDim (MvPolynomial σ ℂ ⧸ PW) := hc9k8_ringKrullDim_tensorProduct
  have hDP : ringKrullDim (D ⧸ 𝔓) = ringKrullDim (MvPolynomial σ ℂ ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective
      (f := (Θ : D →+* MvPolynomial σ ℂ ⧸ Q)) hsurj)
  rwa [hD, hDP] at hb

end Translate

end HodgeLean.Adapters
