import HodgeLean.Adapters.NormalConeB4aGysinBridge2FiltrationLength
import HodgeLean.Adapters.NormalConeB4aGysinBridge2RegularParameters

/-! # Reformulated bridge of A3-B4a: exact slice lengths of local nilpotent thickenings

A local ring `A` with a nilpotent ideal `I` whose graded pieces `I^k / I^(k+1)` are free over
`A ⧸ I` of ranks `r k`: for a sequence weakly regular on `A ⧸ I` generating the maximal ideal
together with `I`, the length of the slice `A ⧸ (rs)` is the total rank `∑ r k`. When `A ⧸ I` is
regular local of dimension `n`, every list of `n` elements generating the maximal ideal together
with `I` is such a sequence. Source: Fulton, *Intersection Theory*, Lemma A.2 and Example 7.1.10;
Matsumura, *Commutative Ring Theory*, Theorem 17.4. -/

noncomputable section
namespace HodgeLean.Adapters
open IsLocalRing RingTheory.Sequence Pointwise

/-- The residue field of a local ring has length one. -/
theorem a3b4g_length_quotient_maximalIdeal (A : Type*) [CommRing A] [IsLocalRing A] :
    Module.length A (A ⧸ maximalIdeal A) = 1 := by
  haveI : IsSimpleModule A (A ⧸ maximalIdeal A) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A))
  exact Module.length_eq_one _ _

/-- The exact length of a slice of a local nilpotent thickening with free graded pieces is the
total rank of the graded pieces. Source: Fulton, *Intersection Theory*, Lemma A.2. -/
theorem a3b4g_local_length (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A) (N : ℕ)
    (hN : I ^ N = ⊥) (r : ℕ → ℕ)
    (e : ∀ k < N, a3b4g_gradedPiece (fun k => ((I ^ k : Ideal A) : Submodule A A)) k ≃ₗ[A]
      (Fin (r k) → A ⧸ I))
    (rs : List A) (hreg : IsWeaklyRegular (A ⧸ I) rs)
    (hgen : Ideal.ofList rs ⊔ I = maximalIdeal A) :
    Module.length A (A ⧸ Ideal.ofList rs) = ∑ k ∈ Finset.range N, (r k : ℕ∞) := by
  rw [a3b4g_length_quot_of_free_graded I N hN r e rs hreg]
  suffices h : Module.length A ((A ⧸ I) ⧸ (Ideal.ofList rs • ⊤ : Submodule A (A ⧸ I))) = 1 by
    rw [h, mul_one]
  have hmap : (Ideal.ofList rs • ⊤ : Submodule A (A ⧸ I)) =
      Submodule.map (Submodule.mkQ (I : Submodule A A)) (Ideal.ofList rs : Submodule A A) := by
    calc (Ideal.ofList rs • ⊤ : Submodule A (A ⧸ I))
        = Ideal.ofList rs • Submodule.map (Submodule.mkQ (I : Submodule A A)) (⊤ : Submodule A A) := by
          rw [Submodule.map_top, Submodule.range_mkQ]
      _ = Submodule.map (Submodule.mkQ (I : Submodule A A)) (Ideal.ofList rs • ⊤ : Submodule A A) :=
          (Submodule.map_smul'' _ _ _).symm
      _ = Submodule.map (Submodule.mkQ (I : Submodule A A)) (Ideal.ofList rs : Submodule A A) := by
          rw [smul_eq_mul, Ideal.mul_top]
  rw [hmap, (Submodule.quotientQuotientEquivQuotientSup (I : Submodule A A)
    (Ideal.ofList rs : Submodule A A)).length_eq]
  have hsup : ((I : Submodule A A) ⊔ (Ideal.ofList rs : Submodule A A)) = maximalIdeal A := by
    rw [sup_comm]
    exact hgen
  rw [hsup]
  exact a3b4g_length_quotient_maximalIdeal A

/-- A list of `dim (A ⧸ I)` elements generating the maximal ideal of a local ring `A` together
with `I`, where `A ⧸ I` is regular local, is weakly regular on `A ⧸ I`.
Source: Matsumura, *Commutative Ring Theory*, Theorem 14.3 and Theorem 17.4. -/
theorem a3b4g_isWeaklyRegular_quotient (A : Type*) [CommRing A] [IsLocalRing A] (I : Ideal A)
    [IsRegularLocalRing (A ⧸ I)] (n : ℕ) (hdim : ringKrullDim (A ⧸ I) = n) (rs : List A)
    (hlen : rs.length = n) (hgen : Ideal.ofList rs ⊔ I = maximalIdeal A) :
    IsWeaklyRegular (A ⧸ I) rs := by
  have h := a3b4g_isWeaklyRegular_of_ofList_eq_maximalIdeal n (A ⧸ I)
    (rs.map (algebraMap A (A ⧸ I))) hdim (by rw [List.length_map, hlen]) (by
      rw [← Ideal.map_ofList, ← map_maximalIdeal_of_surjective (algebraMap A (A ⧸ I))
        Ideal.Quotient.mk_surjective, ← hgen, Ideal.map_sup, Ideal.Quotient.algebraMap_eq,
        Ideal.map_quotient_self, sup_bot_eq])
  exact (isWeaklyRegular_map_algebraMap_iff (R := A) (S := A ⧸ I) (M := A ⧸ I) rs).mp h

end HodgeLean.Adapters
