import HodgeLean.Foundations.Curves.CurvePoints
import HodgeLean.Foundations.Curves.CurveRamification
import HodgeLean.Foundations.Curves.ChartStalks
import HodgeLean.Foundations.Curves.CurveStalkDVR

/-! # Counting zeros on a smooth projective curve

For a transcendental rational function `t` on an integral smooth complete complex curve, the
zeros of `t` correspond to the primes above `(t)` in the integral closure of `ℂ[t]` in the
function field, with matching multiplicities. Hence the number of zeros of `t`, counted with
multiplicity, is `[K : ℂ⟮t⟯]`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry IntermediateField

namespace HodgeLean.Foundations.Curves

attribute [local instance] overSpecAlgebra functionFieldAlgebra

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsLocallyNoetherian X.left]

/-- The order of the image of a nonzero element of a DVR stalk is its length-based order. -/
theorem ord_algebraMap_stalk {P : X.left} [IsDiscreteValuationRing (X.left.presheaf.stalk P)]
    {s : X.left.presheaf.stalk P} (hs : s ≠ 0) :
    X.left.ord (algebraMap _ X.left.functionField s) P =
      ((Ring.ord (X.left.presheaf.stalk P) s).toNat : ℤ) := by
  have hs' : s ∈ nonZeroDivisors (X.left.presheaf.stalk P) := mem_nonZeroDivisors_of_ne_zero hs
  have hfin := Ring.ord_ne_top hs'
  apply ChartStalks.ord_eq_of_dvr P (by simpa using hs)
  rw [Ring.ordFrac_eq_ord _ (K := X.left.functionField) hs,
    Ring.ordMonoidWithZeroHom_eq_coe _ hs' (ENat.natCast_toNat hfin).symm]
  rfl

/-- The order of `1` is zero. -/
theorem ord_one_eq_zero (P : X.left) : X.left.ord (1 : X.left.functionField) P = 0 := by
  have h := Scheme.ord_mul (X := X.left) (x := P) (one_ne_zero (α := X.left.functionField))
    (one_ne_zero (α := X.left.functionField))
  rw [mul_one] at h
  omega

/-- The order of an inverse is the negative order. -/
theorem ord_inv {f : X.left.functionField} (hf : f ≠ 0) (P : X.left) :
    X.left.ord f⁻¹ P = - X.left.ord f P := by
  have h := Scheme.ord_mul (X := X.left) (x := P) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one_eq_zero] at h
  omega

variable [SmoothOfRelativeDimension 1 X.hom] [UniversallyClosed X.hom] [IsSeparated X.hom]

/-- The zeros of a transcendental rational function, counted with multiplicity, number
`[K : ℂ⟮t⟯]`.
Source: Hartshorne, *Algebraic Geometry*, II.6.9; Serre, *Local Fields*, I.4. -/
theorem finsum_toNat_ord_eq_finrank (t : X.left.functionField) (ht : Transcendental ℂ t)
    [FiniteDimensional ℂ⟮t⟯ X.left.functionField] :
    ∑ᶠ P : X.left, (X.left.ord t P).toNat = Module.finrank ℂ⟮t⟯ X.left.functionField := by
  have ht0 : t ≠ 0 := fun h0 ↦ ht (h0 ▸ isAlgebraic_zero)
  have hpt := fun q ↦ exists_point_range_eq (X := X) (valAt ht q) (algebraMap_mem_valAt ht q)
    (valAt_ne_top ht q)
  choose Φ hΦcoh hΦ using hpt
  have hval : ∀ q, (X.left.ord t (Φ q)).toNat = (Ring.ord (Localization.AtPrime q.1)
      (algebraMap (intClosure t) _ (tA t))).toNat := by
    intro q
    have := isDVR_stalk (X := X) (hΦcoh q)
    obtain ⟨s, hs⟩ := (hΦ q t).mp (t_mem_valAt ht q)
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [map_zero] at hs
      exact ht0 hs.symm
    have h1 := ord_algebraMap_stalk (X := X) hs0
    rw [hs] at h1
    rw [h1, Int.toNat_natCast, ord_localization_eq]
    congr 1
    refine ord_eq_of_range_eq (algebraMap _ X.left.functionField)
      (algebraMap (locSub t q.1) X.left.functionField) (IsFractionRing.injective _ _)
      Subtype.val_injective (fun x ↦ (hΦ q x).symm) ?_
    exact hs
  have hinj : Function.Injective Φ := by
    intro q q' h
    apply valAt_injective ht
    ext x
    rw [hΦ q x, hΦ q' x, h]
  have hsupp : Function.support (fun P ↦ (X.left.ord t P).toNat) ⊆ Set.range Φ := by
    intro P hP
    have hpos : 0 < X.left.ord t P := by
      simp only [Function.mem_support, ne_eq, Int.toNat_eq_zero, not_le] at hP
      exact hP
    have hcoh : Order.coheight P = 1 := by
      by_contra h
      rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at hpos
      exact lt_irrefl _ hpos
    have := isDVR_stalk (X := X) hcoh
    let W := valuationSubringOfFractionRing (X.left.presheaf.stalk P) X.left.functionField
    have hinv : t⁻¹ ∉ W := by
      rintro ⟨s, hs⟩
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [map_zero] at hs
        exact inv_ne_zero ht0 hs.symm
      have h1 := ord_algebraMap_stalk (X := X) hs0
      rw [hs, ord_inv ht0] at h1
      omega
    have htW : t ∈ W := by
      rcases ValuationRing.isInteger_or_isInteger (X.left.presheaf.stalk P) t with h | h
      · exact h
      · exact absurd h hinv
    have hC : ∀ c, algebraMap ℂ X.left.functionField c ∈ W := fun c ↦
      ⟨stalkC P c, algebraMap_stalkC P c⟩
    have hWtop : W ≠ ⊤ := fun h ↦ hinv (h ▸ trivial)
    obtain ⟨q, hq⟩ := exists_locSub_le ht W hC htW hinv
    have := isDVR_locSub ht q
    have hWeq : ∀ x, x ∈ valAt ht q ↔ x ∈ W := fun x ↦
      ⟨fun hx ↦ by
        obtain ⟨r, rfl⟩ := (mem_valAt ht q).mp hx
        exact hq r,
       fun hx ↦ (mem_valAt ht q).mpr
        (exists_algebraMap_eq_of_mem_valuationSubring W hq hWtop hx)⟩
    have := isDVR_stalk (X := X) (hΦcoh q)
    refine ⟨q, eq_of_range_eq ?_⟩
    ext x
    rw [RingHom.mem_range, RingHom.mem_range, ← hΦ q x, hWeq]
    rfl
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range Φ)
    (fun x hx ↦ ⟨fun _ ↦ hsupp hx, fun _ ↦ trivial⟩), finsum_mem_range hinj]
  simp_rw [hval]
  exact finsum_ord_primesOver ht

end HodgeLean.Foundations.Curves