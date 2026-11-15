import HodgeLean.Foundations.Program.SchoenCycleAdicCotangentEquiv

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The canonical maximal-ideal adic map identifies the actual local cotangent modules over the prescribed scalars.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_local_adic_cotangent_equiv
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R] :
    (IsLocalRing.maximalIdeal R).Cotangent ≃ₗ[k]
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)).Cotangent := by
  let I := IsLocalRing.maximalIdeal R
  have h : I.map (algebraMap R (AdicCompletion I R)) =
      IsLocalRing.maximalIdeal (AdicCompletion I R) :=
    (AdicCompletion.maximalIdeal_eq_map (R := R)).symm
  exact (s2e_adic_ideal_cotangent_equiv (k := k) I (IsNoetherian.noetherian I)).trans
    ((Ideal.Cotangent.equivOfEq _ _ h).restrictScalars k)

#print axioms s2e_local_adic_cotangent_equiv

/-- The canonical local adic cotangent identification preserves the actual class of each maximal-ideal element.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_local_adic_cotangent_toCotangent
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R] (x : IsLocalRing.maximalIdeal R) :
    ∃ hx : AdicCompletion.of (IsLocalRing.maximalIdeal R) R x.val ∈
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      s2e_local_adic_cotangent_equiv (k := k) ((IsLocalRing.maximalIdeal R).toCotangent x) =
        (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R)).toCotangent
          ⟨AdicCompletion.of (IsLocalRing.maximalIdeal R) R x.val, hx⟩ := by
  refine ⟨?_, ?_⟩
  · rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap R _) x.property
  · rfl

#print axioms s2e_local_adic_cotangent_toCotangent
end HodgeLean.Foundations.Program
