import HodgeLean.Adapters.NormalConeB4aGysinParameter
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Regular slicing of the special fibre

Regular parameters on the special fibre can be moved before the family
parameter in a regular sequence over the ambient local ring.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- Slicing by a regular sequence on the special fibre preserves injectivity
of the family parameter on the resulting quotient module. -/
theorem a3b4a_gysin_parameter_regular_after_slice
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (t : R) (xs : List R) (ht : IsSMulRegular R t)
    (hxs : RingTheory.Sequence.IsRegular (QuotSMulTop t R) xs) :
    IsSMulRegular (R ⧸ (Ideal.ofList xs • ⊤ : Submodule R R)) t := by
  have hreg : RingTheory.Sequence.IsRegular R (t :: xs) :=
    (RingTheory.Sequence.isRegular_cons_iff R t xs).mpr ⟨ht, hxs⟩
  have hperm : RingTheory.Sequence.IsRegular R (xs ++ [t]) :=
    IsLocalRing.isRegular_of_perm hreg (List.perm_append_comm (l₁ := [t]) (l₂ := xs))
  have hlast := ((RingTheory.Sequence.isWeaklyRegular_append_iff R xs [t]).mp
    hperm.toIsWeaklyRegular).2
  exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ t).mp hlast

end HodgeLean.Adapters
