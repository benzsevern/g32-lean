import HodgeLean.Adapters.NormalConeB4aGysinLocalParameterLength

/-! # Affine representatives of local slice parameters -/

noncomputable section
namespace HodgeLean.Adapters

/-- A finite list of local parameters can be represented by elements of the
original prime, retaining its length and its full extended ideal. -/
theorem a3b4a_gysin_exists_affine_parameter_numerators
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (xs : List (Localization.AtPrime p))
    (hxs : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    ∃ ys : List R, ys.length = xs.length ∧
      (∀ y ∈ ys, y ∈ p) ∧
      (Ideal.ofList ys).map (algebraMap R (Localization.AtPrime p)) = Ideal.ofList xs := by
  induction xs with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons x xs ih =>
    obtain ⟨ys, hlen, hmem, hideal⟩ := ih (fun z hz => hxs z (List.mem_cons_of_mem x hz))
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj p.primeCompl x
    have ha : a ∈ p := by
      apply (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p a).mp
      rw [← hs]
      exact (IsLocalRing.maximalIdeal (Localization.AtPrime p)).mul_mem_right _
        (hxs x (List.mem_cons_self))
    refine ⟨a :: ys, by simp [hlen], ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ha
      · exact hmem y hy
    · rw [Ideal.ofList_cons, Ideal.map_sup, hideal, Ideal.ofList_cons]
      congr 1
      rw [Ideal.map_span, Set.image_singleton, ← hs]
      exact Ideal.span_singleton_mul_right_unit (IsLocalization.map_units (Localization.AtPrime p) s) x

end HodgeLean.Adapters
