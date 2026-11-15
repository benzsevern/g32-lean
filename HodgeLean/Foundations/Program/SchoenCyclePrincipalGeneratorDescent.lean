import HodgeLean.Foundations.Program.SchoenCycleCotangentGeneration
import HodgeLean.Foundations.Program.SchoenCycleAdicCotangentGeneration
import HodgeLean.Foundations.Program.SchoenCycleAdicIdealKernel

/-! # Approximation and descent of principal ideal generators -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A principal ideal generator remains a generator after perturbation by
the maximal ideal times that principal ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 2,
Proposition 2.8. -/
theorem s2e_principal_generator_stable_mod_maximal_mul
    {R : Type*} [CommRing R] [IsLocalRing R] (c d : R)
    (h : d - c ∈ IsLocalRing.maximalIdeal R * Ideal.span {c}) :
    Ideal.span {c} = Ideal.span {d} := by
  let J : Ideal R := Ideal.span {c}
  have hd : d ∈ J := by
    have hm : IsLocalRing.maximalIdeal R * J ≤ J := Ideal.mul_le_right
    simpa only [sub_add_cancel] using J.add_mem (hm h) (Ideal.subset_span (Set.mem_singleton c))
  apply le_antisymm
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot (Submodule.fg_span_singleton c)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    rw [Ideal.smul_eq_mul]
    apply Ideal.span_le.mpr
    intro r hr
    have hr : r = c := Set.mem_singleton_iff.mp hr
    subst r
    have hl : d ∈ Ideal.span {d} ⊔ IsLocalRing.maximalIdeal R * J :=
      (show Ideal.span {d} ≤ Ideal.span {d} ⊔ IsLocalRing.maximalIdeal R * J from le_sup_left)
        (Ideal.subset_span (Set.mem_singleton d))
    have hh : d - c ∈ Ideal.span {d} ⊔ IsLocalRing.maximalIdeal R * J :=
      (show IsLocalRing.maximalIdeal R * J ≤ Ideal.span {d} ⊔ IsLocalRing.maximalIdeal R * J from le_sup_right) h
    change c ∈ Ideal.span {d} ⊔ IsLocalRing.maximalIdeal R * J
    simpa only [sub_sub_cancel] using
      (Ideal.span {d} ⊔ IsLocalRing.maximalIdeal R * J).sub_mem hl hh
  · exact Ideal.span_le.mpr (fun r hr => (Set.mem_singleton_iff.mp hr) ▸ hd)

#print axioms s2e_principal_generator_stable_mod_maximal_mul
/-- Elements of an extended ideal can be approximated by original ideal
elements with error in an arbitrarily high adic power times that ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10,
Propositions 10.12–10.13. -/
theorem s2e_adic_ideal_element_approximation
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I J : Ideal R)
    (c : AdicCompletion I R) (hc : c ∈ J.map (algebraMap R (AdicCompletion I R)))
    (N : ℕ) :
    ∃ d : R, d ∈ J ∧ algebraMap R (AdicCompletion I R) d - c ∈
      (I ^ N).map (algebraMap R (AdicCompletion I R)) *
        J.map (algebraMap R (AdicCompletion I R)) := by
  let A := AdicCompletion I R
  let F := AdicCompletion.map I J.subtype
  rw [← s2e_adic_ideal_subtype_range I J] at hc
  obtain ⟨w, hw⟩ := hc
  obtain ⟨d, hd⟩ := Submodule.mkQ_surjective (I ^ N • (⊤ : Submodule R J)) (w.val N)
  have hu : AdicCompletion.of I J d - w ∈ I ^ N • (⊤ : Submodule R (AdicCompletion I J)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing I)]
    change AdicCompletion.eval I J N (AdicCompletion.of I J d - w) = 0
    rw [map_sub]
    change Submodule.mkQ _ d - w.val N = 0
    rw [hd, sub_self]
  let K := (I ^ N).map (algebraMap R A) * J.map (algebraMap R A)
  have hmap : ∀ u ∈ I ^ N • (⊤ : Submodule R (AdicCompletion I J)), F u ∈ K := by
    intro u hu
    refine Submodule.smul_induction_on hu ?_ ?_
    · intro r hr v hv
      rw [show F (r • v) = r • F v from (F.restrictScalars R).map_smul r v,
        Algebra.smul_def]
      apply Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hr)
      rw [← s2e_adic_ideal_subtype_range I J]
      exact ⟨v, rfl⟩
    · intro u v hu hv
      simpa only [map_add] using K.add_mem hu hv
  refine ⟨d.val, d.property, ?_⟩
  change AdicCompletion.of I R d.val - c ∈ K
  have h := hmap _ hu
  simpa only [F, map_sub, AdicCompletion.map_of, Submodule.subtype_apply, hw] using h

#print axioms s2e_adic_ideal_element_approximation
/-- A generator of an extended local ideal can be approximated to arbitrary
order by a generator of the original ideal.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 2 and 10;
Nakayama's lemma and faithful flatness of the local adic algebra. -/
theorem s2e_local_principal_generator_approximating_adic
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) (c : AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (hgen : J.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) =
      Ideal.span {c}) (N : ℕ) :
    ∃ d : R, J = Ideal.span {d} ∧
      algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) d - c ∈
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ N := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI : Module.FaithfullyFlat R A := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hc : c ∈ J.map (algebraMap R A) := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton c)
  obtain ⟨d, _, hd⟩ := s2e_adic_ideal_element_approximation
    (IsLocalRing.maximalIdeal R) J c hc (N + 1)
  have he : algebraMap R A d - c ∈
      IsLocalRing.maximalIdeal A ^ (N + 1) * Ideal.span {c} := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← hgen]
    exact hd
  have hh : algebraMap R A d - c ∈ IsLocalRing.maximalIdeal A * Ideal.span {c} :=
    (Ideal.mul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero N))) he
  have hg := s2e_principal_generator_stable_mod_maximal_mul c (algebraMap R A d) hh
  refine ⟨d, ?_, ?_⟩
  · apply Ideal.map_injective_of_faithfullyFlat (B := A)
    rw [Ideal.map_span, Set.image_singleton]
    exact hgen.trans hg
  · exact (Ideal.pow_le_pow_right (Nat.le_succ N)) (Ideal.mul_le_left he)

#print axioms s2e_local_principal_generator_approximating_adic
end HodgeLean.Foundations.Program
