import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantLocalization

/-! # Actual invariant images after principal quotient restriction

Implication from an actual invariant-image ring map to its same identification
after compatible principal localizations and specified restricted actions.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Injectivity and the exact invariant image persist on compatible actual
principal localizations, using the specified localized section map.
Source: Stacks Project, tag 04A9; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2v_l1a_localized_invariant_image
    {D A D' A' T : Type*} [CommRing D] [CommRing A] [CommRing D'] [CommRing A']
    [Algebra D D'] [Algebra A A'] [Finite T]
    (q : D →+* A) (hq : Function.Injective q)
    (ρ : T → (A →+* A))
    (himage : ∀ a : A, a ∈ Set.range q ↔ ∀ t, ρ t a = a)
    (d : D) [IsLocalization.Away d D'] [IsLocalization.Away (q d) A']
    (q' : D' →+* A')
    (hcomm : ∀ r : D, q' (algebraMap D D' r) = algebraMap A A' (q r))
    (σ : T → (A' →+* A'))
    (hmap : ∀ t, (σ t).comp (algebraMap A A') = (algebraMap A A').comp (ρ t)) :
    Function.Injective q' ∧
      ∀ s : A', s ∈ Set.range q' ↔ ∀ t, σ t s = s := by
  have hfixed (t : T) (r : D) : ρ t (q r) = q r := (himage (q r)).mp ⟨r, rfl⟩ t
  have hmap' (t : T) (a : A) : σ t (algebraMap A A' a) =
      algebraMap A A' (ρ t a) := DFunLike.congr_fun (hmap t) a
  letI : IsLocalization ((Submonoid.powers d).map q) A' := by
    rw [Submonoid.map_powers]
    infer_instance
  have hqmap : q' = IsLocalization.map A' q (Submonoid.powers d).le_comap_map := by
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    ext r
    rw [RingHom.comp_apply, hcomm, RingHom.comp_apply, IsLocalization.map_eq]
  refine ⟨?_, ?_⟩
  · rw [hqmap]
    exact IsLocalization.map_injective_of_injective (Submonoid.powers d) D' A' hq
  · intro s
    constructor
    · rintro ⟨r, rfl⟩ t
      have H : (σ t).comp q' = q' := by
        apply IsLocalization.ringHom_ext (Submonoid.powers d)
        ext r
        simp only [RingHom.comp_apply, hcomm, hmap', hfixed]
      exact DFunLike.congr_fun H r
    · intro hs
      obtain ⟨n, r, hr, hnum⟩ := s2v_l1a_invariant_localization_numerator_of_finite_family
        (q d) ρ σ hmap (fun t => hfixed t d) s hs
      obtain ⟨b, hb⟩ := (himage r).mpr hr
      let den : Submonoid.powers d := ⟨d ^ n, ⟨n, rfl⟩⟩
      let v := IsLocalization.mk' D' b den
      refine ⟨v, ?_⟩
      apply (IsUnit.mul_right_inj ((IsLocalization.map_units A'
        ⟨q d, Submonoid.mem_powers (q d)⟩).pow n)).mp
      have H := congrArg q' (IsLocalization.mk'_spec D' b den)
      change q' (v * algebraMap D D' (d ^ n)) = q' (algebraMap D D' b) at H
      rw [map_mul, hcomm, hcomm, map_pow, map_pow, hb] at H
      simpa only [mul_comm] using H.trans hnum.symm

end HodgeLean.Foundations.Program
