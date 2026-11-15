import HodgeLean.Foundations.Program.SchoenHomogeneousFractionCancellation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual homogeneous-localization map agrees with ordinary localization
under the canonical fraction embeddings. -/
theorem s2_homogeneousLocalization_val_map {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (M : Submonoid A) (N : Submonoid B) (hMN : M ≤ N.comap f)
    (z : HomogeneousLocalization 𝒜 M) :
    (HomogeneousLocalization.map f hMN z).val =
      IsLocalization.map (Localization N) f.toRingHom hMN z.val := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  simp only [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.map_mk']
  rfl

/-- An injective graded ring map into a domain stays injective after homogeneous
localization at compatible submonoids excluding zero in the target. -/
theorem s2_homogeneousLocalization_map_injective {A B : Type} [CommRing A] [CommRing B]
    [IsDomain B] (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (M : Submonoid A) (N : Submonoid B) (hMN : M ≤ N.comap f)
    (hN : (0 : B) ∉ N) (hf : Function.Injective f) :
    Function.Injective (HomogeneousLocalization.map f hMN) := by
  have hF : Function.Injective
      (IsLocalization.map (Localization N) f.toRingHom hMN : Localization M →+* Localization N) :=
    IsLocalization.map_injective_of_injective' M B (Localization N) hMN hN hf
  intro x y hxy
  apply HomogeneousLocalization.val_injective
  apply hF
  rw [← s2_homogeneousLocalization_val_map 𝒜 ℬ f M N hMN,
    ← s2_homogeneousLocalization_val_map 𝒜 ℬ f M N hMN]
  exact congrArg HomogeneousLocalization.val hxy

end HodgeLean.Foundations.Program
