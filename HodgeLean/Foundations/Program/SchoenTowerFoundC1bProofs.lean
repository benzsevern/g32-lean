module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2t_imageIdeal_eq_top_of_avoids_support {B T : Scheme.{0}}
    (I : B.IdealSheafData) (f : T ⟶ B)
    (hf : ∀ x : T, f x ∉ I.support) : I.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  exact iff_of_false (hf x) (by simp)

theorem s2t_imageIdeal_frames_of_avoids_support {B T : Scheme.{0}}
    (I : B.IdealSheafData) (f : T ⟶ B)
    (hf : ∀ x : T, f x ∉ I.support) :
    ∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V)) := by
  intro x
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, _⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨⟨V, hV⟩, hx, ?_⟩
  rw [s2t_imageIdeal_eq_top_of_avoids_support I f hf]
  exact ⟨Submodule.topEquiv⟩

/-- Away from the ideal support, a specified universal modification has an actual inverse.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.14;
Stacks Project, Tag 01OF, Lemmas 31.33.4(1) and 31.33.5. -/
theorem s2t_cartierUniversal_offCentre_aux {B X : Scheme.{0}}
    (I : B.IdealSheafData) (b : X ⟶ B)
    (huniv : ∀ (T : Scheme.{0}) (f : T ⟶ B),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X, u ≫ b = f)
    (U : B.Opens) (hU : ∀ x ∈ U, x ∉ I.support) :
    ∃! e : (b ⁻¹ᵁ U).toScheme ≅ U.toScheme,
      e.hom = b ∣_ U ∧ e.inv ≫ (b ⁻¹ᵁ U).ι ≫ b = U.ι :=
by
  obtain ⟨u, hu, _⟩ := huniv U.toScheme U.ι
    (s2t_imageIdeal_frames_of_avoids_support I U.ι (fun x => hU _ x.property))
  let P := isPullback_morphismRestrict b U
  let v := P.lift (𝟙 U.toScheme) u (by simpa only [Category.id_comp] using hu.symm)
  have hv : v ≫ b ∣_ U = 𝟙 U.toScheme := P.lift_fst _ _ _
  have hvj : v ≫ (b ⁻¹ᵁ U).ι = u := P.lift_snd _ _ _
  have hru : (b ∣_ U) ≫ u = (b ⁻¹ᵁ U).ι := by
    obtain ⟨w, _, hw⟩ := huniv (b ⁻¹ᵁ U).toScheme ((b ⁻¹ᵁ U).ι ≫ b)
      (s2t_imageIdeal_frames_of_avoids_support I _ (fun x => hU _ x.property))
    apply (hw _ ?_).trans (hw _ rfl).symm
    rw [Category.assoc, hu, morphismRestrict_ι]
  have hrv : (b ∣_ U) ≫ v = 𝟙 (b ⁻¹ᵁ U).toScheme := by
    apply (cancel_mono (b ⁻¹ᵁ U).ι).mp
    rw [Category.assoc, hvj, hru, Category.id_comp]
  refine ⟨⟨b ∣_ U, v, hrv, hv⟩, ⟨rfl, ?_⟩, ?_⟩
  · change v ≫ (b ⁻¹ᵁ U).ι ≫ b = U.ι
    rw [← Category.assoc, hvj, hu]
  · intro e he
    apply Iso.ext
    exact he.1

end HodgeLean.Foundations.Program
