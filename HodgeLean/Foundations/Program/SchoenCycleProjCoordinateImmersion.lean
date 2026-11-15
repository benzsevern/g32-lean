import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartMaps
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

/-- A graded retraction gives surjections on the degree-zero affine chart rings.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; homogeneous coordinate elimination. -/
theorem s2e_away_map_surjective_of_graded_retraction
    {A B : Type} [CommRing A] [CommRing B]
    {σ τ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : ∀ b, f (g b) = b)
    {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  refine ⟨Away.mk 𝒜 hs n (g b) (g.map_mem hb), ?_⟩
  simp only [Away.map_mk, hfg]

/-- Coordinate elimination on a graded retraction induces a closed immersion on projective spectra.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; affine chart criterion. -/
theorem s2e_proj_map_isClosedImmersion_of_graded_retraction
    {A B : Type} [CommRing A] [CommRing B]
    {σ τ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : ∀ b, f (g b) = b)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    IsClosedImmersion (Proj.map f hf) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (Proj.affineOpenCover 𝒜).openCover]
  intro x
  let s : A := x.2
  have hs : s ∈ 𝒜 (x.1 : ℕ) := x.2.2
  let iA := Proj.awayι 𝒜 s hs x.1.2
  let iB := Proj.awayι ℬ (f s) (f.map_mem hs) x.1.2
  let φ := Spec.map (CommRingCat.ofHom (Away.map f s))
  have hw : iB ≫ Proj.map f hf = φ ≫ iA := Proj.awayι_comp_map f hf x.1.2 s hs
  have hr : Proj.map f hf ⁻¹ᵁ iA.opensRange = iB.opensRange := by
    simp only [iA, iB, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]
  have pb := IsOpenImmersion.isPullback φ iB iA (Proj.map f hf) hw hr
  have hφ : IsClosedImmersion φ := IsClosedImmersion.spec_of_surjective _
    (s2e_away_map_surjective_of_graded_retraction 𝒜 ℬ f g hfg s hs)
  change IsClosedImmersion (pullback.snd (Proj.map f hf) iA)
  rw [← pb.flip.isoPullback_inv_snd]
  infer_instance

/-- A graded retraction maps onto the irrelevant ideal needed by the projective functor.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; homogeneous coordinate elimination. -/
theorem s2e_irrelevant_le_map_of_graded_retraction
    {A B : Type} [CommRing A] [CommRing B]
    {σ τ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : ∀ b, f (g b) = b) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  intro x hx
  rw [← hfg x]
  apply Ideal.mem_map_of_mem
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hx
  change GradedRing.proj 𝒜 0 (g x) = 0
  rw [GradedRing.proj_apply] at hx ⊢
  rw [← g.map_directSumDecompose, hx, map_zero]

/-- Graded maps preserve the irrelevant ideal.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; homogeneous coordinate maps. -/
theorem s2e_graded_map_mem_irrelevant
    {A B : Type} [CommRing A] [CommRing B]
    {σ τ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) {a : A} (ha : a ∈ HomogeneousIdeal.irrelevant 𝒜) :
    f a ∈ HomogeneousIdeal.irrelevant ℬ := by
  rw [HomogeneousIdeal.mem_irrelevant_iff] at ha ⊢
  rw [GradedRing.proj_apply] at ha ⊢
  rw [← f.map_directSumDecompose, ha, map_zero]

/-- The image of a projective graded retraction consists of the primes containing its kernel.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15; homogeneous coordinate elimination. -/
theorem s2e_proj_map_range_of_graded_retraction
    {A B : Type} [CommRing A] [CommRing B]
    {σ τ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : ∀ b, f (g b) = b)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Set.range (Proj.map f hf) =
      {p | RingHom.ker f.toRingHom ≤ p.asHomogeneousIdeal.toIdeal} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ a ha
    change f.toRingHom a ∈ q.asHomogeneousIdeal
    rw [RingHom.mem_ker.mp ha]
    exact q.asHomogeneousIdeal.zero_mem
  · intro hp
    let J := p.asHomogeneousIdeal.comap g
    have heq : J.comap f = p.asHomogeneousIdeal := by
      apply HomogeneousIdeal.ext
      ext a
      change g (f a) ∈ p.asHomogeneousIdeal.toIdeal ↔ a ∈ p.asHomogeneousIdeal.toIdeal
      have ha : a - g (f a) ∈ p.asHomogeneousIdeal.toIdeal := hp (by
        rw [RingHom.mem_ker, map_sub]
        exact sub_eq_zero.mpr (hfg (f a)).symm)
      constructor
      · intro h
        simpa only [sub_add_cancel] using p.asHomogeneousIdeal.toIdeal.add_mem ha h
      · intro h
        simpa only [sub_sub_cancel] using p.asHomogeneousIdeal.toIdeal.sub_mem h ha
    have hJ : ¬ HomogeneousIdeal.irrelevant ℬ ≤ J := by
      intro h
      apply p.not_irrelevant_le
      intro a ha
      have hmem : a ∈ J.comap f := h (s2e_graded_map_mem_irrelevant 𝒜 ℬ f ha)
      rwa [heq] at hmem
    let q : ProjectiveSpectrum ℬ := ⟨J, inferInstance, hJ⟩
    refine ⟨q, ?_⟩
    apply ProjectiveSpectrum.ext
    exact heq

end HodgeLean.Foundations.Program
