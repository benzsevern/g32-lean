import HodgeLean.Foundations.Program.SchoenTowerI1aHomogeneousAvoidance

import HodgeLean.Foundations.Program.SchoenTowerI1aHomogeneousAvoidanceLo
/-! # Finite affine neighborhoods in projective presentations
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An open of a closed subscheme is the inverse image of an ambient open.
Source: Hartshorne, Algebraic Geometry, II.2, topology of closed immersions. -/
theorem s2v_i1alo_ambient_open
    (S Q : Scheme) (f : S ⟶ Q) [IsClosedImmersion f] (N : S.Opens) :
    ∃ M : Q.Opens, f ⁻¹ᵁ M = N := by
  obtain ⟨M, hM, hpre⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp N.isOpen
  exact ⟨⟨M, hM⟩, SetLike.coe_injective hpre⟩

/-- A finite set in a spectrum open lies in one contained principal open.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.11. -/
theorem s2v_i1alo_spectrum_finite_principal
    (R : Type*) [CommRing R] (O : TopologicalSpace.Opens (PrimeSpectrum R))
    (s : Finset (PrimeSpectrum R)) (hs : ∀ p ∈ s, p ∈ O) :
    ∃ r : R, PrimeSpectrum.basicOpen r ≤ O ∧ ∀ p ∈ s, p ∈ PrimeSpectrum.basicOpen r := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (O : Set (PrimeSpectrum R))ᶜ).mp
    O.isOpen.isClosed_compl
  have hnot (p) (hp : p ∈ s) : ¬ I ≤ p.asIdeal := by
    intro hle
    have hz : p ∈ (O : Set (PrimeSpectrum R))ᶜ := by
      rw [hI]
      exact hle
    exact hz (hs p hp)
  have hbad : ¬ (I : Set R) ⊆ ⋃ p ∈ (s : Set (PrimeSpectrum R)), (p.asIdeal : Set R) := by
    intro hsub
    obtain ⟨p, hp, hIP⟩ := (Ideal.subset_union_prime p₀ p₀ (f := PrimeSpectrum.asIdeal)
      (fun p _ _ _ => p.isPrime)).mp hsub
    exact hnot p hp hIP
  obtain ⟨r, hrI, hrbad⟩ := Set.not_subset.mp hbad
  refine ⟨r, ?_, ?_⟩
  · intro p hp
    by_contra hpo
    change p ∈ (O : Set (PrimeSpectrum R))ᶜ at hpo
    rw [hI] at hpo
    exact hp (hpo hrI)
  · intro p hp
    exact fun hrp => hrbad (Set.mem_biUnion hp hrp)

/-- A finite set in an affine chart can be retained while shrinking into a prescribed open.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.11; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2v_i1alo_shrink_affine_finite
    (Q : Scheme) (A : Q.Opens) (hA : IsAffineOpen A) (N : Q.Opens)
    (s : Finset Q) (hsA : ∀ x ∈ s, x ∈ A) (hsN : ∀ x ∈ s, x ∈ N) :
    ∃ V : Q.Opens, IsAffineOpen V ∧ V ≤ N ∧ V ≤ A ∧ ∀ x ∈ s, x ∈ V := by
  classical
  let e := hA.isoSpec
  have hehom : e.hom = A.toSpecΓ := hA.isoSpec_hom
  let O := e.inv ⁻¹ᵁ (A.ι ⁻¹ᵁ N)
  let points : Finset (Spec Γ(Q, A)) := s.attach.image
    (fun x => e.hom ⟨x.val, hsA x.val x.property⟩)
  have hpoints : ∀ p ∈ points, p ∈ O := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    have hh := congrArg (fun k : A.toScheme ⟶ A.toScheme =>
      k ⟨x.val, hsA x.val x.property⟩) e.hom_inv_id
    change e.inv (e.hom ⟨x.val, hsA x.val x.property⟩) = ⟨x.val, hsA x.val x.property⟩ at hh
    change e.inv (e.hom ⟨x.val, hsA x.val x.property⟩) ∈ A.ι ⁻¹ᵁ N
    rw [hh]
    exact hsN x.val x.property
  obtain ⟨r, hr, hrpoints⟩ := s2v_i1alo_spectrum_finite_principal (Γ(Q, A) : Type _) O points hpoints
  have hpA : A.ι ⁻¹ᵁ Q.basicOpen r ≤ A.ι ⁻¹ᵁ N := by
    rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen, ← hehom]
    have hh := e.hom.preimage_mono hr
    change e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ e.hom ⁻¹ᵁ (e.inv ⁻¹ᵁ (A.ι ⁻¹ᵁ N)) at hh
    simpa only [← Scheme.Hom.comp_preimage, Iso.hom_inv_id_assoc] using hh
  have hVN : Q.basicOpen r ≤ N := by
    have hh := A.ι.image_mono hpA
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (Q.basicOpen_le r)] at hh
    exact hh.trans inf_le_right
  refine ⟨Q.basicOpen r, hA.basicOpen r, hVN, Q.basicOpen_le r, ?_⟩
  intro x hx
  let xA : A.toScheme := ⟨x, hsA x hx⟩
  have hp : e.hom xA ∈ points := Finset.mem_image.mpr
    ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
  have hz : xA ∈ A.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
    rw [← hehom]
    exact hrpoints _ hp
  have hz' := (Scheme.Opens.toSpecΓ_preimage_basicOpen A r).le hz
  exact hz'


end HodgeLean.Foundations.Program
