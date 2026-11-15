import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantLocalization
import Mathlib.Algebra.Ring.Subring.Units

/-! # Localization of invariant equalizer subrings

Implication from compatible endomorphisms of a domain and its localization to
localization of their invariant subrings. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The inclusion of a subring of common fixed points reflects invertibility.
Source: Stacks Project, tag 04A9, equalizers of invariant functions; uniqueness of multiplicative inverses. -/
theorem s2v_l1a_invariant_subring_isLocalHom
    {R T : Type*} [CommRing R] (ρ : T → (R →+* R)) (P : Subring R)
    (hP : ∀ r : R, r ∈ P ↔ ∀ t, ρ t r = r) :
    IsLocalHom P.subtype := by
  let F : R →+* (T → R) := RingHom.pi ρ
  let D : R →+* (T → R) := RingHom.pi (fun _ : T => RingHom.id R)
  have heq : P = F.eqLocus D := by
    apply SetLike.ext
    intro r
    rw [hP r, RingHom.mem_eqLocus]
    change (∀ t, ρ t r = r) ↔ (fun t => ρ t r) = (fun _ => r)
    exact funext_iff.symm
  exact heq.symm ▸ (inferInstance : IsLocalHom (F.eqLocus D).subtype)

/-- Invariant equalizer subrings of a domain and its localization form the corresponding localization.
Source: Stacks Project, tag 04A9, invariant functions; localization on principal affine opens. -/
theorem s2v_l1a_equalizer_subring_localization
    {R A T : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    (ρ : T → (R →+* R)) (σ : T → (A →+* A))
    (P : Subring R) (Q : Subring A)
    (hP : ∀ r : R, r ∈ P ↔ ∀ t, ρ t r = r)
    (hQ : ∀ s : A, s ∈ Q ↔ ∀ t, σ t s = s)
    [Algebra P Q] [IsLocalHom Q.subtype]
    (hPQ : ∀ r : P, (algebraMap P Q r : A) = algebraMap R A (r : R))
    (d : R) (hd : d ∈ P) [IsLocalization.Away d A]
    (hmap : ∀ t, (σ t).comp (algebraMap R A) = (algebraMap R A).comp (ρ t)) :
    IsLocalization.Away (⟨d, hd⟩ : P) Q := by
  apply IsLocalization.Away.mk
  · apply (isUnit_map_iff Q.subtype _).mp
    change IsUnit ((algebraMap P Q ⟨d, hd⟩ : Q) : A)
    rw [hPQ]
    exact IsLocalization.map_units A ⟨d, Submonoid.mem_powers d⟩
  · intro s
    obtain ⟨n, r, hr, heq⟩ := s2v_l1a_invariant_localization_numerator
      d ρ σ hmap ((hP d).mp hd) (s : A) ((hQ (s : A)).mp s.property)
    refine ⟨n, ⟨r, (hP r).mpr hr⟩, ?_⟩
    apply Subtype.ext
    change (s : A) * (algebraMap P Q ⟨d, hd⟩ : A) ^ n = _
    rw [hPQ, hPQ]
    exact heq
  · intro a b hab
    have heq : algebraMap R A (a : R) = algebraMap R A (b : R) := by
      simpa only [hPQ] using congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq d heq
    exact ⟨n, Subtype.ext hn⟩

/-- Invariant equalizer subrings of a ring and its localization for a finite endomorphism family form the corresponding localization.
Source: Stacks Project, tag 04A9, invariant functions; localization on principal affine opens. -/
theorem s2v_l1a_finite_equalizer_subring_localization
    {R A T : Type*} [CommRing R] [Finite T] [CommRing A] [Algebra R A]
    (ρ : T → (R →+* R)) (σ : T → (A →+* A))
    (P : Subring R) (Q : Subring A)
    (hP : ∀ r : R, r ∈ P ↔ ∀ t, ρ t r = r)
    (hQ : ∀ s : A, s ∈ Q ↔ ∀ t, σ t s = s)
    [Algebra P Q] [IsLocalHom Q.subtype]
    (hPQ : ∀ r : P, (algebraMap P Q r : A) = algebraMap R A (r : R))
    (d : R) (hd : d ∈ P) [IsLocalization.Away d A]
    (hmap : ∀ t, (σ t).comp (algebraMap R A) = (algebraMap R A).comp (ρ t)) :
    IsLocalization.Away (⟨d, hd⟩ : P) Q := by
  apply IsLocalization.Away.mk
  · apply (isUnit_map_iff Q.subtype _).mp
    change IsUnit ((algebraMap P Q ⟨d, hd⟩ : Q) : A)
    rw [hPQ]
    exact IsLocalization.map_units A ⟨d, Submonoid.mem_powers d⟩
  · intro s
    obtain ⟨n, r, hr, heq⟩ := s2v_l1a_invariant_localization_numerator_of_finite_family
      d ρ σ hmap ((hP d).mp hd) (s : A) ((hQ (s : A)).mp s.property)
    refine ⟨n, ⟨r, (hP r).mpr hr⟩, ?_⟩
    apply Subtype.ext
    change (s : A) * (algebraMap P Q ⟨d, hd⟩ : A) ^ n = _
    rw [hPQ, hPQ]
    exact heq
  · intro a b hab
    have heq : algebraMap R A (a : R) = algebraMap R A (b : R) := by
      simpa only [hPQ] using congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq d heq
    exact ⟨n, Subtype.ext hn⟩

end HodgeLean.Foundations.Program
