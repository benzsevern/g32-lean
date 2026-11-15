import HodgeLean.Foundations.Program.SchoenHomogeneousQuotientProj
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A homogeneous prime containing the quotient ideal gives an actual point of the quotient Proj. -/
def s2_homogeneousQuotientProjPoint {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    (p : ProjectiveSpectrum 𝒜) (hIp : I.toIdeal ≤ p.asHomogeneousIdeal.toIdeal) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    ProjectiveSpectrum (s2_homogeneousQuotientPiece 𝒜 I) := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  let f := s2_homogeneousQuotientMap 𝒜 I
  let J := p.asHomogeneousIdeal.map f
  haveI := p.isPrime
  have hc : J.toIdeal.comap f.toRingHom = p.asHomogeneousIdeal.toIdeal := by
    change (p.asHomogeneousIdeal.toIdeal.map f.toRingHom).comap f.toRingHom = _
    rw [Ideal.comap_map_of_surjective (f := f.toRingHom) (Ideal.Quotient.mk_surjective)]
    change p.asHomogeneousIdeal.toIdeal ⊔ RingHom.ker f.toRingHom = _
    rw [show RingHom.ker f.toRingHom = I.toIdeal from Ideal.mk_ker]
    exact sup_eq_left.mpr hIp
  refine ⟨J, ?_, ?_⟩
  · exact Ideal.map_isPrime_of_surjective (f := f.toRingHom)
      (Ideal.Quotient.mk_surjective) (by simpa only [show RingHom.ker f.toRingHom = I.toIdeal from Ideal.mk_ker] using hIp)
  · intro hirr
    apply p.not_irrelevant_le
    apply (HomogeneousIdeal.irrelevant_le 𝒜).mpr
    intro n hn a ha
    have hm := hirr (HomogeneousIdeal.mem_irrelevant_of_mem _ hn (f.map_mem ha))
    change a ∈ J.toIdeal.comap f.toRingHom at hm
    rwa [hc] at hm

/-- The constructed quotient Proj point contracts to the original homogeneous prime. -/
theorem s2_homogeneousQuotientProjMap_point {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    (p : ProjectiveSpectrum 𝒜) (hIp : I.toIdeal ≤ p.asHomogeneousIdeal.toIdeal) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    s2_homogeneousQuotientProjMap 𝒜 I (s2_homogeneousQuotientProjPoint 𝒜 I p hIp) = p := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  change (p.asHomogeneousIdeal.toIdeal.map (Ideal.Quotient.mk I.toIdeal)).comap
    (Ideal.Quotient.mk I.toIdeal) = p.asHomogeneousIdeal.toIdeal
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change p.asHomogeneousIdeal.toIdeal ⊔ RingHom.ker (Ideal.Quotient.mk I.toIdeal) = _
  rw [Ideal.mk_ker]
  exact sup_eq_left.mpr hIp

/-- The actual homogeneous quotient Proj map has exactly the primes containing the quotient ideal as its image. -/
theorem s2_homogeneousQuotientProjMap_mem_range_iff {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜)
    (p : ProjectiveSpectrum 𝒜) :
    letI := s2_homogeneousQuotientGrading 𝒜 I
    p ∈ Set.range (s2_homogeneousQuotientProjMap 𝒜 I) ↔ I.toIdeal ≤ p.asHomogeneousIdeal.toIdeal := by
  letI := s2_homogeneousQuotientGrading 𝒜 I
  constructor
  · rintro ⟨q, rfl⟩ a ha
    change Ideal.Quotient.mk I.toIdeal a ∈ q.asHomogeneousIdeal.toIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Ideal.zero_mem _
  · intro hIp
    exact ⟨s2_homogeneousQuotientProjPoint 𝒜 I p hIp,
      s2_homogeneousQuotientProjMap_point 𝒜 I p hIp⟩

end HodgeLean.Foundations.Program
