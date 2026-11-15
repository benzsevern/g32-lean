import HodgeLean.Foundations.Program.SchoenFixedRingGrading
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Radical control of irrelevant ideals makes contraction a map on Proj points. -/
def s2_projRadicalComapFun {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical)
    (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.asHomogeneousIdeal.comap f
  isPrime := p.isPrime.comap f
  not_irrelevant_le := by
    intro h
    apply p.not_irrelevant_le
    have hm : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom ≤
        p.asHomogeneousIdeal.toIdeal := Ideal.map_le_iff_le_comap.mpr h
    exact hf.trans ((Ideal.radical_mono hm).trans_eq p.isPrime.radical)

/-- Basic opens pull back under radical-controlled contraction to their actual graded images. -/
theorem s2_projRadicalComapFun_preimage_basicOpen {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical) (a : A) :
    s2_projRadicalComapFun 𝒜 ℬ f hf ⁻¹'
      (ProjectiveSpectrum.basicOpen 𝒜 a : Set (ProjectiveSpectrum 𝒜)) =
      (ProjectiveSpectrum.basicOpen ℬ (f a) : Set (ProjectiveSpectrum ℬ)) := rfl

/-- Radical-controlled contraction of homogeneous primes is continuous. -/
def s2_projRadicalComap {A B : Type} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f.toRingHom).radical) :
    C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := s2_projRadicalComapFun 𝒜 ℬ f hf
  continuous_toFun := by
    apply (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).continuous_iff.mpr
    rintro _ ⟨a, rfl⟩
    rw [s2_projRadicalComapFun_preimage_basicOpen]
    exact ProjectiveSpectrum.isOpen_basicOpen ℬ

end HodgeLean.Foundations.Program
