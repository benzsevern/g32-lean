import HodgeLean.Foundations.Program.SchoenRescaledIdeals
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The same actual prime ideal defines corresponding Proj points under positive degree rescaling. -/
def s2_rescaledProjEquiv {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))] :
    ProjectiveSpectrum 𝒜 ≃ ProjectiveSpectrum (fun n => 𝒜 (D * n)) where
  toFun p :=
    { asHomogeneousIdeal := ⟨p.asHomogeneousIdeal.toIdeal,
        (s2_rescaled_isHomogeneous_iff 𝒜 D hD _).mp p.asHomogeneousIdeal.isHomogeneous⟩
      isPrime := p.isPrime
      not_irrelevant_le := by
        intro h
        apply p.not_irrelevant_le
        change (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p.asHomogeneousIdeal.toIdeal
        rw [s2_rescaled_irrelevant_eq 𝒜 D hD]
        exact h }
  invFun p :=
    { asHomogeneousIdeal := ⟨p.asHomogeneousIdeal.toIdeal,
        (s2_rescaled_isHomogeneous_iff 𝒜 D hD _).mpr p.asHomogeneousIdeal.isHomogeneous⟩
      isPrime := p.isPrime
      not_irrelevant_le := by
        intro h
        apply p.not_irrelevant_le
        change (HomogeneousIdeal.irrelevant (fun n => 𝒜 (D * n))).toIdeal ≤
          p.asHomogeneousIdeal.toIdeal
        rw [← s2_rescaled_irrelevant_eq 𝒜 D hD]
        exact h }
  left_inv p := by ext; rfl
  right_inv p := by ext; rfl

/-- The actual Proj topology is preserved by positive degree rescaling. -/
def s2_rescaledProjHomeomorph {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    [GradedRing (fun n => 𝒜 (D * n))] :
    ProjectiveSpectrum 𝒜 ≃ₜ ProjectiveSpectrum (fun n => 𝒜 (D * n)) where
  toEquiv := s2_rescaledProjEquiv 𝒜 D hD
  continuous_toFun := by
    apply (ProjectiveSpectrum.isTopologicalBasis_basic_opens (fun n => 𝒜 (D * n))).continuous_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact ProjectiveSpectrum.isOpen_basicOpen 𝒜
  continuous_invFun := by
    apply (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜).continuous_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact ProjectiveSpectrum.isOpen_basicOpen (fun n => 𝒜 (D * n))

end HodgeLean.Foundations.Program
