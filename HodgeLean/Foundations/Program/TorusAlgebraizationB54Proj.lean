import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program

variable {A σ : Type*} [CommRing A] [IsDomain A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem b54_proj_integral_of_domain
    (h : ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ ⊥) : IsIntegral (Proj 𝒜) := by
  let hdomains (p : ProjectiveSpectrum 𝒜) :
      IsDomain (HomogeneousLocalization.AtPrime 𝒜 p.asHomogeneousIdeal.toIdeal) :=
    Function.Injective.isDomain
      (algebraMap (HomogeneousLocalization.AtPrime 𝒜 p.asHomogeneousIdeal.toIdeal)
        (Localization p.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective _)
  letI : IsReduced (Proj 𝒜) := by
    constructor
    intro U
    change _root_.IsReduced (ProjectiveSpectrum.StructureSheaf.sectionsSubring
      (𝒜 := 𝒜) (Opposite.op U))
    constructor
    intro s hs
    apply Subtype.ext
    funext x
    obtain ⟨n, hn⟩ := hs
    have he : s.val x ^ n = 0 :=
      congrArg (fun t : ProjectiveSpectrum.StructureSheaf.sectionsSubring
        (𝒜 := 𝒜) (Opposite.op U) ↦ t.val x) hn
    letI := hdomains x.val
    exact (IsNilpotent.mk _ n he).eq_zero
  let p : ProjectiveSpectrum 𝒜 := ⟨⊥, Ideal.isPrime_bot, h⟩
  have hp : closure ({p} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    apply (ProjectiveSpectrum.le_iff_mem_closure 𝒜 p q).mp
    change (⊥ : HomogeneousIdeal 𝒜) ≤ q.asHomogeneousIdeal
    exact bot_le
  letI : IrreducibleSpace (Proj 𝒜) := by
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
    rw [← hp]
    exact isIrreducible_singleton.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end HodgeLean.Foundations.Program
