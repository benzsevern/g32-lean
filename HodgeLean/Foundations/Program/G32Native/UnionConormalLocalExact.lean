import HodgeLean.Foundations.Program.G32Native.UnionConormalRestrictionExact
import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalZero
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Detecting module exactness on open neighborhoods -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Exactness of a module complex can be checked on open neighborhoods. -/
lemma unionConormal_exact_of_open_neighborhoods {X : Scheme.{0}}
    (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  apply unionConormal_isZero_of_open_neighborhoods
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  letI := unionConormal_restrict_preservesFiniteLimits U.ι
  refine ⟨U, hx, ?_⟩
  exact ((S.map (Scheme.Modules.restrictFunctor U.ι)).exact_iff_isZero_homology.mp hU).of_iso
    (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm

/-- A module map is monic if it is monic on neighborhoods of every point. -/
lemma unionConormal_mono_of_open_neighborhoods {X : Scheme.{0}}
    {M N : X.Modules} (a : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map a)) : Mono a := by
  apply Preadditive.mono_of_isZero_kernel
  apply unionConormal_isZero_of_open_neighborhoods
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  letI := unionConormal_restrict_preservesFiniteLimits U.ι
  letI := hU
  refine ⟨U, hx, ?_⟩
  exact (isZero_kernel_of_mono ((Scheme.Modules.restrictFunctor U.ι).map a)).of_iso
    (asIso (kernelComparison a (Scheme.Modules.restrictFunctor U.ι)))

/-- A module map is epic if it is epic on neighborhoods of every point. -/
lemma unionConormal_epi_of_open_neighborhoods {X : Scheme.{0}}
    {M N : X.Modules} (a : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.restrictFunctor U.ι).map a)) : Epi a := by
  apply Preadditive.epi_of_isZero_cokernel
  apply unionConormal_isZero_of_open_neighborhoods
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  letI := hU
  refine ⟨U, hx, ?_⟩
  exact (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor U.ι).map a)).of_iso
    (asIso (cokernelComparison a (Scheme.Modules.restrictFunctor U.ι))).symm

/-- Short exactness of a module complex can be checked on open neighborhoods. -/
lemma unionConormal_shortExact_of_open_neighborhoods {X : Scheme.{0}}
    (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).ShortExact) : S.ShortExact where
  exact := unionConormal_exact_of_open_neighborhoods S (fun x => by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, hU.exact⟩)
  mono_f := unionConormal_mono_of_open_neighborhoods S.f (fun x => by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, hU.mono_f⟩)
  epi_g := unionConormal_epi_of_open_neighborhoods S.g (fun x => by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, hU.epi_g⟩)

end HodgeLean.Foundations.Program.G32Native
