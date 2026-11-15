import HodgeLean.Adapters.NormalConeB4aGysinBridge2GenericLength
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Reformulated bridge of A3-B4a: good opens around generic points

On a locally Noetherian scheme, every generic point `η` of an irreducible component has an open
neighbourhood `W` such that at every point `w ∈ W` each list of `dim 𝒪_w` elements generating the
maximal ideal of `𝒪_w` together with the nilradical has slice length equal to the length of the
Artinian local ring `𝒪_η`. Source: Fulton, *Intersection Theory*, Lemma A.2 and Example 7.1.10;
Hartshorne, *Algebraic Geometry*, §II.2. -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry IsLocalRing

/-- The generic point of an irreducible component is maximal for the specialization order. -/
theorem a3b4g_isMax_of_mem_genericPoints {K : Scheme.{0}} (η : K) (hη : η ∈ genericPoints K) :
    IsMax η := by
  intro y hy
  rw [Scheme.le_iff_specializes] at hy ⊢
  have hsub : closure ({η} : Set K) ⊆ closure {y} := specializes_iff_closure_subset.mp hy
  have hle := hη.2 isIrreducible_singleton.closure hsub
  exact specializes_iff_mem_closure.mpr (hle (subset_closure rfl))

/-- A generic point of a locally Noetherian scheme has a neighbourhood on which every slice of
`dim 𝒪_w` elements generating the maximal ideal modulo the nilradical has the generic length.
Source: Fulton, *Intersection Theory*, Lemma A.2. -/
theorem a3b4g_exists_good_open_of_generic {K : Scheme.{0}} [IsLocallyNoetherian K] (η : K)
    (hη : η ∈ genericPoints K) :
    ∃ W : K.Opens, η ∈ W ∧ ∃ m : ℕ,
      Module.length (K.presheaf.stalk η) (K.presheaf.stalk η) = m ∧
      ∀ w ∈ W, ∀ rs : List (K.presheaf.stalk w), ringKrullDim (K.presheaf.stalk w) = rs.length →
        Ideal.ofList rs ⊔ nilradical (K.presheaf.stalk w) = maximalIdeal (K.presheaf.stalk w) →
        Module.length (K.presheaf.stalk w) (K.presheaf.stalk w ⧸ Ideal.ofList rs) = m := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ :=
    K.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  haveI : IsNoetherianRing Γ(K, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set P := (hV.primeIdealOf ⟨η, hηV⟩).asIdeal with hPdef
  letI := K.presheaf.algebra_section_stalk ⟨η, hηV⟩
  haveI hlocη : IsLocalization.AtPrime (K.presheaf.stalk η) P := hV.isLocalization_stalk ⟨η, hηV⟩
  have hP : P ∈ minimalPrimes Γ(K, V) := by
    rw [← Ideal.height_eq_zero_iff]
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height P (K.presheaf.stalk η)
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr
      (a3b4g_isMax_of_mem_genericPoints η hη)] at h1
    exact_mod_cast h1.symm
  obtain ⟨g, hgP, -, m, hlen0, hslice⟩ := a3b4g_exists_basicOpen_slice_length P hP
  refine ⟨K.basicOpen g, ?_, m, hlen0 (K.presheaf.stalk η), ?_⟩
  · rw [Scheme.mem_basicOpen K g η hηV]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (K.presheaf.stalk η) P g).mpr hgP
  · intro w hw rs hdim hgen
    have hwV : w ∈ V := K.basicOpen_le g hw
    letI := K.presheaf.algebra_section_stalk ⟨w, hwV⟩
    haveI : IsLocalization.AtPrime (K.presheaf.stalk w) (hV.primeIdealOf ⟨w, hwV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨w, hwV⟩
    have hgQ : g ∉ (hV.primeIdealOf ⟨w, hwV⟩).asIdeal := by
      have hu := (Scheme.mem_basicOpen K g w hwV).mp hw
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (K.presheaf.stalk w) _ g).mp hu
    exact hslice _ (K.presheaf.stalk w) hgQ rs hdim hgen

end HodgeLean.Adapters
