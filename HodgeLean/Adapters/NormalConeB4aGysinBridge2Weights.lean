import HodgeLean.Adapters.NormalConeB4aGysinBridge2GoodOpen
import HodgeLean.Adapters.NormalConeB4aGysinBridge2Defs
import HodgeLean.Adapters.NormalConeB4aGysinStalkLength

/-! # Reformulated bridge of A3-B4a: generic component weights

Away from a closed set containing no generic point of an irreducible component, the exact
length of a slice of `dim 𝒪_{K,w}` elements generating the maximal ideal modulo the nilradical
equals the multiplicity of the cycle of `K` at the point. Source: Fulton, *Intersection Theory*,
§1.5, Lemma A.2 and Example 7.1.10; Matsumura, *Commutative Ring Theory*, Theorem 4.10. -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry IsLocalRing

/-- Every point of a quasi-sober space lies in the closure of the generic point of some
irreducible component. -/
theorem a3b4g_exists_genericPoint_specializes {K : Scheme.{0}} (w : K) :
    ∃ ζ ∈ genericPoints K, w ∈ closure ({ζ} : Set K) := by
  obtain ⟨u, hu, hwu⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({w} : Set K) isIrreducible_singleton
  have hirr : IsIrreducible u := hu.1
  have hgen := hirr.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents u hu).closure_eq] at hgen
  refine ⟨hirr.genericPoint, ?_, ?_⟩
  · change closure {hirr.genericPoint} ∈ irreducibleComponents K
    rw [hgen.def]
    exact hu
  · rw [hgen.def]
    exact hwu rfl

/-- Distinct generic points of irreducible components do not specialize to each other. -/
theorem a3b4g_not_mem_closure_of_genericPoints {K : Scheme.{0}} {η η' : K}
    (hη : η ∈ genericPoints K) (hne : η' ≠ η) :
    η ∉ closure ({η'} : Set K) := by
  intro h
  have hsub : closure ({η} : Set K) ⊆ closure {η'} :=
    closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure
  have hle := hη.2 isIrreducible_singleton.closure hsub
  have heq : closure ({η'} : Set K) = closure {η} := le_antisymm hle hsub
  exact hne ((inseparable_iff_closure_eq.mpr heq).eq)

/-- Generic component weights: away from a closed set containing no generic point, exact slice
lengths of `dim 𝒪_{K,w}` elements generating the maximal ideal modulo the nilradical are the
multiplicities of the cycle of `K`. Source: Fulton, *Intersection Theory*, Lemma A.2 and
Example 7.1.10. -/
theorem a3b4g_generic_component_weights_core
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (hi : IsClosedImmersion i) :
    ∃ B : Set K, IsClosed B ∧ (∀ x ∈ B, closure {x} ∉ irreducibleComponents K) ∧
      ∀ w : ComplexPoint (Over.mk (i ≫ q)), w.underlying ∉ B →
      ∀ (U : Z.Opens) {n : ℕ} (g : Fin n → Γ(Z, U)) (a : Fin n → ℂ)
        (hw : i.base w.underlying ∈ U),
        ringKrullDim (K.presheaf.stalk w.underlying) = n →
        a3b4g_sliceIdeal q i U g a w.underlying hw ⊔ nilradical (K.presheaf.stalk w.underlying) =
          IsLocalRing.maximalIdeal (K.presheaf.stalk w.underlying) →
        ∃ k : ℕ, a3b4a_gysin_sliceLength q i U g a w = k ∧
          a3b4_multiplicity q (a3b3_imageCycle i inferInstance) (a3b4_anMap (q := i ≫ q) (q' := q)
            i rfl w) = k := by
  classical
  haveI : IsClosedImmersion i := hi
  haveI : IsLocallyNoetherian K := LocallyOfFiniteType.isLocallyNoetherian i
  haveI : CompactSpace K := (quasiCompact_iff_compactSpace i).1 inferInstance
  haveI : IsNoetherian K := {}
  have hfin : (genericPoints K).Finite := by
    refine Set.Finite.preimage ?_ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
    intro x _ y _ hxy
    exact (inseparable_iff_closure_eq.mpr hxy).eq
  choose! W hηW m hm hsl using fun η (hη : η ∈ genericPoints K) =>
    a3b4g_exists_good_open_of_generic η hη
  let W' : K → Set K := fun η =>
    (W η : Set K) ∩ ⋂ η' ∈ genericPoints K \ {η}, (closure ({η'} : Set K))ᶜ
  have hW' : ∀ η, IsOpen (W' η) := fun η =>
    (W η).2.inter ((hfin.diff).isOpen_biInter fun _ _ => isClosed_closure.isOpen_compl)
  have hηW' : ∀ η ∈ genericPoints K, η ∈ W' η := by
    intro η hη
    refine ⟨hηW η hη, Set.mem_iInter₂.mpr fun η' hη' => ?_⟩
    exact a3b4g_not_mem_closure_of_genericPoints hη hη'.2
  refine ⟨(⋃ η ∈ genericPoints K, W' η)ᶜ, (isOpen_biUnion fun η _ => hW' η).isClosed_compl,
    ?_, ?_⟩
  · intro x hx hcomp
    exact hx (Set.mem_iUnion₂.mpr ⟨x, hcomp, hηW' x hcomp⟩)
  · intro w hwB U n g a hw hdim hgen
    obtain ⟨η, hη, hwW⟩ := Set.mem_iUnion₂.mp (not_not.mp hwB)
    let rs := a3b4a_gysin_sliceSequence q i U g a w.underlying hw
    have hlen : rs.length = n := List.length_ofFn
    have hL := hsl η hη w.underlying hwW.1 rs (by rw [hdim, hlen]) hgen
    have hwη : w.underlying ∈ closure ({η} : Set K) := by
      obtain ⟨ζ, hζ, hwζ⟩ := a3b4g_exists_genericPoint_specializes w.underlying
      by_cases h : ζ = η
      · exact h ▸ hwζ
      · exact absurd hwζ (Set.mem_iInter₂.mp hwW.2 ζ ⟨hζ, h⟩)
    refine ⟨m η, ?_, ?_⟩
    · simp only [a3b4a_gysin_sliceLength, hw, ↓reduceDIte]
      exact hL
    · have hx : (a3b4_anMap (q := i ≫ q) (q' := q) i rfl w).underlying ∈
          closure ({i η} : Set Z) := by
        change i.base w.underlying ∈ _
        exact specializes_iff_mem_closure.mp
          ((specializes_iff_mem_closure.mpr hwη).map i.continuous)
      have hother : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, ξ ≠ i η →
          (a3b4_anMap (q := i ≫ q) (q' := q) i rfl w).underlying ∉ closure ({ξ} : Set Z) := by
        intro ξ hξ hne
        rw [a3b3_imageCycle, a3b4a_gysin_idealCycle_support] at hξ
        obtain ⟨y', hy', rfl⟩ := hξ
        let y := (Scheme.homeoOfIso (asIso i.toImage)).symm y'
        have hyy : i.toImage y = y' := (Scheme.homeoOfIso (asIso i.toImage)).apply_symm_apply y'
        have hpt : i.ker.subschemeι y' = i y := by
          rw [← hyy, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
        have hyg : y ∈ genericPoints K := by
          rw [← a3b2_homeomorph_mem_genericPoints (Scheme.homeoOfIso (asIso i.toImage)) y]
          change i.toImage y ∈ _
          rw [hyy]
          exact hy'
        have hyη : y ≠ η := by
          rintro rfl
          exact hne hpt
        rw [hpt]
        change i.base w.underlying ∉ _
        intro hcl
        have hsp : i y ⤳ i w.underlying := specializes_iff_mem_closure.mpr hcl
        rw [(IsClosedImmersion.isClosedEmbedding i).isInducing.specializes_iff] at hsp
        exact (Set.mem_iInter₂.mp hwW.2 y ⟨hyg, hyη⟩) (specializes_iff_mem_closure.mp hsp)
      rw [a3b4a_gysin_multiplicity_eq_source_stalkLength q i η hη _ hx hother, hm η hη]
      simp

end HodgeLean.Adapters
