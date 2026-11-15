import HodgeLean.Adapters.IntersectionProductMovingDiagonal
import HodgeLean.Adapters.IntersectionProductDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! # The dimension inequality for intersections on a smooth variety

Every irreducible component of `closure {u} ∩ closure {v}` on a smooth integral variety over `ℂ`
has codimension at most `codim u + codim v`. On an affine chart with étale coordinates this is
`a3m_height_le_of_mem_minimalPrimes`; the generic point of the component is a minimal prime over
the sum of the primes of `u` and `v`.

Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, Théorème 3; Hartshorne, *Algebraic
Geometry*, I, Proposition 7.1. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Adapters

attribute [local instance] overSpecAlgebra

/-- The generic point of a component of a closed subscheme with support `closure {u} ∩ closure {v}`
is a maximal point of `closure {u} ∩ closure {v}`. -/
theorem a3m_component_spec_of_support {X : Scheme} (u v : X) (J : X.IdealSheafData)
    (hJ : (J.support : Set X) = closure {u} ∩ closure {v}) (w : J.subscheme)
    (hw : closure ({w} : Set J.subscheme) ∈ irreducibleComponents J.subscheme) :
    u ⤳ J.subschemeι w ∧ v ⤳ J.subschemeι w ∧
      ∀ z' : X, u ⤳ z' → v ⤳ z' → z' ⤳ J.subschemeι w → z' = J.subschemeι w := by
  have hrange : Set.range J.subschemeι = closure {u} ∩ closure {v} := by
    rw [Scheme.IdealSheafData.range_subschemeι, hJ]
  have hemb := J.subschemeι.isClosedEmbedding
  have hmem : J.subschemeι w ∈ closure {u} ∩ closure {v} := hrange ▸ ⟨w, rfl⟩
  refine ⟨specializes_iff_mem_closure.2 hmem.1, specializes_iff_mem_closure.2 hmem.2, ?_⟩
  intro z' hu hv hz'
  obtain ⟨w', rfl⟩ : z' ∈ Set.range J.subschemeι :=
    hrange ▸ ⟨specializes_iff_mem_closure.1 hu, specializes_iff_mem_closure.1 hv⟩
  have hww' : w' ⤳ w := hemb.isInducing.specializes_iff.1 hz'
  have hsub : closure ({w} : Set J.subscheme) ⊆ closure {w'} :=
    closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hww'))
      isClosed_closure
  have heq := hw.2 isIrreducible_singleton.closure hsub
  have hw'w : w ⤳ w' := specializes_iff_mem_closure.2 (heq (subset_closure rfl))
  rw [(hww'.antisymm hw'w).eq]

/-- The support of `I_u ⊔ I_v` is `closure {u} ∩ closure {v}`. -/
theorem a3m_support_sup_primeIdeal {X : Scheme} (u v : X) :
    ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).support : Set X) =
      closure {u} ∩ closure {v} := by
  rw [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf, ccm3_primeIdeal,
    ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The generic point of a component of `closure {u} ∩ closure {v}` is a maximal point of it. -/
theorem a3m_component_spec {X : Scheme} (u v : X)
    (w : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) :
    u ⤳ (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w ∧
      v ⤳ (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w ∧
      ∀ z' : X, u ⤳ z' → v ⤳ z' → z' ⤳ (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w →
        z' = (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w :=
  a3m_component_spec_of_support u v _ (a3m_support_sup_primeIdeal u v) w hw

/-- The dimension inequality for intersections on a smooth integral variety over `ℂ`: every
irreducible component of `closure {u} ∩ closure {v}` has codimension at most
`codim u + codim v`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, Théorème 3 (reduction to the
diagonal); Hartshorne, *Algebraic Geometry*, I, Proposition 7.1. -/
theorem a3m_coheight_component_le_of_smooth (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (u v : X.left)
    (w : (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subscheme) :
    Order.coheight ((ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι w) ≤
      Order.coheight u + Order.coheight v := by
  obtain ⟨huz, hvz, hmin⟩ := a3m_component_spec u v w hw
  set z := (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι w
  obtain ⟨d, hd⟩ := Smooth.exists_smoothOfRelativeDimension X.hom
  obtain ⟨V, hV, hzV, hf⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := d) X.hom z
  have hf' := algebraMap_isStandardSmoothOfRelativeDimension (d := d) X hf
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hdim : ringKrullDim Γ(X.left, V) = d := hf'.ringKrullDim_eq_complex
  obtain ⟨g, hgC, hg⟩ := hf'.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) ℂ) Γ(X.left, V) := g.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) Γ(X.left, V) :=
    IsScalarTower.of_algebraMap_eq' hgC.symm
  have : Algebra.Etale (MvPolynomial (Fin d) ℂ) Γ(X.left, V) := RingHom.etale_algebraMap.mp hg
  have : Algebra.FiniteType ℂ Γ(X.left, V) :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin d) ℂ) inferInstance inferInstance
  -- points of `V` as primes of `S`
  have hrange : Set.range hV.fromSpec = V := hV.range_fromSpec
  have hemb := hV.fromSpec.isOpenEmbedding
  have hpt : ∀ x ∈ V, ∃ p : Spec Γ(X.left, V), hV.fromSpec p = x := by
    intro x hx
    have : x ∈ Set.range hV.fromSpec := hrange ▸ hx
    exact this
  obtain ⟨pz, hpz⟩ := hpt z hzV
  obtain ⟨pu, hpu⟩ := hpt u (huz.mem_open V.isOpen hzV)
  obtain ⟨pv, hpv⟩ := hpt v (hvz.mem_open V.isOpen hzV)
  have hle : ∀ p q : Spec Γ(X.left, V), hV.fromSpec p ⤳ hV.fromSpec q ↔ p.asIdeal ≤ q.asIdeal :=
    fun p q => hemb.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes p q).symm
  have hcoh : ∀ p : Spec Γ(X.left, V), Order.coheight (hV.fromSpec p) = p.asIdeal.height := by
    intro p
    rw [idealHeight_eq_coheight Γ(X.left, V) p]
    exact coheight_eq_of_isOpenImmersion (x := p) hV.fromSpec
  have hR : pz.asIdeal ∈ (pu.asIdeal ⊔ pv.asIdeal).minimalPrimes := by
    refine ⟨⟨pz.isPrime, sup_le ((hle pu pz).1 (hpu ▸ hpz ▸ huz))
      ((hle pv pz).1 (hpv ▸ hpz ▸ hvz))⟩, fun R' hR' hR'z => ?_⟩
    obtain ⟨hR'prime, hR'le⟩ := hR'
    let p' : Spec Γ(X.left, V) := ⟨R', hR'prime⟩
    have h1 : u ⤳ hV.fromSpec p' := hpu ▸ (hle pu p').2 (le_sup_left.trans hR'le)
    have h2 : v ⤳ hV.fromSpec p' := hpv ▸ (hle pv p').2 (le_sup_right.trans hR'le)
    have h3 : hV.fromSpec p' ⤳ z := hpz ▸ (hle p' pz).2 hR'z
    have := hmin _ h1 h2 h3
    rw [← hpz] at this
    have hp : p' = pz := hemb.injective this
    rw [← hp]
  have := pu.isPrime
  have := pv.isPrime
  have key := a3m_height_le_of_mem_minimalPrimes (k := ℂ) d hdim pu.asIdeal pv.asIdeal
    pz.asIdeal hR
  rw [← hpz, ← hpu, ← hpv, hcoh, hcoh, hcoh]
  exact key

end HodgeLean.Adapters
