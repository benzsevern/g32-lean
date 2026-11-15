import HodgeLean.Foundations.QuotientDuality.ProperCyclePartialChartLocalHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartCoclassComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadLocalHomology

/-! # Local caps on the literal source of a partial complex chart

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

private lemma chart_puncture_union
    {M : TopCat.{0}} (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source) (hex : e x = (0, 0))
    (W : Set M) (hW : W ⊆ e.source) (hxW : x ∈ W) :
    ({w : W | (e w.val).2 ≠ 0} : Set W) ∪ {w : W | (e w.val).1 ≠ 0} =
      ({⟨x, hxW⟩} : Set W)ᶜ := by
  ext w
  change ((e w.val).2 ≠ 0 ∨ (e w.val).1 ≠ 0) ↔ w ≠ ⟨x, hxW⟩
  rw [← not_and_or]
  apply not_congr
  constructor
  · intro h
    apply Subtype.ext
    apply e.injOn (hW w.property) hx
    exact (Prod.ext h.2 h.1).trans hex.symm
  · intro h
    have hew : e w.val = (0, 0) := (congrArg (fun z : W => e z.val) h).trans hex
    exact ⟨congrArg Prod.snd hew, congrArg Prod.fst hew⟩

/-- The original triad cap on an actual chart neighborhood, followed by the literal tangential projection to its point-complement pair. Its input ambient class uses actual point excision.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, local relative cap and excision.
HC no distance; AV milestone no distance. -/
def properCycle_partial_chart_cap
    {M : TopCat.{0}} [T1Space M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source) (hex : e x = (0, 0))
    (W : Set M) (hW : W ⊆ e.source) (hWo : IsOpen W) (hxW : x ∈ W) :
    RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of W)
      {w : W | (e w.val).2 ≠ 0}) (2 * d) →ₗ[ℚ]
      (orientationGroup M (2 * (r + d)) x →ₗ[ℚ]
        orientationGroup (TopCat.of (Fin r → ℂ)) (2 * r) 0) := by
  let X := TopCat.of W
  let A : Set X := {w | (e w.val).2 ≠ 0}
  let B : Set X := {w | (e w.val).1 ≠ 0}
  have hec : Continuous (fun w : W => e w.val) :=
    (e.continuousOn.mono hW).domRestrict
  have hAo : IsOpen A := isClosed_singleton.isOpen_compl.preimage hec.snd
  have hBo : IsOpen B := isClosed_singleton.isOpen_compl.preimage hec.fst
  let i := properCycle_triad_local_homology_iso X A B hAo hBo ⟨x, hxW⟩
    (chart_puncture_union r d e x hx hex W hW hxW) (2 * d + 2 * r)
  let j := neighborhoodPointComplementRelativeHomologyIso W x hWo hxW (2 * (r + d))
  let pointPair : neighborhoodPointComplementPair W x ≅ pointComplementPair (⟨x, hxW⟩ : W) :=
    TopPair.isoOfSubset (Homeomorph.refl W) (by
      intro w
      change w ≠ ⟨x, hxW⟩ ↔ w.val ≠ x
      exact not_congr Subtype.ext_iff)
  let pointHomology := (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) (2 * (r + d))).mapIso ((relativeChainFunctor ℚ).mapIso pointPair)
  let degree : orientationGroup X (2 * (r + d)) ⟨x, hxW⟩ ≅
      orientationGroup X (2 * d + 2 * r) ⟨x, hxW⟩ :=
    eqToIso (congrArg (fun n => orientationGroup X n ⟨x, hxW⟩) (by omega))
  let p : TopPair.ofSubset (X := X) B ⟶ puncturedPair ℂ r :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨fun w => (e w.val).1, hec.fst⟩)
      (fun _ h => h)
  let K := triadCapCohomologyLinear ℚ X A B (2 * d) (2 * r)
  let input := i.inv.hom.comp (degree.hom.hom.comp (pointHomology.hom.hom.comp j.inv.hom))
  let output := relativeHomologyMap ℚ (2 * r) p
  exact
    { toFun := fun a => output.comp ((K a).comp input)
      map_add' := by intro a b; ext c; simp [map_add]
      map_smul' := by intro t a; ext c; simp [map_smul] }

/-- A chart neighborhood that itself has full product coordinates gives an invertible original local cap for the pulled-back standard normal coclass.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative homotopy invariance and cap naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_partial_chart_cap_bijective
    {M : TopCat.{0}} [T1Space M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source) (hex : e x = (0, 0))
    (W : Set M) (hW : W ⊆ e.source) (hWo : IsOpen W) (hxW : x ∈ W)
    (E : W ≃ₜ ((Fin r → ℂ) × (Fin d → ℂ))) (hE : ∀ w : W, E w = e w.val) :
    let A : Set W := {w | (e w.val).2 ≠ 0}
    let C : Set ((Fin r → ℂ) × (Fin d → ℂ)) := {z | z.2 ≠ 0}
    let hAC : ∀ w : W, E w ∈ C ↔ w ∈ A := fun w => by rw [hE w]; rfl
    Function.Bijective (properCycle_partial_chart_cap r d e x hx hex W hW hWo hxW
      (relativeCohomologyMap ℚ (2 * d) (TopPair.isoOfSubset E hAC).hom
        (relativeCohomologyMap ℚ (2 * d)
          (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
          (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
            (standardComplexLocalClass_ne_zero_for_chart d))))) := by
  dsimp only
  let X := TopCat.of W
  let Y := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))
  let A : Set X := {w | (e w.val).2 ≠ 0}
  let B : Set X := {w | (e w.val).1 ≠ 0}
  let C : Set Y := {z | z.2 ≠ 0}
  let D : Set Y := {z | z.1 ≠ 0}
  have hec : Continuous (fun w : W => e w.val) := (e.continuousOn.mono hW).domRestrict
  have hAo : IsOpen A := isClosed_singleton.isOpen_compl.preimage hec.snd
  have hBo : IsOpen B := isClosed_singleton.isOpen_compl.preimage hec.fst
  have hAC : ∀ w : W, E w ∈ C ↔ w ∈ A := fun w => by rw [hE w]; rfl
  have hBD : ∀ w : W, E w ∈ D ↔ w ∈ B := fun w => by rw [hE w]; rfl
  let a := relativeCohomologyMap ℚ (2 * d)
    (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
    (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
      (standardComplexLocalClass_ne_zero_for_chart d))
  have hcap := properCycle_homeomorph_triad_cap_bijective (X := X) (Y := Y) E A B C D
    hAC hBD hAo hBo
    (isClosed_singleton.isOpen_compl.preimage continuous_snd)
    (isClosed_singleton.isOpen_compl.preimage continuous_fst)
    (2 * d) (2 * r) a (properCycle_standard_complex_product_triad_cap_bijective r d)
  let eB := TopPair.isoOfSubset (X := X) (Y := Y) (A := B) (B := D) E hBD
  let pY : TopPair.ofSubset (X := Y) D ⟶ puncturedPair ℂ r :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (fun _ h => h)
  let pX : TopPair.ofSubset (X := X) B ⟶ puncturedPair ℂ r :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨fun w => (e w.val).1, hec.fst⟩) (fun _ h => h)
  let swap : TopPair.ofSubset (X := Y) D ≅
      TopPair.ofSubset (X := TopCat.of ((Fin d → ℂ) × (Fin r → ℂ)))
        (Prod.snd ⁻¹' ({0} : Set (Fin r → ℂ))ᶜ) :=
    TopPair.isoOfSubset (Homeomorph.prodComm _ _) (fun _ => Iff.rfl)
  have hpY : Function.Bijective (relativeHomologyMap ℚ (2 * r) pY) := by
    have hs : Function.Bijective (relativeHomologyMap ℚ (2 * r) swap.hom) :=
      ConcreteCategory.bijective_of_isIso
        (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map swap.hom) (2 * r))
    have hp := (properCycle_product_support_homology_iso (Fin d → ℂ)
      (TopCat.of (Fin r → ℂ)) {0} (2 * r)).toLinearEquiv.bijective
    have heq : swap.hom ≫ properCycle_product_support_projection (Fin d → ℂ)
        (TopCat.of (Fin r → ℂ)) {0} = pY := by ext z : 2 <;> rfl
    change Function.Bijective (relativeHomologyMap ℚ (2 * r)
      (properCycle_product_support_projection (Fin d → ℂ) (TopCat.of (Fin r → ℂ)) {0})) at hp
    have h := hp.comp hs
    change Function.Bijective ((relativeHomologyMap ℚ (2 * r)
      (properCycle_product_support_projection (Fin d → ℂ) (TopCat.of (Fin r → ℂ)) {0})).comp
      (relativeHomologyMap ℚ (2 * r) swap.hom)) at h
    rw [← relativeHomologyMap_comp, heq] at h
    exact h
  have hpX : Function.Bijective (relativeHomologyMap ℚ (2 * r) pX) := by
    have hi : Function.Bijective (relativeHomologyMap ℚ (2 * r) eB.hom) :=
      ConcreteCategory.bijective_of_isIso
        (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map eB.hom) (2 * r))
    have heq : eB.hom ≫ pY = pX := by
      ext z : 2
      · apply Subtype.ext
        exact congrArg Prod.fst (hE z.val)
      · exact congrArg Prod.fst (hE z)
    have h := hpY.comp hi
    change Function.Bijective ((relativeHomologyMap ℚ (2 * r) pY).comp
      (relativeHomologyMap ℚ (2 * r) eB.hom)) at h
    rw [← relativeHomologyMap_comp, heq] at h
    exact h
  unfold properCycle_partial_chart_cap
  dsimp only
  apply hpX.comp
  apply hcap.comp
  let i := properCycle_triad_local_homology_iso X A B hAo hBo ⟨x, hxW⟩
    (chart_puncture_union r d e x hx hex W hW hxW) (2 * d + 2 * r)
  let j := neighborhoodPointComplementRelativeHomologyIso W x hWo hxW (2 * (r + d))
  let pointPair : neighborhoodPointComplementPair W x ≅ pointComplementPair (⟨x, hxW⟩ : W) :=
    TopPair.isoOfSubset (Homeomorph.refl W) (by
      intro w
      change w ≠ ⟨x, hxW⟩ ↔ w.val ≠ x
      exact not_congr Subtype.ext_iff)
  let pointHomology := (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) (2 * (r + d))).mapIso ((relativeChainFunctor ℚ).mapIso pointPair)
  let degree : orientationGroup X (2 * (r + d)) ⟨x, hxW⟩ ≅
      orientationGroup X (2 * d + 2 * r) ⟨x, hxW⟩ :=
    eqToIso (congrArg (fun n => orientationGroup X n ⟨x, hxW⟩) (by omega))
  exact (ConcreteCategory.bijective_of_isIso i.inv).comp
    ((ConcreteCategory.bijective_of_isIso degree.hom).comp
      ((ConcreteCategory.bijective_of_isIso pointHomology.hom).comp
        (ConcreteCategory.bijective_of_isIso j.inv)))

example {M : TopCat.{0}} [T1Space M] (r d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin d → ℂ)))
    (x : M) (hx : x ∈ e.source) (hex : e x = (0, 0))
    (W : Set M) (hW : W ⊆ e.source) (hWo : IsOpen W) (hxW : x ∈ W) :
    properCycle_partial_chart_cap r d e x hx hex W hW hWo hxW 0 = 0 := map_zero _

end HodgeLean.Foundations.QuotientDuality
