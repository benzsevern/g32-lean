import HodgeLean.Adapters.NormalConeB2Defs

/-! # Fundamental cycles along closed immersions

The fundamental cycle of a closed subscheme depends only on the subscheme up to isomorphism
over the ambient scheme: an isomorphism preserves generic points and local rings, so it
preserves generic lengths. For a closed immersion `g : Z ⟶ Y`, the fundamental cycle of
`ker g` is the push-forward of the fundamental cycle of `Z` along the points of `g`.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry

universe u

/-- Isomorphic rings have the same length over themselves.
Source: Mathlib, `Module.coe_length` and `Order.krullDim_eq_of_orderIso`. -/
theorem a3b2_length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso
    (Ideal.relIsoOfBijective (e : R →+* S) e.bijective)).symm

/-- A homeomorphism carries irreducible components to irreducible components.
Source: Mathlib, `image_mem_irreducibleComponents_of_isPreirreducible_fiber`. -/
theorem a3b2_image_mem_irreducibleComponents {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) {T : Set α} (hT : T ∈ irreducibleComponents α) :
    h '' T ∈ irreducibleComponents β :=
  image_mem_irreducibleComponents_of_isPreirreducible_fiber h h.continuous h.isOpenMap
    (fun y => (Set.subsingleton_singleton.preimage h.injective).isPreirreducible) h.surjective hT

/-- A homeomorphism carries generic points to generic points.
Source: Mathlib, `Homeomorph.image_closure` and `genericPoints`. -/
theorem a3b2_homeomorph_mem_genericPoints {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) (x : α) :
    h x ∈ genericPoints β ↔ x ∈ genericPoints α := by
  have e : ∀ {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] (h : α ≃ₜ β) (x : α),
      closure ({h x} : Set β) = h '' closure {x} := fun h x => by
    rw [h.image_closure, Set.image_singleton]
  constructor
  · intro hx
    change closure {x} ∈ irreducibleComponents α
    have := a3b2_image_mem_irreducibleComponents h.symm hx
    rwa [e, ← Set.image_comp, Homeomorph.symm_comp_self, Set.image_id] at this
  · intro hx
    change closure {h x} ∈ irreducibleComponents β
    rw [e]
    exact a3b2_image_mem_irreducibleComponents h hx

/-- The fundamental cycle vanishes off the images of the generic points.
Source: definition `a3b2_idealCycle`. -/
theorem a3b2_idealCycle_apply_eq_zero {Y : Scheme.{u}} (J : Y.IdealSheafData)
    (hc : (irreducibleComponents J.subscheme).Finite)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤)
    (w : Y) (hw : ∀ y ∈ genericPoints J.subscheme, J.subschemeι y ≠ w) :
    a3b2_idealCycle J hc hl w = 0 := by
  classical
  rw [a3b2_idealCycle]
  simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right_iff]
  intro h
  exact ((hw y.1 ((Set.Finite.mem_toFinset _).1 y.2)) h.symm).elim

/-- The fundamental cycle is transported along an isomorphism of closed subschemes over an
injective map of ambient schemes.
Source: Fulton, *Intersection Theory*, second edition, §1.5; theorems
`a3b2_homeomorph_mem_genericPoints` and `a3b2_length_eq_of_ringEquiv`. -/
theorem a3b2_idealCycle_transfer {Y₁ Y₂ : Scheme.{u}} (J₁ : Y₁.IdealSheafData)
    (J₂ : Y₂.IdealSheafData) (φ : Y₂ ⟶ Y₁) (hφ : Function.Injective φ)
    (s : J₂.subscheme ≅ J₁.subscheme) (hs : s.hom ≫ J₁.subschemeι = J₂.subschemeι ≫ φ)
    (hc₁ : (irreducibleComponents J₁.subscheme).Finite)
    (hl₁ : ∀ y ∈ genericPoints J₁.subscheme,
      Module.length (J₁.subscheme.presheaf.stalk y) (J₁.subscheme.presheaf.stalk y) ≠ ⊤)
    (hc₂ : (irreducibleComponents J₂.subscheme).Finite)
    (hl₂ : ∀ y ∈ genericPoints J₂.subscheme,
      Module.length (J₂.subscheme.presheaf.stalk y) (J₂.subscheme.presheaf.stalk y) ≠ ⊤)
    (w : Y₂) : a3b2_idealCycle J₁ hc₁ hl₁ (φ w) = a3b2_idealCycle J₂ hc₂ hl₂ w := by
  have hpt : ∀ y, J₁.subschemeι (s.hom y) = φ (J₂.subschemeι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hs, Scheme.Hom.comp_apply]
  have hgen : ∀ y, s.hom y ∈ genericPoints J₁.subscheme ↔ y ∈ genericPoints J₂.subscheme :=
    fun y => a3b2_homeomorph_mem_genericPoints (Scheme.homeoOfIso s) y
  by_cases hw : ∃ y ∈ genericPoints J₂.subscheme, J₂.subschemeι y = w
  · obtain ⟨y, hy, rfl⟩ := hw
    rw [← hpt, a3b2_idealCycle_apply J₁ hc₁ hl₁ ⟨s.hom y, (hgen y).2 hy⟩,
      a3b2_idealCycle_apply J₂ hc₂ hl₂ ⟨y, hy⟩]
    congr 1
    apply Nat.cast_injective (R := ℕ∞)
    rw [a3b2_genericLength, a3b2_genericLength, ENat.natCast_lift, ENat.natCast_lift]
    exact a3b2_length_eq_of_ringEquiv (asIso (s.hom.stalkMap y)).commRingCatIsoToRingEquiv
  · push_neg at hw
    rw [a3b2_idealCycle_apply_eq_zero J₂ hc₂ hl₂ w hw]
    refine a3b2_idealCycle_apply_eq_zero J₁ hc₁ hl₁ _ fun y hy h => ?_
    have h1 : s.hom (s.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [← h1, hpt] at h
    rw [← h1, hgen] at hy
    exact hw _ hy (hφ h)

/-- For a closed immersion `g : Z ⟶ Y`, the fundamental cycle of `ker g` at `g z` is the
fundamental cycle of `Z` at `z`, and it vanishes off the image of `g`.
Source: Fulton, *Intersection Theory*, second edition, §1.5; Mathlib,
`AlgebraicGeometry.Scheme.Hom.toImage`. -/
theorem a3b2_idealCycle_ker {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsClosedImmersion g]
    (J : Y.IdealSheafData) (hJ : J = g.ker)
    (hc : (irreducibleComponents J.subscheme).Finite)
    (hl : ∀ y ∈ genericPoints J.subscheme,
      Module.length (J.subscheme.presheaf.stalk y) (J.subscheme.presheaf.stalk y) ≠ ⊤)
    (hc' : (irreducibleComponents (⊥ : Z.IdealSheafData).subscheme).Finite)
    (hl' : ∀ y ∈ genericPoints (⊥ : Z.IdealSheafData).subscheme,
      Module.length ((⊥ : Z.IdealSheafData).subscheme.presheaf.stalk y)
        ((⊥ : Z.IdealSheafData).subscheme.presheaf.stalk y) ≠ ⊤) :
    (∀ z : Z, a3b2_idealCycle J hc hl (g z) = a3b2_idealCycle ⊥ hc' hl' z) ∧
      ∀ y : Y, y ∉ Set.range g → a3b2_idealCycle J hc hl y = 0 := by
  subst hJ
  refine ⟨fun z => ?_, fun y hy => ?_⟩
  · refine a3b2_idealCycle_transfer _ _ g g.isClosedEmbedding.injective
      (asIso (⊥ : Z.IdealSheafData).subschemeι ≪≫ asIso g.toImage) ?_ _ _ _ _ z
    simp only [Iso.trans_hom, asIso_hom, Category.assoc]
    exact congrArg _ g.toImage_imageι
  · refine a3b2_idealCycle_apply_eq_zero _ hc hl y fun y' _ h => hy ⟨inv g.toImage y', ?_⟩
    have e : inv g.toImage ≫ g = g.ker.subschemeι := by
      rw [← cancel_epi g.toImage, IsIso.hom_inv_id_assoc, Scheme.Hom.toImage_imageι]
    rw [← h, ← Scheme.Hom.comp_apply, e]

end HodgeLean.Adapters
