import HodgeLean.Adapters.IntersectionProductDefs

/-! # Stalks of closed subschemes and the `Tor_0` length

For an ideal sheaf `I` on a scheme `X` and a point `y` of `I.subscheme` over `z ∈ X`, the stalk map
`𝒪_{X,z} → 𝒪_{I.subscheme,y}` is surjective with kernel the localization of `I(U)` for any affine
open `U ∋ z`. For the reduced subscheme `closure {u}` with `u ⤳ z` that localization is the prime
`a3i_stalkIdeal X z u`. Together with `A/𝔭 ⊗ A/𝔮 ≅ A/(𝔭 + 𝔮)` this computes the length of
`Tor_0` as the length of the local ring of the scheme-theoretic intersection.

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.2 and Exercise 3.11 (closed
subschemes of affine schemes and their local rings); Atiyah–Macdonald, Proposition 3.11
(extension of ideals to a localization). HC no distance; AV milestone no distance.
-/

open CategoryTheory AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HodgeLean.Adapters
universe u

/-- The kernel of the stalk map of a closed subscheme is the localized ideal. -/
theorem a3l_ker_stalkMap_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) (y : I.subscheme)
    (U : X.affineOpens) (hy : I.subschemeι y ∈ U.1) :
    RingHom.ker (I.subschemeι.stalkMap y).hom =
      Ideal.map (X.presheaf.germ U.1 _ hy).hom (I.ideal U) := by
  set f := I.subschemeι
  have hV : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨f y, hy⟩ : U.1)
  have hA := U.2.isLocalization_stalk ⟨f y, hy⟩
  let _ := TopCat.Presheaf.algebra_section_stalk I.subscheme.presheaf (⟨y, hy⟩ : f ⁻¹ᵁ U.1)
  have hS := hV.isLocalization_stalk ⟨y, hy⟩
  set 𝔓 := (U.2.primeIdealOf ⟨f y, hy⟩).asIdeal
  set 𝔔 := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  have sq : ∀ b, f.stalkMap y (X.presheaf.germ U.1 _ hy b) =
      I.subscheme.presheaf.germ (f ⁻¹ᵁ U.1) y hy (f.app U.1 b) := fun b =>
    Scheme.Hom.germ_stalkMap_apply f U.1 y hy b
  have hgX : ∀ b, X.presheaf.germ U.1 _ hy b = algebraMap Γ(X, U.1) (X.presheaf.stalk (f y)) b :=
    fun _ => rfl
  have hgY : ∀ c, I.subscheme.presheaf.germ (f ⁻¹ᵁ U.1) y hy c =
      algebraMap Γ(I.subscheme, f ⁻¹ᵁ U.1) (I.subscheme.presheaf.stalk y) c := fun _ => rfl
  have hPQ : ∀ t, f.app U.1 t ∉ 𝔔 → t ∉ 𝔓 := by
    intro t ht h𝔓
    have h1 : IsUnit (algebraMap Γ(I.subscheme, f ⁻¹ᵁ U.1) (I.subscheme.presheaf.stalk y)
        (f.app U.1 t)) := (IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔔 _).2 ht
    rw [← hgY, ← sq] at h1
    have h2 := (isUnit_map_iff (f.stalkMap y).hom _).1 h1
    rw [hgX] at h2
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔓 _).1 h2) h𝔓
  apply le_antisymm
  · intro a ha
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl a
    dsimp only at ha ⊢
    have hb : f.stalkMap y (algebraMap Γ(X, U.1) (X.presheaf.stalk (f y)) b) = 0 := by
      rw [← IsLocalization.mk'_spec (X.presheaf.stalk (f y)) b s, map_mul]
      rw [RingHom.mem_ker] at ha
      erw [ha, zero_mul]
    rw [← hgX, sq, hgY, IsLocalization.map_eq_zero_iff 𝔔.primeCompl] at hb
    obtain ⟨⟨c, hc⟩, hcb⟩ := hb
    obtain ⟨t, rfl⟩ := I.subschemeι_app_surjective U c
    have htb : t * b ∈ I.ideal U := by
      rw [← I.ker_subschemeι_app U, RingHom.mem_ker, map_mul]; exact hcb
    have ht : t ∈ 𝔓.primeCompl := hPQ t hc
    have h1 : algebraMap Γ(X, U.1) (X.presheaf.stalk (f y)) (t * b) ∈
        Ideal.map (X.presheaf.germ U.1 _ hy).hom (I.ideal U) := Ideal.mem_map_of_mem _ htb
    rw [map_mul] at h1
    have h2 : algebraMap Γ(X, U.1) (X.presheaf.stalk (f y)) b ∈
        Ideal.map (X.presheaf.germ U.1 _ hy).hom (I.ideal U) :=
      (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units _ ⟨t, ht⟩)).1 h1
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h2
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    erw [sq]
    rw [← I.ker_subschemeι_app U, RingHom.mem_ker] at hb
    erw [hb, map_zero]


/-- On an affine open `U ∋ z`, the localized ideal of the reduced subscheme `closure {u}` is the
prime `a3i_stalkIdeal X z u` of `𝒪_{X,z}`. -/
theorem a3l_map_primeIdeal_eq_stalkIdeal {X : Scheme.{u}} {z u : X} (h : u ⤳ z)
    (U : X.affineOpens) (hz : z ∈ U.1) :
    Ideal.map (X.presheaf.germ U.1 z hz).hom ((ccm3_primeIdeal X u).ideal U) =
      a3i_stalkIdeal X z u := by
  classical
  have hu : u ∈ U.1 := h.mem_open U.1.isOpen hz
  set pu := U.2.primeIdealOf ⟨u, hu⟩
  have hpu : U.2.fromSpec pu = u := U.2.fromSpec_primeIdealOf ⟨u, hu⟩
  have hideal : (ccm3_primeIdeal X u).ideal U = pu.asIdeal := by
    rw [ccm3_primeIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have : U.2.fromSpec ⁻¹' closure ({u} : Set X) = closure {pu} := by
      rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
        U.2.fromSpec.continuous]
      congr 1
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [← hpu]
      exact U.2.fromSpec.isOpenEmbedding.injective.eq_iff
    change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' closure ({u} : Set X)) = _
    rw [this, PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]
  have hex : ∃ p : Spec (X.presheaf.stalk z), X.fromSpecStalk z p = u := by
    have : u ∈ Set.range (X.fromSpecStalk z) := by
      rw [Scheme.range_fromSpecStalk]; exact h
    exact this
  rw [a3i_stalkIdeal]
  split
  swap
  · exact absurd hex ‹_›
  rename_i hex'
  set p : PrimeSpectrum (X.presheaf.stalk z) := Classical.choose hex'
  have hp : X.fromSpecStalk z p = u := Classical.choose_spec hex'
  rw [← U.2.fromSpecStalk_eq_fromSpecStalk hz, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.comp_apply, Spec.map_apply, ← hpu] at hp
  have hcomap := U.2.fromSpec.isOpenEmbedding.injective hp
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : U.1)
  have hA := U.2.isLocalization_stalk ⟨z, hz⟩
  rw [hideal, ← hcomap]
  exact IsLocalization.map_under (U.2.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl _ p.asIdeal

/-- `length (A/𝔭 ⊗ A/𝔮) = length A/(𝔭 + 𝔮)`. -/
theorem a3l_length_tensor_quot {A : Type u} [CommRing A] (p q : Ideal A) :
    Module.length A ((A ⧸ p) ⊗[A] (A ⧸ q)) = Module.length A (A ⧸ (p ⊔ q)) := by
  let e₁ := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ p) q).restrictScalars A
  let e₂ := DoubleQuot.quotQuotEquivQuotSupₐ A p q
  exact (e₁.symm.toLinearEquiv.trans e₂.toLinearEquiv).length_eq

/-- A surjection `A → S` with kernel `I` identifies `length_A A/I` with `length_S S`. -/
theorem a3l_length_quot_ker {A S : Type u} [CommRing A] [CommRing S] (φ : A →+* S)
    (hφ : Function.Surjective φ) (I : Ideal A) (hI : RingHom.ker φ = I) :
    Module.length A (A ⧸ I) = Module.length S S := by
  let := φ.toAlgebra
  have e := (Ideal.quotientEquivAlgOfEq A hI.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A S) hφ)
  rw [e.toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective hφ

/-- A point of the scheme-theoretic intersection of `closure {u}` and `closure {v}` is a
specialization of both `u` and `v`. -/
theorem a3l_specializes_of_subscheme {X : Scheme.{u}} (u v : X)
    (y : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) :
    u ⤳ (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι y ∧
      v ⤳ (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι y := by
  have hz : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι y ∈
      ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩
  simp only [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
    ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_mk, Set.mem_inter_iff] at hz
  exact ⟨specializes_iff_mem_closure.2 hz.1, specializes_iff_mem_closure.2 hz.2⟩

end HodgeLean.Adapters
