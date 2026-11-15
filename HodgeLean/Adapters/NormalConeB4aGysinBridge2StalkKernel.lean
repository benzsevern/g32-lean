import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Reformulated bridge of A3-B4a: stalk maps of open embeddings kill only nilpotents

For a morphism of schemes whose underlying map is an open embedding, every element of a stalk of
the target that maps to zero in the stalk of the source is nilpotent: the corresponding section
vanishes at every point of an open neighbourhood. Source: Hartshorne, *Algebraic Geometry*,
Exercise II.2.3 and Proposition II.2.2. -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- Elements of a stalk killed by the stalk map of a morphism that is an open embedding on
underlying spaces are nilpotent. Source: Hartshorne, *Algebraic Geometry*, Exercise II.2.3. -/
theorem a3b4g_isNilpotent_of_stalkMap_eq_zero {A K : Scheme} (ψ : A ⟶ K)
    (hψ : Topology.IsOpenEmbedding ψ.base) (x : A) (f : K.presheaf.stalk (ψ.base x))
    (hf : ψ.stalkMap x f = 0) : IsNilpotent f := by
  obtain ⟨W, hW, s, rfl⟩ := K.presheaf.exists_germ_eq f
  rw [Scheme.Hom.germ_stalkMap_apply] at hf
  obtain ⟨N, hxN, iN, iN', hN⟩ := TopCat.Presheaf.germ_eq A.presheaf x (show x ∈ ψ ⁻¹ᵁ W from hW)
    (show x ∈ ψ ⁻¹ᵁ W from hW) (ψ.app W s) 0
    (by rw [hf, map_zero])
  rw [map_zero] at hN
  have hkey : ∀ z ∈ ψ.base '' (N : Set A), ∀ hz : z ∈ W,
      ¬ IsUnit (K.presheaf.germ W z hz s) := by
    rintro z ⟨p, hpN, rfl⟩ hz hu
    have hu' := hu.map (ψ.stalkMap p).hom
    rw [Scheme.Hom.germ_stalkMap_apply] at hu'
    have h0 : A.presheaf.germ (ψ ⁻¹ᵁ W) p hz (ψ.app W s) = 0 := by
      rw [← TopCat.Presheaf.germ_res_apply A.presheaf iN p hpN, hN, map_zero]
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  let O : K.Opens := ⟨ψ.base '' (N : Set A), hψ.isOpenMap _ N.2⟩
  have hxO : ψ.base x ∈ O ⊓ W := ⟨⟨x, hxN, rfl⟩, hW⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    K.isBasis_affineOpens.exists_subset_of_mem_open hxO (O ⊓ W).2
  have hVW : V ≤ W := fun z hz => (hVle hz).2
  let t : Γ(K, V) := K.presheaf.map (homOfLE hVW).op s
  have hnil : IsNilpotent t := by
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    let y : PrimeSpectrum Γ(K, V) := ⟨P, hP⟩
    have hyV : hV.fromSpec y ∈ V := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]
      exact ⟨y, rfl⟩
    by_contra hPt
    have hyb : y ∈ (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum Γ(K, V))) := hPt
    rw [← hV.fromSpec_preimage_basicOpen] at hyb
    have hunit : IsUnit (K.presheaf.germ V (hV.fromSpec y) hyV t) :=
      (Scheme.mem_basicOpen K t (hV.fromSpec y) hyV).mp hyb
    rw [TopCat.Presheaf.germ_res_apply] at hunit
    exact hkey _ (hVle hyV).1 _ hunit
  have hf : K.presheaf.germ W (ψ.base x) hW s = K.presheaf.germ V (ψ.base x) hxV t := by
    rw [TopCat.Presheaf.germ_res_apply]
  rw [hf]
  exact hnil.map _

end HodgeLean.Adapters
