import HodgeLean.Adapters.IntersectionProductPrincipalLocal
import HodgeLean.Adapters.IntersectionProductStalk
import HodgeLean.Adapters.IntersectionProductCMStalk
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-! # `Tor` under flat base change and localization

For a flat ring map `f : A → B` and `A`-modules `M`, `N`,
`Tor_i^B(B ⊗ M, B ⊗ N) ≅ B ⊗ Tor_i^A(M, N)` (`a3q_tor_baseChange`): extension of scalars is
exact, monoidal, and sends projective modules to projective modules, so it carries a projective
resolution `Q` of `N` to one of `B ⊗ N`, and `(B ⊗ M) ⊗_B (B ⊗ Q) ≅ B ⊗ (M ⊗ Q)`.

For a point `Z` of a scheme `X` specializing to `T`, the map `𝒪_{X,T} → 𝒪_{X,Z}` is the
localization at the prime `𝔭_Z = a3i_stalkIdeal X T Z` (`a3q_isLocalization_stalkSpecializes`)
and carries `a3i_stalkIdeal X T u` to `a3i_stalkIdeal X Z u` for `u ⤳ Z` (`a3q_map_stalkIdeal`).
So the lengths in `a3i_serreMult X Z u v` are the localized lengths `a3e_locLen 𝔭_Z` of the `Tor`
modules over `𝒪_{X,T}` (`a3q_length_torModule`), which is the form of the inner sums of
`a3e_principal_local`.

Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9; Matsumura,
*Commutative Ring Theory*, Theorem 7.11; Hartshorne, *Algebraic Geometry*, II, Proposition 2.2.

HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters
universe u

section baseChange
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

instance a3q_extendScalars_preservesFiniteColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) := by
  have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

instance a3q_extendScalars_preservesProjectiveObjects :
    (ModuleCat.extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj f)

instance a3q_extendScalars_additive : (ModuleCat.extendScalars.{u, u, u} f).Additive := by
  have : (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (ModuleCat.extendScalars.{u, u, u} f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Extension of scalars along a flat map preserves homology. -/
theorem a3q_extendScalars_preservesHomology (hf : f.Flat) :
    (ModuleCat.extendScalars.{u, u, u} f).PreservesHomology := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  infer_instance

/-- `(B ⊗ M) ⊗_B (B ⊗ K) ≅ B ⊗ (M ⊗ K)` for a complex `K`, from the monoidal structure of
extension of scalars. -/
def a3q_tensCIso (M : ModuleCat.{u} A) (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    a3c_tensC ((ModuleCat.extendScalars.{u, u, u} f).obj M)
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).obj K) ≅
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).obj (a3c_tensC M K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => Functor.Monoidal.μIso (ModuleCat.extendScalars.{u, u, u} f) M (K.X i))
    (fun i j _ => (Functor.LaxMonoidal.μ_natural_right _ _ _).symm)

/-- Flat base change of `Tor`: `Tor_n^B(B ⊗ M, B ⊗ N) ≅ B ⊗ Tor_n^A(M, N)` for a flat ring map
`A → B`.
Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9 (flat base change
for `Tor`); Matsumura, *Commutative Ring Theory*, Theorem 7.11. -/
theorem a3q_tor_baseChange (hf : f.Flat) (M N : ModuleCat.{u} A) (n : ℕ) :
    Nonempty (((Tor (ModuleCat.{u} B) n).obj ((ModuleCat.extendScalars.{u, u, u} f).obj M)).obj
      ((ModuleCat.extendScalars.{u, u, u} f).obj N) ≅
      (ModuleCat.extendScalars.{u, u, u} f).obj (((Tor (ModuleCat.{u} A) n).obj M).obj N)) := by
  have := a3q_extendScalars_preservesHomology f hf
  let F := ModuleCat.extendScalars.{u, u, u} f
  let Q := ProjectiveResolution.of N
  let Q' := F.mapProjectiveResolution Q
  exact ⟨a3c_torIso _ _ Q' n ≪≫
    HomologicalComplex.homologyMapIso
      (show a3c_tensC (F.obj M) Q'.complex ≅ _ from a3q_tensCIso f M Q.complex) n ≪≫
    ((a3c_tensC M Q.complex).sc n).mapHomologyIso F ≪≫ F.mapIso (a3c_torIso M N Q n).symm⟩

end baseChange

section length

/-- The length of a localization at a prime, computed in any model `B` of `A_𝔭` and any
localized module `X` of `T`. -/
theorem a3q_locLen_eq_length {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝔭 : PrimeSpectrum A) [IsLocalization.AtPrime B 𝔭.asIdeal] (T X : Type u) [AddCommGroup T]
    [Module A T] [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    (g : T →ₗ[A] X) [IsLocalizedModule 𝔭.asIdeal.primeCompl g] :
    a3e_locLen 𝔭 T = Module.length B X := by
  let L := Localization.AtPrime 𝔭.asIdeal
  let e : L ≃ₐ[A] B := IsLocalization.algEquiv 𝔭.asIdeal.primeCompl L B
  letI : Algebra L B := e.toRingHom.toAlgebra
  letI : Module L X := Module.compHom X (algebraMap L B)
  haveI : IsScalarTower L B X := ⟨fun l b x => mul_smul (algebraMap L B l) b x⟩
  haveI : IsScalarTower A L X := ⟨fun a l x => by
    change (algebraMap L B (a • l)) • x = a • ((algebraMap L B l) • x)
    have : algebraMap L B (a • l) = a • algebraMap L B l := map_smul e a l
    rw [this, smul_assoc]⟩
  let e1 : LocalizedModule 𝔭.asIdeal.primeCompl T ≃ₗ[A] X := IsLocalizedModule.iso _ g
  let e2 := e1.extendScalarsOfIsLocalization 𝔭.asIdeal.primeCompl L
  rw [a3e_locLen, e2.length_eq]
  exact Module.length_eq_of_surjective e.surjective

end length

section stalk
open AlgebraicGeometry

/-- For `u ⤳ z`, the ideal of `closure {u}` in `𝒪_{X,z}` is prime. -/
theorem a3q_stalkIdeal_isPrime (X : Scheme.{u}) {z u : X} (h : u ⤳ z) :
    (a3i_stalkIdeal X z u).IsPrime := by
  obtain ⟨p, -, hp⟩ := a3c_stalkIdeal_spec X z u h
  rw [hp]
  exact p.isPrime

/-- On an affine open `U ∋ u`, the sections of the ideal of `closure {u}` are the prime of `u`. -/
theorem a3q_ideal_primeIdeal {X : Scheme.{u}} (u : X) (U : X.affineOpens) (hu : u ∈ U.1) :
    (ccm3_primeIdeal X u).ideal U = (U.2.primeIdealOf ⟨u, hu⟩).asIdeal := by
  set pu := U.2.primeIdealOf ⟨u, hu⟩
  have hpu : U.2.fromSpec pu = u := U.2.fromSpec_primeIdealOf ⟨u, hu⟩
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

/-- For `Z ⤳ T`, the specialization map `𝒪_{X,T} → 𝒪_{X,Z}` is the localization at the prime of
`closure {Z}`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.2 and Exercise 3.11 (stalks of an
affine scheme are localizations); Atiyah–Macdonald, Corollary 3.13 (a localization of a
localization). -/
theorem a3q_isLocalization_stalkSpecializes (X : Scheme.{u}) {T Z : X} (h : Z ⤳ T) :
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    haveI := a3q_stalkIdeal_isPrime X h
    IsLocalization.AtPrime (X.presheaf.stalk Z) (a3i_stalkIdeal X T Z) := by
  letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  haveI := a3q_stalkIdeal_isPrime X h
  obtain ⟨_, ⟨U, hU, rfl⟩, hTU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ T) isOpen_univ
  have hZU : Z ∈ U := h.mem_open U.isOpen hTU
  letI aT : Algebra Γ(X, U) (X.presheaf.stalk T) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨T, hTU⟩
  letI aZ : Algebra Γ(X, U) (X.presheaf.stalk Z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨Z, hZU⟩
  haveI hT := hU.isLocalization_stalk ⟨T, hTU⟩
  haveI hZ := hU.isLocalization_stalk ⟨Z, hZU⟩
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk T) (X.presheaf.stalk Z) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hTU h r).symm
  set pT := (hU.primeIdealOf ⟨T, hTU⟩).asIdeal
  set pZ := (hU.primeIdealOf ⟨Z, hZU⟩).asIdeal
  have hle : pZ ≤ pT := by
    have hs : hU.primeIdealOf ⟨Z, hZU⟩ ⤳ hU.primeIdealOf ⟨T, hTU⟩ := by
      rw [← hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff, hU.fromSpec_primeIdealOf,
        hU.fromSpec_primeIdealOf]
      exact h
    exact (PrimeSpectrum.le_iff_specializes _ _).2 hs
  have hmap : a3i_stalkIdeal X T Z = pZ.map (algebraMap Γ(X, U) (X.presheaf.stalk T)) := by
    rw [← a3l_map_primeIdeal_eq_stalkIdeal h ⟨U, hU⟩ hTU, a3q_ideal_primeIdeal Z ⟨U, hU⟩ hZU]
    rfl
  have hcomap : (a3i_stalkIdeal X T Z).comap (algebraMap Γ(X, U) (X.presheaf.stalk T)) = pZ := by
    rw [hmap]
    exact IsLocalization.under_map_of_isPrime_disjoint pT.primeCompl _
      (hU.primeIdealOf ⟨Z, hZU⟩).isPrime
      (by rw [Set.disjoint_left]; exact fun x hx hx' => hx (hle hx'))
  haveI := IsLocalization.isLocalization_of_submonoid_le (S := X.presheaf.stalk T)
    (T := X.presheaf.stalk Z) pT.primeCompl pZ.primeCompl (fun x hx h' => hx (hle h'))
  refine IsLocalization.isLocalization_of_is_exists_mul_mem (X.presheaf.stalk Z)
    (pZ.primeCompl.map (algebraMap Γ(X, U) (X.presheaf.stalk T))) _ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩ h'
    exact hr (by rw [← hcomap]; exact h')
  · rintro ⟨x, hx⟩
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective pT.primeCompl x
    dsimp only at hx ⊢
    refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk T) s, ⟨r, fun hr => hx ?_, ?_⟩⟩
    · rw [hmap, IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr)
    · simp only [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm (s : Γ(X, U)) r,
        IsLocalization.mk'_mul_cancel_right]

/-- `𝔭_u 𝒪_{X,Z}` is the ideal of `closure {u}` in `𝒪_{X,Z}`, for `u ⤳ Z ⤳ T`. -/
theorem a3q_map_stalkIdeal (X : Scheme.{u}) {T Z u : X} (h : Z ⤳ T) (hu : u ⤳ Z) :
    (a3i_stalkIdeal X T u).map (X.presheaf.stalkSpecializes h).hom = a3i_stalkIdeal X Z u := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hTU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ T) isOpen_univ
  have hZU : Z ∈ U := h.mem_open U.isOpen hTU
  rw [← a3l_map_primeIdeal_eq_stalkIdeal (hu.trans h) ⟨U, hU⟩ hTU,
    ← a3l_map_primeIdeal_eq_stalkIdeal hu ⟨U, hU⟩ hZU, Ideal.map_map]
  congr 1
  ext r
  exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hTU h r

/-- The lengths in Serre's multiplicity along `Z` are lengths of localized `Tor` modules at any
specialization `T` of `Z`: `ℓ Tor_i^{𝒪_{X,Z}}(𝒪_{X,Z}/𝔭_u, 𝒪_{X,Z}/𝔭_v) =
ℓ (Tor_i^{𝒪_{X,T}}(𝒪_{X,T}/𝔭_u, 𝒪_{X,T}/𝔭_v))_{𝔭_Z}`.
Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9 (flat base change
for `Tor`); Hartshorne, *Algebraic Geometry*, II, Proposition 2.2 (stalks as localizations). -/
theorem a3q_length_torModule (X : Scheme.{u}) {T Z u v : X} (h : Z ⤳ T) (hu : u ⤳ Z)
    (hv : v ⤳ Z) (i : ℕ) :
    Module.length (X.presheaf.stalk Z) (a3i_torModule X Z u v i) =
      a3e_locLen ⟨a3i_stalkIdeal X T Z, a3q_stalkIdeal_isPrime X h⟩
        (((Tor (ModuleCat.{u} (X.presheaf.stalk T)) i).obj
          (ModuleCat.of _ (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T u))).obj
          (ModuleCat.of _ (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T v))) := by
  set f := (X.presheaf.stalkSpecializes h).hom
  letI := f.toAlgebra
  haveI := a3q_stalkIdeal_isPrime X h
  haveI := a3q_isLocalization_stalkSpecializes X h
  have hf : f.Flat := IsLocalization.flat (X.presheaf.stalk Z) (a3i_stalkIdeal X T Z).primeCompl
  let F := ModuleCat.extendScalars.{u, u, u} f
  have hq : ∀ w : X, w ⤳ Z → Nonempty
      (F.obj (ModuleCat.of _ (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T w)) ≅
        ModuleCat.of _ (X.presheaf.stalk Z ⧸ a3i_stalkIdeal X Z w)) := by
    intro w hw
    rw [← a3q_map_stalkIdeal X h hw]
    exact ⟨(Algebra.TensorProduct.quotIdealMapEquivTensorQuot (X.presheaf.stalk Z)
      (a3i_stalkIdeal X T w)).toLinearEquiv.toModuleIso.symm⟩
  obtain ⟨eu⟩ := hq u hu
  obtain ⟨ev⟩ := hq v hv
  obtain ⟨eb⟩ := a3q_tor_baseChange f hf
    (ModuleCat.of _ (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T u))
    (ModuleCat.of _ (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T v)) i
  let e : a3i_torModule X Z u v i ≅ _ :=
    (((Tor _ i).mapIso eu).app _ ≪≫ ((Tor _ i).obj _).mapIso ev).symm ≪≫ eb
  rw [e.toLinearEquiv.length_eq]
  symm
  change _ = Module.length (X.presheaf.stalk Z) (TensorProduct (X.presheaf.stalk T)
    (X.presheaf.stalk Z) (((Tor (ModuleCat.{u} (X.presheaf.stalk T)) i).obj
      (ModuleCat.of _ (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T u))).obj
      (ModuleCat.of _ (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T v))))
  exact a3q_locLen_eq_length ⟨_, _⟩ _ _ (TensorProduct.mk _ (X.presheaf.stalk Z) _ 1)

end stalk

end HodgeLean.Adapters
