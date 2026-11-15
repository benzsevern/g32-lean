import HodgeLean.Adapters.IntersectionProductCMQuotient
import HodgeLean.Adapters.KleimanCoheightAlgebra
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import HodgeConjecture.Mathlib.RingTheory.SmoothKrullDimension
import HodgeConjecture.Lemmas.RingTheory.TranscendenceDegreeKrullDimension
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Local rings of a smooth complex variety

For a smooth integral scheme `X` over `ℂ` and points `u ⤳ z`:
* the stalk `𝒪_{X,z}` is a regular local ring (`a3c_isRegularLocalRing_stalk`): locally `X` is
  étale over an affine space, and a local étale map out of a regular local ring has regular local
  target;
* every prime `𝔮` of `𝒪_{X,z}` satisfies `ht 𝔮 + dim 𝒪_{X,z}/𝔮 = dim 𝒪_{X,z}`
  (`a3c_height_add_ringKrullDim_quotient_stalk`), from the dimension formula for finitely
  generated domains over a field on an affine chart;
* the ideal `a3i_stalkIdeal X z u` is the prime of `𝒪_{X,z}` over `u`, its height is the coheight
  of `u`, and `codim u + dim 𝒪_{X,z}/𝔭_u = codim z` (`a3c_coheight_add_ringKrullDim_stalkIdeal`).

Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6 and §14 (regular local rings);
EGA IV, 17.5.1 and 6.5 (smooth morphisms have regular local rings); Hartshorne,
*Algebraic Geometry*, Exercise II.3.20. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing

namespace HodgeLean.Adapters

/-! ## Regular stalks -/

/-- An essentially finite-type, formally unramified, flat and quasi-finite local map out of a
regular local ring has regular local target.
Source: EGA IV, 17.5.1; Matsumura, *Commutative Ring Theory*, §14. -/
theorem a3c_isRegularLocalRing_of_formallyUnramified {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsRegularLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] [Algebra.QuasiFinite R S] :
    IsRegularLocalRing S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)]
  have hspan :
      (↑(Submodule.spanFinrank ((maximalIdeal R).map (algebraMap R S))) : WithBot ℕ∞) ≤
        (↑(Submodule.spanFinrank (maximalIdeal R)) : WithBot ℕ∞) := by
    exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
      (maximalIdeal R).fg_of_isNoetherianRing
  refine hspan.trans_eq ?_
  rw [(isRegularLocalRing_iff R).mp inferInstance]
  have hheight := Algebra.QuasiFinite.height_eq_height_under (R := R) (S := S) (maximalIdeal S)
  rw [show (maximalIdeal S).under R = maximalIdeal R from
    IsLocalRing.maximalIdeal_comap (algebraMap R S)] at hheight
  calc
    ringKrullDim R = (↑(maximalIdeal R).height : WithBot ℕ∞) :=
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ = (↑(maximalIdeal S).height : WithBot ℕ∞) := by rw [hheight]
    _ = ringKrullDim S := IsLocalRing.maximalIdeal_height_eq_ringKrullDim

/-- Every localization at a prime of an étale algebra over a regular ring is regular local.
Source: EGA IV, 17.5.1. -/
theorem a3c_isRegularLocalRing_atPrime_of_etale {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsRegularRing R] [Algebra.Etale R S] (P : Ideal S) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) := by
  let q : Ideal R := P.under R
  let : q.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  let : P.LiesOver q := ⟨rfl⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver q P
  have _ : Algebra.FormallyEtale R (Localization.AtPrime P) := inferInstance
  have _ : Algebra.FormallyEtale (Localization.AtPrime q) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.localization_base q.primeCompl
  have _ : Algebra.EssFiniteType (Localization.AtPrime q) (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_comp R _ _
  have _ : Module.Flat (Localization.AtPrime q) (Localization.AtPrime P) := inferInstance
  have _ : Algebra.QuasiFinite (Localization.AtPrime q) (Localization.AtPrime P) :=
    Algebra.QuasiFinite.of_restrictScalars R _ _
  have _ : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularRing.isRegularLocalRing_localization q
  exact a3c_isRegularLocalRing_of_formallyUnramified
    (R := Localization.AtPrime q) (S := Localization.AtPrime P)

/-- Every stalk of a smooth integral complex scheme is a regular local ring: on an affine chart
the coordinate ring is étale over a polynomial ring.
Source: EGA IV, 17.5.1 and 6.5; Hartshorne, *Algebraic Geometry*, Theorem II.8.8. -/
theorem a3c_isRegularLocalRing_stalk (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (x : X.left) : IsRegularLocalRing (X.left.presheaf.stalk x) := by
  obtain ⟨d, hd⟩ := Smooth.exists_smoothOfRelativeDimension X.hom
  obtain ⟨V, hV, hxV, hf⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := d) X.hom x
  have hstd := (algebraMap_isStandardSmoothOfRelativeDimension X hf).isStandardSmooth
  obtain ⟨n, g, _, hg⟩ := hstd.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, V) := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(X.left, V) := RingHom.etale_algebraMap.mp hg
  let P : Ideal Γ(X.left, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hregular : IsRegularLocalRing (Localization.AtPrime P) :=
    a3c_isRegularLocalRing_atPrime_of_etale (R := MvPolynomial (Fin n) ℂ) P
  let : Algebra Γ(X.left, V) (X.left.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨x, hxV⟩
  let : IsLocalization.AtPrime (X.left.presheaf.stalk x) P := hV.isLocalization_stalk ⟨x, hxV⟩
  exact @IsRegularLocalRing.of_ringEquiv (Localization.AtPrime P) _ hregular
    (X.left.presheaf.stalk x) _
    (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (X.left.presheaf.stalk x)).toRingEquiv


/-! ## The dimension formula in a local ring of a variety -/

section dim

/-- In a local ring, `dim A/𝔮` is the height of the closed point among the primes above `𝔮`. -/
lemma a3c_ringKrullDim_quotient_eq_height {A : Type*} [CommRing A] [IsLocalRing A]
    (𝔮 : Ideal A) [𝔮.IsPrime] :
    ringKrullDim (A ⧸ 𝔮) = Order.height (⟨IsLocalRing.closedPoint A,
      (PrimeSpectrum.mem_zeroLocus _ _).mpr
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))⟩ :
          PrimeSpectrum.zeroLocus (R := A) 𝔮) := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_height]
  refine le_antisymm (iSup_le fun x => ?_)
    (le_iSup (fun x : PrimeSpectrum.zeroLocus (R := A) 𝔮 => (Order.height x : WithBot ℕ∞)) _)
  exact_mod_cast Order.height_mono (show x ≤ _ from
    (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (IsLocalRing.le_maximalIdeal_of_isPrime _))

/-- Heights of primes above `𝔮` in a localization `A = S_𝔐` agree with heights of their
contractions among the primes of `S` above `𝔮 ∩ S`. -/
lemma a3c_height_zeroLocus_comap {S : Type*} [CommRing S] (𝔐 : Ideal S) [𝔐.IsPrime]
    (A : Type*) [CommRing A] [Algebra S A] [IsLocalization.AtPrime A 𝔐] (𝔮 : Ideal A)
    (x : PrimeSpectrum.zeroLocus (R := A) 𝔮) :
    Order.height x = Order.height (⟨PrimeSpectrum.comap (algebraMap S A) x.1,
      (PrimeSpectrum.mem_zeroLocus _ _).mpr (Ideal.comap_mono
        ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩ :
          PrimeSpectrum.zeroLocus (R := S) (𝔮.comap (algebraMap S A))) := by
  have hinj := PrimeSpectrum.localization_comap_injective A 𝔐.primeCompl
  let f : PrimeSpectrum.zeroLocus (R := A) 𝔮 →
      PrimeSpectrum.zeroLocus (R := S) (𝔮.comap (algebraMap S A)) := fun x =>
    ⟨PrimeSpectrum.comap (algebraMap S A) x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (Ideal.comap_mono ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩
  have hmono : ∀ a b : PrimeSpectrum.zeroLocus (R := A) 𝔮, a ≤ b → f a ≤ f b := fun a b h =>
    (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (Ideal.comap_mono
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h))
  have hrefl : ∀ a b : PrimeSpectrum.zeroLocus (R := A) 𝔮, f a ≤ f b → a ≤ b := by
    intro a b h
    have h' : (a.1.asIdeal.comap (algebraMap S A)) ≤ b.1.asIdeal.comap (algebraMap S A) :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h
    have := Ideal.map_mono (f := algebraMap S A) h'
    rw [IsLocalization.map_under 𝔐.primeCompl A, IsLocalization.map_under 𝔐.primeCompl A] at this
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp this
  refine Order.height_eq_of_strictMono f (fun a b hab => ?_) (fun a b hb => ?_) x
  · refine lt_of_le_of_ne (hmono a b hab.le) fun h => hab.ne ?_
    exact Subtype.ext (hinj (congrArg Subtype.val h))
  · have hbm : b.1.asIdeal ≤ 𝔐 := by
      have h1 : b.1.asIdeal ≤ (a.1.asIdeal).comap (algebraMap S A) :=
        (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hb.le
      refine h1.trans ?_
      have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A 𝔐
      rw [← IsLocalization.AtPrime.under_maximalIdeal A 𝔐]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime _)
    have hrange : b.1 ∈ Set.range (PrimeSpectrum.comap (algebraMap S A)) := by
      rw [PrimeSpectrum.localization_comap_range A 𝔐.primeCompl]
      change Disjoint (𝔐.primeCompl : Set S) b.1.asIdeal
      rw [Set.disjoint_left]
      intro r hr hrb
      exact hr (hbm hrb)
    obtain ⟨c, hc⟩ := hrange
    have hcq : c ∈ PrimeSpectrum.zeroLocus (R := A) 𝔮 := by
      rw [PrimeSpectrum.mem_zeroLocus]
      have h1 : 𝔮.comap (algebraMap S A) ≤ c.asIdeal.comap (algebraMap S A) := by
        have := (PrimeSpectrum.mem_zeroLocus _ _).mp b.2
        rw [← hc] at this
        exact this
      have := Ideal.map_mono (f := algebraMap S A) h1
      rw [IsLocalization.map_under 𝔐.primeCompl A, IsLocalization.map_under 𝔐.primeCompl A] at this
      exact this
    have hfc : f ⟨c, hcq⟩ = b := Subtype.ext hc
    refine ⟨⟨c, hcq⟩, ?_, hfc⟩
    refine lt_of_le_of_ne (hrefl _ _ (hfc ▸ hb.le)) fun h => ?_
    rw [h] at hfc
    exact hb.ne hfc.symm

lemma a3c_split_nat {x : ℕ∞} {y : WithBot ℕ∞} {n : ℕ} (h : (x : WithBot ℕ∞) + y = n) :
    ∃ x' y' : ℕ, x = x' ∧ y = y' ∧ x' + y' = n := by
  induction y using WithBot.recBotCoe with
  | bot => simp at h
  | coe c =>
    have h' : x + c = n := by exact_mod_cast h
    induction x using ENat.recTopCoe with
    | top => simp at h'
    | coe x' =>
      induction c using ENat.recTopCoe with
      | top => simp at h'
      | coe c' => exact ⟨x', c', rfl, rfl, by exact_mod_cast h'⟩

/-- The dimension formula `ht 𝔮 + dim A/𝔮 = dim A` in a localization `A = S_𝔐` of a finitely
generated domain `S` over a field.
Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6 and §31 (catenarity of finitely
generated algebras over a field). -/
theorem a3c_height_add_ringKrullDim_quotient_of_isLocalization {k : Type} [Field k] {S : Type}
    [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S] (𝔐 : Ideal S) [𝔐.IsPrime]
    (A : Type) [CommRing A] [Algebra S A] [IsLocalization.AtPrime A 𝔐] (𝔮 : Ideal A)
    [𝔮.IsPrime] :
    (𝔮.height : WithBot ℕ∞) + ringKrullDim (A ⧸ 𝔮) = ringKrullDim A := by
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A 𝔐
  set P := 𝔮.comap (algebraMap S A) with hPdef
  have hm : (maximalIdeal A).comap (algebraMap S A) = 𝔐 :=
    IsLocalization.AtPrime.under_maximalIdeal A 𝔐
  have hP𝔐 : P ≤ 𝔐 :=
    hm ▸ Ideal.comap_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
  have hmp : (𝔐.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  -- `dim A/𝔮 = ht (𝔐/P)`
  have hquot : ringKrullDim (A ⧸ 𝔮) = ((𝔐.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) := by
    rw [a3c_ringKrullDim_quotient_eq_height, a3c_height_zeroLocus_comap 𝔐 A 𝔮,
      PrimeSpectrum.height_eq_orderHeight ⟨_, hmp⟩]
    let e := P.primeSpectrumQuotientOrderIsoZeroLocus
    have he : e ⟨_, hmp⟩ = ⟨PrimeSpectrum.comap (algebraMap S A) (IsLocalRing.closedPoint A),
        (PrimeSpectrum.mem_zeroLocus _ _).mpr (Ideal.comap_mono
          ((PrimeSpectrum.mem_zeroLocus _ _).mp ((PrimeSpectrum.mem_zeroLocus _ _).mpr
            (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)))))⟩ := by
      apply Subtype.ext
      apply PrimeSpectrum.ext
      change (𝔐.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) =
        (maximalIdeal A).comap (algebraMap S A)
      rw [hm, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hP𝔐]
    rw [← he, Order.height_orderIso]
  have : P.IsPrime := Ideal.IsPrime.comap _
  have : IsDomain (S ⧸ P) := (Ideal.Quotient.isDomain_iff_prime P).mpr inferInstance
  have : Algebra.FiniteType k (S ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) (Ideal.Quotient.mkₐ_surjective k P)
  obtain ⟨n, hn, -⟩ := Algebra.FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := k) (A := S)
  have h1 := hc9k8_height_add_ringKrullDim_quotient (k := k) P
  have h2 := hc9k8_height_add_ringKrullDim_quotient (k := k) 𝔐
  have h3 := hc9k8_height_add_ringKrullDim_quotient (k := k) (S := S ⧸ P)
    (𝔐.map (Ideal.Quotient.mk P))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hP𝔐)] at h3
  rw [hn] at h1 h2
  obtain ⟨p, a, hp, ha, hpa⟩ := a3c_split_nat h1
  obtain ⟨m, b, hm', hb, hmb⟩ := a3c_split_nat h2
  rw [ha] at h3
  obtain ⟨t, b', ht, hb', htb⟩ := a3c_split_nat h3
  rw [hb] at hb'
  have hbb : b = b' := by exact_mod_cast hb'
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔐 A, hquot,
    ← IsLocalization.height_under 𝔐.primeCompl 𝔮, hp, ht, hm']
  norm_cast
  omega

/-- The dimension formula `ht 𝔮 + dim 𝒪_{X,z}/𝔮 = dim 𝒪_{X,z}` for every prime `𝔮` of a local
ring of an integral scheme locally of finite type over `ℂ`.
Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6; Hartshorne, *Algebraic Geometry*,
Exercise II.3.20. -/
theorem a3c_height_add_ringKrullDim_quotient_stalk (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (z : X.left) (𝔮 : Ideal (X.left.presheaf.stalk z))
    [𝔮.IsPrime] :
    (𝔮.height : WithBot ℕ∞) + ringKrullDim (X.left.presheaf.stalk z ⧸ 𝔮) =
      ringKrullDim (X.left.presheaf.stalk z) := by
  obtain ⟨_, ⟨V, hV', rfl⟩, hzV, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hV : IsAffineOpen V := hV'
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ X.hom)
  let : Algebra ℂ Γ(X.left, V) := φ.hom.toAlgebra
  have : Algebra.FiniteType ℂ Γ(X.left, V) := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  let : Algebra Γ(X.left, V) (X.left.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf ⟨z, hzV⟩
  have : IsLocalization.AtPrime (X.left.presheaf.stalk z) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨z, hzV⟩
  exact a3c_height_add_ringKrullDim_quotient_of_isLocalization (k := ℂ)
    (hV.primeIdealOf ⟨z, hzV⟩).asIdeal _ 𝔮

end dim

/-! ## The prime of a generization in a local ring -/

/-- `fromSpecStalk` preserves coheights: its image is the set of generizations of `z`. -/
lemma a3c_coheight_fromSpecStalk {X : Scheme} (z : X) (p : Spec (X.presheaf.stalk z)) :
    Order.coheight p = Order.coheight (X.fromSpecStalk z p) := by
  let f := X.fromSpecStalk z
  have hle : ∀ a b : Spec (X.presheaf.stalk z), f a ≤ f b ↔ a ≤ b := fun a b => by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact f.isEmbedding.isInducing.specializes_iff
  have hlt : ∀ a b : Spec (X.presheaf.stalk z), f a < f b ↔ a < b := fun a b => by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle, hle]
  refine Order.coheight_eq_of_strictMono (fun a => f a) (fun a b hab => (hlt a b).mpr hab)
    (fun a b hb => ?_) p
  have hspec : b ⤳ f a := Scheme.le_iff_specializes.mp hb.le
  have hz : f a ⤳ z := by
    have : f a ∈ Set.range f := ⟨a, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  obtain ⟨a', ha'⟩ : b ∈ Set.range f := by
    rw [Scheme.range_fromSpecStalk]
    exact hspec.trans hz
  exact ⟨a', (hlt a a').mp (ha' ▸ hb), ha'⟩

/-- For `u ⤳ z`, the ideal `a3i_stalkIdeal X z u` is the prime of a point of `Spec 𝒪_{X,z}`
over `u`. -/
lemma a3c_stalkIdeal_spec (X : Scheme) (z u : X) (h : u ⤳ z) :
    ∃ p : Spec (X.presheaf.stalk z), X.fromSpecStalk z p = u ∧
      a3i_stalkIdeal X z u = p.asIdeal := by
  have hex : ∃ p : Spec (X.presheaf.stalk z), X.fromSpecStalk z p = u := by
    have : u ∈ Set.range (X.fromSpecStalk z) := by
      rw [Scheme.range_fromSpecStalk]
      exact h
    exact this
  refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
  unfold a3i_stalkIdeal
  split
  · rfl
  · exact absurd hex ‹_›

/-- `codim u + dim 𝒪_{X,z}/𝔭_u = codim z` for `u ⤳ z` on an integral scheme locally of finite
type over `ℂ`.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.20; Matsumura, *Commutative Ring
Theory*, Theorem 5.6. -/
theorem a3c_coheight_add_ringKrullDim_stalkIdeal (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (z u : X.left) (h : u ⤳ z) :
    ((Order.coheight u : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (X.left.presheaf.stalk z ⧸ a3i_stalkIdeal X.left z u) =
      Order.coheight z := by
  obtain ⟨p, hp, heq⟩ := a3c_stalkIdeal_spec X.left z u h
  rw [heq, ← ringKrullDim_stalk_eq_coheight z, ← hp, ← a3c_coheight_fromSpecStalk z p,
    ← idealHeight_eq_coheight]
  have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  exact a3c_height_add_ringKrullDim_quotient_stalk X z p.asIdeal

end HodgeLean.Adapters
