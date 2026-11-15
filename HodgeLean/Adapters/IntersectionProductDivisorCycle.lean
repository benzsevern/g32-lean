import HodgeLean.Adapters.IntersectionProductDivisorLocal
import HodgeLean.Adapters.IntersectionProductMovingGlue
import HodgeLean.Adapters.IntersectionProductCMComponent
import HodgeLean.Adapters.IntersectionProductCycle

/-! # Orders of vanishing on a subvariety, read in the local rings of the ambient scheme

Toward the cycle form of Fulton, Theorem 2.4, for Serre's product: the local identity
`a3w_principal_stalk` speaks of localized lengths in `A = 𝒪_{X,T}`, the principal cycles of
`a2_principalCycle` of orders of vanishing `Scheme.ord` on `W = closure {w}`. This file connects
them:
* the closed immersion `W → X` pulls the prime of a point of `W` in `𝒪_{W,T}` back to the prime of
  its image in `𝒪_{X,T}` (`a3y_comap_stalkIdeal`), and the kernel of `𝒪_{X,T} → 𝒪_{W,T}` is the
  prime `𝔭_W` (`a3y_ker_stalkMap`);
* for a codimension-one point `D` of `W` through `T` and `a ∈ 𝒪_{X,T} ∖ 𝔭_W`,
  `ord_D(a|_W) = ℓ((𝒪_{X,T} ⧸ (𝔭_W + a))_D)` (`a3y_ord_eq_locLen`);
* for `T` itself of codimension one on `Z = closure {z}` and `a ∉ 𝔭_Z`,
  `ord_T(a|_Z) = e_a(𝒪_{X,T} ⧸ 𝔭_Z)` (`a3y_ord_eq_herbrand`).

Source: Fulton, *Intersection Theory*, second edition, §1.2 and Example A.2.1; Hartshorne,
*Algebraic Geometry*, II, Proposition 2.2 and Exercise 3.11. HC no distance; AV milestone no
distance.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing HodgeLean.Foundations.Curves Order
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters
universe u

section plumbing

/-- `a3i_stalkIdeal X z u` is the prime of any point of `Spec 𝒪_{X,z}` over `u`. -/
theorem a3y_stalkIdeal_eq {X : Scheme.{u}} {z u : X} (p : Spec (X.presheaf.stalk z))
    (hp : X.fromSpecStalk z p = u) : a3i_stalkIdeal X z u = p.asIdeal := by
  have h : u ⤳ z := by
    have : u ∈ Set.range (X.fromSpecStalk z) := ⟨p, hp⟩
    rwa [Scheme.range_fromSpecStalk] at this
  obtain ⟨q, hq, hqe⟩ := a3c_stalkIdeal_spec X z u h
  rw [hqe]
  have : q = p := (X.fromSpecStalk z).isEmbedding.injective (hq.trans hp.symm)
  rw [this]

/-- The stalk map of a morphism pulls `a3i_stalkIdeal` back to `a3i_stalkIdeal`. -/
theorem a3y_comap_stalkIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) {x v : X} (h : v ⤳ x) :
    (a3i_stalkIdeal X x v).comap (f.stalkMap x).hom = a3i_stalkIdeal Y (f x) (f v) := by
  obtain ⟨p, hp, hpe⟩ := a3c_stalkIdeal_spec X x v h
  rw [hpe]
  have key := congrArg (fun g => g.base p) (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x))
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at key
  rw [hp] at key
  rw [a3y_stalkIdeal_eq _ key]
  rfl

/-- The kernel of `𝒪_{X,x} → 𝒪_{W,x}` for `W = closure {w}` is the prime of `w`. -/
theorem a3y_ker_stalkMap (X : Scheme.{u}) (w : X) (x : cycleComponent X w) :
    RingHom.ker ((cycleComponentι X w).stalkMap x).hom =
      a3i_stalkIdeal X (cycleComponentι X w x) w := by
  have h := a3y_comap_stalkIdeal (cycleComponentι X w)
    ((genericPoint_spec (cycleComponent X w)).specializes (Set.mem_univ x))
  rw [a3c_stalkIdeal_genericPoint, a3m_cycleComponentι_genericPoint] at h
  rw [← h]
  rfl

end plumbing

section ord

/-- The order of vanishing of an element of a local ring of codimension one is the length of its
quotient. -/
theorem a3y_ord_algebraMap {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (hx : Order.coheight x = 1) (r : X.presheaf.stalk x) (hr : r ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField r) x =
      ((Ring.ord (X.presheaf.stalk x) r).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := AlgebraicGeometry.krullDimLE_of_coheight_le hx.le
  have hnz : r ∈ nonZeroDivisors (X.presheaf.stalk x) := mem_nonZeroDivisors_of_ne_zero hr
  have hne : Ring.ord (X.presheaf.stalk x) r ≠ ⊤ := Ring.ord_ne_top hnz
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk x)
    (algebraMap (X.presheaf.stalk x) X.functionField r)).unzeroD 1) = _
  rw [Ring.ordFrac_eq_ord _ hr]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  simp [Ring.ordMonoidWithZeroHom, hnz, ← hn, WithZero.unzeroD]

/-- The algebra maps from the local rings to the function field commute with specialization. -/
theorem a3y_algebraMap_stalkSpecializes {X : Scheme.{u}} [IsIntegral X] {x y : X} (h : x ⤳ y)
    (r : X.presheaf.stalk y) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.stalkSpecializes h).hom r) =
      algebraMap (X.presheaf.stalk y) X.functionField r := by
  change ((X.presheaf.stalkSpecializes h) ≫ X.presheaf.stalkSpecializes
    ((genericPoint_spec X).specializes (Set.mem_univ x))).hom r =
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ y))).hom r
  rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- The length of `R ⧸ (r)` for a localization `R = R₀_𝔭` is the localized length of
`R₀ ⧸ (r)`. -/
theorem a3y_length_quot_localization {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    (𝔭 : PrimeSpectrum R₀) [IsLocalization.AtPrime R 𝔭.asIdeal] (r : R₀) :
    Module.length R (R ⧸ Ideal.span {algebraMap R₀ R r}) =
      a3e_locLen 𝔭 (R₀ ⧸ Ideal.span {r}) := by
  rw [a3q_locLen_eq_length (B := R) 𝔭 _ _ (TensorProduct.mk R₀ R (R₀ ⧸ Ideal.span {r}) 1)]
  have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (Ideal.span {r})).toLinearEquiv
  rw [← e.length_eq, Ideal.map_span, Set.image_singleton]

end ord

section locLenSurj
variable {A R₀ : Type u} [CommRing A] [CommRing R₀] (ρ : A →+* R₀) (hρ : Function.Surjective ρ)
  (𝔇 : PrimeSpectrum R₀)

include hρ in
/-- Localized lengths along a surjective ring map: for an `R₀`-module `M`, viewed as an
`A`-module through `ρ`, the length of `M` localized at `ρ⁻¹ 𝔇` over `A` is that at `𝔇` over
`R₀`. -/
theorem a3y_locLen_surj (M : Type u) [AddCommGroup M] [Module R₀ M] :
    @a3e_locLen A _ ⟨𝔇.asIdeal.comap ρ, Ideal.comap_isPrime _ _⟩ M _ (Module.compHom M ρ) =
      a3e_locLen 𝔇 M := by
  let : Module A M := Module.compHom M ρ
  set 𝔓 : PrimeSpectrum A := ⟨𝔇.asIdeal.comap ρ, Ideal.comap_isPrime _ _⟩
  let X := LocalizedModule 𝔇.asIdeal.primeCompl M
  let π : Localization.AtPrime 𝔓.asIdeal →+* Localization.AtPrime 𝔇.asIdeal :=
    Localization.localRingHom 𝔓.asIdeal 𝔇.asIdeal ρ rfl
  let : Module (Localization.AtPrime 𝔓.asIdeal) X := Module.compHom X π
  let : Module A X := Module.compHom X ((algebraMap R₀ (Localization.AtPrime 𝔇.asIdeal)).comp ρ)
  have : IsScalarTower A (Localization.AtPrime 𝔓.asIdeal) X := ⟨fun a b x => by
    change π (a • b) • x = algebraMap R₀ (Localization.AtPrime 𝔇.asIdeal) (ρ a) • π b • x
    rw [Algebra.smul_def, map_mul, Localization.localRingHom_to_map, mul_smul]⟩
  have hsmul : ∀ (a : A) (x : X), a • x = ρ a • x := fun a x => by
    change algebraMap R₀ (Localization.AtPrime 𝔇.asIdeal) (ρ a) • x = _
    rw [algebraMap_smul]
  let g : M →ₗ[A] X :=
    { toFun := fun m => LocalizedModule.mkLinearMap 𝔇.asIdeal.primeCompl M m
      map_add' := map_add _
      map_smul' := fun a m => by
        rw [RingHom.id_apply, hsmul]
        exact map_smul (LocalizedModule.mkLinearMap 𝔇.asIdeal.primeCompl M) (ρ a) m }
  have : IsLocalizedModule 𝔓.asIdeal.primeCompl g := by
    constructor
    · rintro ⟨s, hs⟩
      have hb := (Module.End.isUnit_iff _).1
        (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap 𝔇.asIdeal.primeCompl M)
          (⟨ρ s, hs⟩ : 𝔇.asIdeal.primeCompl))
      rw [Module.End.isUnit_iff]
      convert hb using 1
      funext x
      exact hsmul s x
    · intro y
      induction y using LocalizedModule.induction_on with
      | h m t =>
        obtain ⟨s, hs⟩ := hρ t
        have hs' : s ∈ 𝔓.asIdeal.primeCompl := by
          change ρ s ∉ 𝔇.asIdeal; rw [hs]; exact t.2
        refine ⟨(m, ⟨s, hs'⟩), ?_⟩
        change s • LocalizedModule.mk m t = LocalizedModule.mk m 1
        rw [hsmul, hs, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
          LocalizedModule.mk_cancel]
    · intro m m' h
      obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.1 h
      obtain ⟨s, hs⟩ := hρ t
      have hs' : s ∈ 𝔓.asIdeal.primeCompl := by
        change ρ s ∉ 𝔇.asIdeal; rw [hs]; exact t.2
      refine ⟨⟨s, hs'⟩, ?_⟩
      simp only [one_smul] at ht
      change ρ s • m = ρ s • m'
      rw [hs]
      exact ht
  rw [a3q_locLen_eq_length (B := Localization.AtPrime 𝔓.asIdeal) 𝔓 M X g]
  let : Algebra (Localization.AtPrime 𝔓.asIdeal) (Localization.AtPrime 𝔇.asIdeal) :=
    π.toAlgebra
  have : IsScalarTower (Localization.AtPrime 𝔓.asIdeal) (Localization.AtPrime 𝔇.asIdeal) X :=
    ⟨fun b r x => by
      change (π b * r) • x = π b • (r • x)
      rw [mul_smul]⟩
  refine Module.length_eq_of_surjective ?_
  intro y
  obtain ⟨r, t, rfl⟩ := IsLocalization.exists_mk'_eq 𝔇.asIdeal.primeCompl y
  obtain ⟨a, rfl⟩ := hρ r
  obtain ⟨s, hs⟩ := hρ t
  have hs' : s ∈ 𝔓.asIdeal.primeCompl := by
    change ρ s ∉ 𝔇.asIdeal; rw [hs]; exact t.2
  refine ⟨IsLocalization.mk' _ a ⟨s, hs'⟩, ?_⟩
  change π _ = _
  rw [Localization.localRingHom_mk']
  congr 1
  exact Subtype.ext hs

end locLenSurj

section ordSubvariety
variable (X : Scheme.{u}) [IsLocallyNoetherian X] (w : X)

/-- `A ⧸ (P + a) ≅ R₀ ⧸ (ρ a)` for a surjection `ρ : A → R₀` with kernel `P`, as `A`-modules. -/
def a3y_quotEquiv {A R₀ : Type u} [CommRing A] [CommRing R₀] (ρ : A →+* R₀)
    (hρ : Function.Surjective ρ) (a : A) :
    @LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _
      (QuotSMulTop a (A ⧸ RingHom.ker ρ)) (R₀ ⧸ Ideal.span {ρ a}) _ _ _
      (Module.compHom (R₀ ⧸ Ideal.span {ρ a}) ρ) := by
  letI : Module A (R₀ ⧸ Ideal.span {ρ a}) := Module.compHom _ ρ
  have hcomap : (Ideal.span {ρ a}).comap ρ = Ideal.span {a} ⊔ RingHom.ker ρ := by
    rw [← Ideal.comap_map_of_surjective' ρ hρ, Ideal.map_span, Set.image_singleton]
  let e₁ : QuotSMulTop a (A ⧸ RingHom.ker ρ) ≃ₗ[A] A ⧸ (Ideal.span {a} ⊔ RingHom.ker ρ) :=
    (Submodule.quotEquivOfEq (a • (⊤ : Submodule A (A ⧸ RingHom.ker ρ)))
      ((Ideal.span {a}) • (⊤ : Submodule A (A ⧸ RingHom.ker ρ)))
      (Submodule.ideal_span_singleton_smul a ⊤).symm).trans (a3c_quotSMulEquiv _ _)
  let f : A ⧸ (Ideal.span {a} ⊔ RingHom.ker ρ) →ₗ[A] R₀ ⧸ Ideal.span {ρ a} :=
    { toFun := Ideal.quotientMap (Ideal.span {ρ a}) ρ hcomap.symm.le
      map_add' := map_add _
      map_smul' := fun c x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.quotientMap _ ρ _ (Ideal.Quotient.mk _ (c * x)) =
          ρ c • Ideal.quotientMap _ ρ _ (Ideal.Quotient.mk _ x)
        simp [Ideal.quotientMap_mk, Algebra.smul_def] }
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.quotientMap (Ideal.span {ρ a}) ρ hcomap.symm.le
        (Ideal.Quotient.mk (Ideal.span {a} ⊔ RingHom.ker ρ) x) = 0 at hx
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap] at hx
      rw [Submodule.mem_bot]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, rfl⟩ := hρ y
      exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  exact e₁.trans (LinearEquiv.ofBijective f hf)

/-- The order of vanishing on `W = closure {w}`, along a codimension-one point `D` of `W` through
`T`, of an element `a` of `𝒪_{X,T}` not vanishing on `W`, is the localized length
`ℓ((𝒪_{X,T} ⧸ (𝔭_W + a))_D)`.
Source: Fulton, *Intersection Theory*, second edition, §1.2 and Example A.2.1; Mathlib,
`AlgebraicGeometry.Scheme.ord`. -/
theorem a3y_ord_eq_locLen (T D : cycleComponent X w) (h : D ⤳ T)
    (hD : Order.coheight D = 1) (a : X.presheaf.stalk (cycleComponentι X w T))
    (ha : a ∉ a3i_stalkIdeal X (cycleComponentι X w T) w) :
    (cycleComponent X w).ord (algebraMap ((cycleComponent X w).presheaf.stalk T)
        (cycleComponent X w).functionField (((cycleComponentι X w).stalkMap T).hom a)) D =
      ((a3e_locLen ⟨a3i_stalkIdeal X (cycleComponentι X w T) (cycleComponentι X w D),
          a3q_stalkIdeal_isPrime X ((h.map (cycleComponentι X w).continuous))⟩
        (QuotSMulTop a (X.presheaf.stalk (cycleComponentι X w T) ⧸
          a3i_stalkIdeal X (cycleComponentι X w T) w))).toNat : ℤ) := by
  set ρ := ((cycleComponentι X w).stalkMap T).hom
  have hρ : Function.Surjective ρ := (cycleComponentι X w).stalkMap_surjective T
  have hker : RingHom.ker ρ = a3i_stalkIdeal X ((cycleComponentι X w) T) w := a3y_ker_stalkMap X w T
  have hr : ρ a ≠ 0 := fun h0 => ha (hker ▸ (RingHom.mem_ker.2 h0))
  set σ := ((cycleComponent X w).presheaf.stalkSpecializes h).hom
  rw [← a3y_algebraMap_stalkSpecializes h]
  have hσ : σ (ρ a) ≠ 0 := by
    intro h0
    apply hr
    have := a3y_algebraMap_stalkSpecializes h (ρ a)
    rw [h0, map_zero] at this
    exact (IsFractionRing.injective ((cycleComponent X w).presheaf.stalk T)
      (cycleComponent X w).functionField)
      (this.symm.trans (map_zero _).symm)
  rw [a3y_ord_algebraMap D hD _ hσ]
  congr 2
  let := σ.toAlgebra
  have := a3q_stalkIdeal_isPrime (cycleComponent X w) h
  have := a3q_isLocalization_stalkSpecializes (cycleComponent X w) h
  have h1 := a3y_length_quot_localization (R := (cycleComponent X w).presheaf.stalk D)
    ⟨a3i_stalkIdeal (cycleComponent X w) T D, inferInstance⟩ (ρ a)
  change Module.length _ (_ ⧸ Ideal.span {σ (ρ a)}) = _
  rw [show σ (ρ a) = algebraMap ((cycleComponent X w).presheaf.stalk T)
    ((cycleComponent X w).presheaf.stalk D) (ρ a) from rfl, h1]
  have h2 := a3y_locLen_surj ρ hρ ⟨a3i_stalkIdeal (cycleComponent X w) T D, inferInstance⟩
    (((cycleComponent X w).presheaf.stalk T) ⧸ Ideal.span {ρ a})
  rw [← h2]
  have hcomap : (a3i_stalkIdeal (cycleComponent X w) T D).comap ρ =
      a3i_stalkIdeal X ((cycleComponentι X w) T) ((cycleComponentι X w) D) :=
    a3y_comap_stalkIdeal (cycleComponentι X w) h
  let : Module (X.presheaf.stalk ((cycleComponentι X w) T))
      (((cycleComponent X w).presheaf.stalk T) ⧸ Ideal.span {ρ a}) :=
    Module.compHom _ ρ
  have e := a3y_quotEquiv ρ hρ a
  rw [hker] at e
  rw [a3e_locLen_congr _ e]
  congr 1
  exact PrimeSpectrum.ext hcomap

end ordSubvariety

section herbrand

/-- In a local ring the localized length at the maximal ideal is the length. -/
theorem a3y_locLen_closedPoint {A : Type u} [CommRing A] [IsLocalRing A] (M : Type u)
    [AddCommGroup M] [Module A M] :
    a3e_locLen (closedPoint A) M = Module.length A M := by
  have : IsLocalization (closedPoint A).asIdeal.primeCompl A :=
    IsLocalization.self fun x hx => by
      by_contra h
      exact hx ((IsLocalRing.mem_maximalIdeal x).2 h)
  have : IsLocalization.AtPrime A (closedPoint A).asIdeal := this
  have := isLocalizedModule_id (closedPoint A).asIdeal.primeCompl M A
  exact a3q_locLen_eq_length (B := A) (closedPoint A) M M LinearMap.id

/-- On a subvariety `Z = closure {z}`, the order of vanishing at a codimension-one point `T` of an
element `a ∈ 𝒪_{X,T} ∖ 𝔭_Z` is the Herbrand difference `e_a(𝒪_{X,T} ⧸ 𝔭_Z) = ℓ(𝒪_{X,T} ⧸ (𝔭_Z + a))`.
Source: Fulton, *Intersection Theory*, second edition, Example A.2.1 and Lemma A.2.2. -/
theorem a3y_ord_eq_herbrand (X : Scheme.{u}) [IsLocallyNoetherian X] (z : X)
    (T : cycleComponent X z) (hT : Order.coheight T = 1)
    (a : X.presheaf.stalk (cycleComponentι X z T))
    (ha : a ∉ a3i_stalkIdeal X (cycleComponentι X z T) z) :
    (cycleComponent X z).ord (algebraMap ((cycleComponent X z).presheaf.stalk T)
        (cycleComponent X z).functionField (((cycleComponentι X z).stalkMap T).hom a)) T =
      a3e_herbrand a (X.presheaf.stalk (cycleComponentι X z T) ⧸
        a3i_stalkIdeal X (cycleComponentι X z T) z) := by
  rw [a3y_ord_eq_locLen X z T T (specializes_refl T) hT a ha]
  have hP : (a3i_stalkIdeal X (cycleComponentι X z T) z).IsPrime := by
    have h := (genericPoint_spec (cycleComponent X z)).specializes (Set.mem_univ T)
    have h' := h.map (cycleComponentι X z).continuous
    rw [a3m_cycleComponentι_genericPoint] at h'
    exact a3q_stalkIdeal_isPrime X h'
  have hcl : (⟨a3i_stalkIdeal X (cycleComponentι X z T) (cycleComponentι X z T),
      a3q_stalkIdeal_isPrime X (specializes_refl _)⟩ :
        PrimeSpectrum (X.presheaf.stalk (cycleComponentι X z T))) = closedPoint _ :=
    PrimeSpectrum.ext (a3c_stalkIdeal_self X _)
  rw [hcl, a3y_locLen_closedPoint]
  have hker : a3e_kerSMul a (X.presheaf.stalk (cycleComponentι X z T) ⧸
      a3i_stalkIdeal X (cycleComponentι X z T) z) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : Ideal.Quotient.mk _ (a * x) = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx'
    rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact (hP.mem_or_mem hx').resolve_left ha
  unfold a3e_herbrand
  rw [hker]
  have : Module.length (X.presheaf.stalk (cycleComponentι X z T))
      (⊥ : Submodule (X.presheaf.stalk (cycleComponentι X z T))
        (X.presheaf.stalk (cycleComponentι X z T) ⧸
          a3i_stalkIdeal X (cycleComponentι X z T) z)) = 0 := Module.length_eq_zero
  rw [this]
  simp

end herbrand

section germ
variable {X : Scheme.{u}} (w : X)

/-- The restriction `𝒪_{X,T} → 𝒪_{W,T} → K(W)` to the function field of `W = closure {w}`, read
through a point `T_W` of `W` over `T`. -/
def a3y_germ {T : X} (TW : cycleComponent X w) (h : cycleComponentι X w TW = T) :
    X.presheaf.stalk T →+* (cycleComponent X w).functionField :=
  (algebraMap ((cycleComponent X w).presheaf.stalk TW) (cycleComponent X w).functionField).comp
    (((cycleComponentι X w).stalkMap TW).hom.comp
      (X.presheaf.stalkSpecializes (specializes_of_eq h)).hom)

theorem a3y_germ_self (TW : cycleComponent X w) (a : X.presheaf.stalk (cycleComponentι X w TW)) :
    a3y_germ w TW rfl a = algebraMap ((cycleComponent X w).presheaf.stalk TW)
      (cycleComponent X w).functionField (((cycleComponentι X w).stalkMap TW).hom a) := by
  simp [a3y_germ, TopCat.Presheaf.stalkSpecializes_refl]

/-- `a` restricts to zero on `W` exactly when it lies in the prime of `W`. -/
theorem a3y_germ_eq_zero_iff {T : X} (TW : cycleComponent X w) (h : cycleComponentι X w TW = T)
    (a : X.presheaf.stalk T) : a3y_germ w TW h a = 0 ↔ a ∈ a3i_stalkIdeal X T w := by
  subst h
  rw [a3y_germ_self, map_eq_zero_iff _ (IsFractionRing.injective _ _), ← RingHom.mem_ker,
    a3y_ker_stalkMap]

/-- The order of vanishing on `W` along a codimension-one point `D` through `T` of the
restriction of `a ∈ 𝒪_{X,T}`. -/
theorem a3y_ord_germ [IsLocallyNoetherian X] {T : X} (TW D : cycleComponent X w)
    (h : cycleComponentι X w TW = T) (hD : D ⤳ TW) (hD1 : Order.coheight D = 1)
    (a : X.presheaf.stalk T) (ha : a ∉ a3i_stalkIdeal X T w) :
    (cycleComponent X w).ord (a3y_germ w TW h a) D =
      ((a3e_locLen ⟨a3i_stalkIdeal X T (cycleComponentι X w D),
          a3q_stalkIdeal_isPrime X (h ▸ hD.map (cycleComponentι X w).continuous)⟩
        (QuotSMulTop a (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T w))).toNat : ℤ) := by
  subst h
  rw [a3y_germ_self]
  exact a3y_ord_eq_locLen X w TW D hD hD1 a ha

/-- The order of vanishing on `Z = closure {z}` at a codimension-one point `T` of the restriction
of `a ∈ 𝒪_{X,T}` is the Herbrand difference of `a` on `𝒪_{X,T} ⧸ 𝔭_Z`. -/
theorem a3y_ord_germ_self [IsLocallyNoetherian X] {T : X} (TZ : cycleComponent X w)
    (h : cycleComponentι X w TZ = T) (hT1 : Order.coheight TZ = 1)
    (a : X.presheaf.stalk T) (ha : a ∉ a3i_stalkIdeal X T w) :
    (cycleComponent X w).ord (a3y_germ w TZ h a) TZ =
      a3e_herbrand a (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T w) := by
  subst h
  rw [a3y_germ_self]
  exact a3y_ord_eq_herbrand X w TZ hT1 a ha

end germ

section principal
variable (X : Scheme.{u}) [IsNoetherian X] (w : X)

instance a3y_cycleComponent_isNoetherian : IsNoetherian (cycleComponent X w) := by
  have : CompactSpace (cycleComponent X w) :=
    (cycleComponentι X w).isClosedEmbedding.compactSpace
  exact ⟨⟩

/-- The coefficient of `[div φ]` at a point of `W = closure {w}` is the order of `φ`. -/
theorem a3y_principalCycle_apply (φ : (cycleComponent X w).functionField) (hφ : φ ≠ 0)
    (D : cycleComponent X w) :
    a2_principalCycle X ℚ w φ (cycleComponentι X w D) = ((cycleComponent X w).ord φ D : ℚ) := by
  classical
  have hD : ∀ z, (principalDivisor (cycleComponent X w) φ :
      AlgebraicCycle (cycleComponent X w) ℤ) z = (cycleComponent X w).ord φ z := fun z => by
    have hfin : (Function.support (ordAt (cycleComponent X w) φ)).Finite :=
      a3m_ord_support_finite φ hφ
    rw [principalDivisor, dite_eq_left hfin]
    rfl
  rw [a2_principalCycle, Function.locallyFinsuppWithin.mapRange_apply,
    a1p_pushforward_apply_eq_sum _ _ _ {D}]
  · rw [Finset.sum_singleton, a3m_degree_closedImmersion, hD]
    simp
  · intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [(cycleComponentι X w).isClosedEmbedding.injective hx.1]
  · simp

/-- `[div φ]` vanishes off `W`. -/
theorem a3y_principalCycle_apply_of_not_mem (φ : (cycleComponent X w).functionField) (x : X)
    (hx : x ∉ Set.range (cycleComponentι X w)) : a2_principalCycle X ℚ w φ x = 0 := by
  classical
  rw [a2_principalCycle, Function.locallyFinsuppWithin.mapRange_apply,
    a1p_pushforward_apply_eq_sum _ _ _ ∅]
  · simp
  · intro y hy
    exact absurd ⟨y, hy.1⟩ hx
  · simp

end principal

section intersectPrime
variable (X : Scheme.{u}) [IsNoetherian X]

/-- A closed subscheme of a Noetherian scheme has finitely many irreducible components, and these
have distinct generic points. -/
theorem a3y_components_finite (J : X.IdealSheafData) :
    {y : J.subscheme | closure ({y} : Set J.subscheme) ∈
      irreducibleComponents J.subscheme}.Finite := by
  have hemb := J.subschemeι.isClosedEmbedding
  have : TopologicalSpace.NoetherianSpace J.subscheme := hemb.isEmbedding.noetherianSpace
  refine Set.Finite.of_finite_image (f := fun y => closure ({y} : Set J.subscheme)) ?_ ?_
  · exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).subset (by
      rintro _ ⟨y, hy, rfl⟩; exact hy)
  · intro y _ y' _ h
    exact (inseparable_iff_closure_eq.2 h).eq

open Classical in
/-- The coefficient of the intersection cycle of two prime cycles at a point: Serre's
multiplicity there if it is the generic point of a component of the intersection, else `0`. -/
theorem a3y_intersectPrime_apply (u v x : X) :
    a3i_intersectPrime X u v x =
      if ∃ y : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme,
          closure ({y} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
            irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme ∧
          (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι y = x
      then (a3i_serreMult X x u v : ℚ) else 0 := by
  set J := ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v
  have hfin := a3y_components_finite X J
  unfold a3i_intersectPrime
  rw [a3c_finsum_apply]
  · split_ifs with hex
    · obtain ⟨y₀, hy₀, hx⟩ := hex
      rw [finsum_eq_single _ y₀]
      · rw [ite_eq_left hy₀, Function.locallyFinsuppWithin.single_apply, ite_eq_left hx.symm, hx]
      · intro y hy
        split_ifs with hc
        · rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right]
          intro hxy
          exact hy (J.subschemeι.isClosedEmbedding.injective (hxy.symm.trans hx.symm))
        · rfl
    · refine finsum_eq_zero_of_forall_eq_zero fun y => ?_
      split_ifs with hc
      · rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right]
        exact fun hxy => hex ⟨y, hc, hxy.symm⟩
      · rfl
  · refine hfin.subset fun y hy => ?_
    by_contra hc
    exact hy (ite_eq_right hc)

end intersectPrime

section components

/-- A point with no proper generization is the generic point of an irreducible component. -/
theorem a3y_mem_irreducibleComponents_of_maximal {S : Type*} [TopologicalSpace S] [QuasiSober S]
    [T0Space S] (y : S) (hmax : ∀ y' : S, y' ⤳ y → y' = y) :
    closure ({y} : Set S) ∈ irreducibleComponents S := by
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({y} : Set S)) isIrreducible_singleton.closure
  obtain ⟨g, hg⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  have hyC : y ∈ C := hsub (subset_closure rfl)
  have hgy : g ⤳ y := by
    rw [specializes_iff_mem_closure, hg.def]; exact hyC
  have := hmax g hgy
  subst this
  rw [hg.def]
  exact hC

/-- A point of `closure {u} ∩ closure {v}` with no proper generization in that intersection is the
generic point of an irreducible component of the scheme-theoretic intersection. -/
theorem a3y_component_of_maximal {X : Scheme.{u}} (u v T : X) (hu : u ⤳ T) (hv : v ⤳ T)
    (hmax : ∀ q : X, u ⤳ q → v ⤳ q → q ⤳ T → q = T) :
    ∃ y : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme,
      closure ({y} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme ∧
      (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι y = T := by
  set J := ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v
  have hrange : Set.range J.subschemeι = closure {u} ∩ closure {v} := by
    rw [Scheme.IdealSheafData.range_subschemeι, a3m_support_sup_primeIdeal]
  obtain ⟨y, hy⟩ : T ∈ Set.range J.subschemeι := by
    rw [hrange]
    exact ⟨specializes_iff_mem_closure.1 hu, specializes_iff_mem_closure.1 hv⟩
  refine ⟨y, a3y_mem_irreducibleComponents_of_maximal y fun y' hy' => ?_, hy⟩
  have h1 := hy'.map J.subschemeι.continuous
  rw [hy] at h1
  have hmem : J.subschemeι y' ∈ closure {u} ∩ closure {v} := hrange ▸ ⟨y', rfl⟩
  have := hmax _ (specializes_iff_mem_closure.2 hmem.1) (specializes_iff_mem_closure.2 hmem.2) h1
  exact J.subschemeι.isClosedEmbedding.injective (this.trans hy.symm)

end components

section spec
variable {X : Scheme.{u}} (T : X)

/-- The point of `Spec 𝒪_{X,T}` over a generization `u` of `T`: the prime `a3i_stalkIdeal X T u`. -/
def a3y_pt (u : X) (h : u ⤳ T) : PrimeSpectrum (X.presheaf.stalk T) :=
  ⟨a3i_stalkIdeal X T u, a3q_stalkIdeal_isPrime X h⟩

theorem a3y_fromSpecStalk_pt (u : X) (h : u ⤳ T) : X.fromSpecStalk T (a3y_pt T u h) = u := by
  obtain ⟨p, hp, hpe⟩ := a3c_stalkIdeal_spec X T u h
  have : a3y_pt T u h = p := PrimeSpectrum.ext hpe
  rw [this, hp]

theorem a3y_pt_fromSpecStalk (p : PrimeSpectrum (X.presheaf.stalk T)) :
    a3y_pt T (X.fromSpecStalk T p) (by
      have : X.fromSpecStalk T p ∈ Set.range (X.fromSpecStalk T) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this) = p :=
  (X.fromSpecStalk T).isEmbedding.injective (a3y_fromSpecStalk_pt T _ _)

theorem a3y_specializes_fromSpecStalk (p : PrimeSpectrum (X.presheaf.stalk T)) :
    X.fromSpecStalk T p ⤳ T := by
  have : X.fromSpecStalk T p ∈ Set.range (X.fromSpecStalk T) := ⟨p, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem a3y_pt_le_iff (u u' : X) (h : u ⤳ T) (h' : u' ⤳ T) :
    a3y_pt T u h ≤ a3y_pt T u' h' ↔ u ⤳ u' := by
  rw [PrimeSpectrum.le_iff_specializes, ← (X.fromSpecStalk T).isEmbedding.isInducing.specializes_iff,
    a3y_fromSpecStalk_pt, a3y_fromSpecStalk_pt]

theorem a3y_pt_self : a3y_pt T T (specializes_refl T) = closedPoint _ :=
  PrimeSpectrum.ext (a3c_stalkIdeal_self X T)

theorem a3y_pt_injective (u u' : X) (h : u ⤳ T) (h' : u' ⤳ T)
    (he : a3y_pt T u h = a3y_pt T u' h') : u = u' := by
  rw [← a3y_fromSpecStalk_pt T u h, ← a3y_fromSpecStalk_pt T u' h', he]

end spec

section geom
variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A proper specialization raises the codimension. -/
theorem a3y_coheight_lt {x y : X} (h : x ⤳ y) (hne : x ≠ y) :
    Order.coheight x < Order.coheight y :=
  Order.coheight_strictAnti (lt_of_le_not_ge (Scheme.le_iff_specializes.2 h)
    fun h' => hne (h.antisymm (Scheme.le_iff_specializes.1 h')).eq)
    (lt_top_iff_ne_top.2 (a3c_coheight_ne_top X x))

theorem a3y_eq_of_specializes {x y : X} (h : x ⤳ y)
    (hle : Order.coheight y ≤ Order.coheight x) : x = y := by
  by_contra hne
  exact absurd hle (not_le.2 (a3y_coheight_lt h hne))

variable (w v : X)

/-- The generic points of the irreducible components of `closure {w} ∩ closure {v}`. -/
def a3y_comps : Set X :=
  {z | ∃ y : (ccm3_primeIdeal X w ⊔ ccm3_primeIdeal X v).subscheme,
    closure ({y} : Set (ccm3_primeIdeal X w ⊔ ccm3_primeIdeal X v).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X w ⊔ ccm3_primeIdeal X v).subscheme ∧
    (ccm3_primeIdeal X w ⊔ ccm3_primeIdeal X v).subschemeι y = z}

omit [IsLocallyNoetherian X] in
theorem a3y_comps_finite [IsNoetherian X] : (a3y_comps w v).Finite :=
  ((a3y_components_finite X _).image _).subset (by
    rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩)

omit [IsLocallyNoetherian X] in
theorem a3y_comps_spec {z : X} (hz : z ∈ a3y_comps w v) :
    w ⤳ z ∧ v ⤳ z ∧ ∀ z' : X, w ⤳ z' → v ⤳ z' → z' ⤳ z → z' = z := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact a3m_component_spec w v y hy

omit [IsLocallyNoetherian X] in
/-- Every point of `closure {w} ∩ closure {v}` lies on a component. -/
theorem a3y_exists_comp {q : X} (hw : w ⤳ q) (hv : v ⤳ q) : ∃ z ∈ a3y_comps w v, z ⤳ q := by
  set J := ccm3_primeIdeal X w ⊔ ccm3_primeIdeal X v
  have hrange : Set.range J.subschemeι = closure {w} ∩ closure {v} := by
    rw [Scheme.IdealSheafData.range_subschemeι, a3m_support_sup_primeIdeal]
  obtain ⟨y, rfl⟩ : q ∈ Set.range J.subschemeι := by
    rw [hrange]
    exact ⟨specializes_iff_mem_closure.1 hw, specializes_iff_mem_closure.1 hv⟩
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({y} : Set J.subscheme)) isIrreducible_singleton.closure
  obtain ⟨g, hg⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  refine ⟨J.subschemeι g, ⟨g, by rw [hg.def]; exact hC, rfl⟩, ?_⟩
  have hgy : g ⤳ y := by
    rw [specializes_iff_mem_closure, hg.def]; exact hsub (subset_closure rfl)
  exact hgy.map J.subschemeι.continuous

omit [IsLocallyNoetherian X] in
theorem a3y_coheight_comps (hWV : a3i_MeetProperly X w v) {z : X} (hz : z ∈ a3y_comps w v) :
    Order.coheight z = Order.coheight w + Order.coheight v := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact hWV y hy

/-- At a point `T` of codimension one more than the components through it, every point of
`closure {w} ∩ closure {v}` specializing to `T` is `T` or the generic point of a component. -/
theorem a3y_good {T : X}
    (hloc : ∀ z ∈ a3y_comps w v, z ⤳ T → Order.coheight z = Order.coheight w + Order.coheight v)
    (hT : Order.coheight T = Order.coheight w + Order.coheight v + 1) {q : X} (hw : w ⤳ q)
    (hv : v ⤳ q) (hq : q ⤳ T) : q = T ∨ q ∈ a3y_comps w v := by
  obtain ⟨z, hz, hzq⟩ := a3y_exists_comp w v hw hv
  by_cases hqz : z = q
  · exact Or.inr (hqz ▸ hz)
  · left
    refine a3y_eq_of_specializes hq ?_
    have hlt := a3y_coheight_lt hzq hqz
    rw [hloc z hz (hzq.trans hq)] at hlt
    rw [hT]
    exact Order.add_one_le_of_lt hlt

end geom

section dims
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]

/-- Codimensions on a variety are natural numbers adding up with the dimension of local
quotients: `codim u + dim 𝒪_{X,T}/𝔭_u = codim T` for `u ⤳ T`. -/
theorem a3y_dims {T u : X.left} (h : u ⤳ T) :
    ∃ cu ct n : ℕ, coheight u = cu ∧ coheight T = ct ∧
      ringKrullDim (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T u) = n ∧ cu + n = ct := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hfin := a3c_coheight_ne_top X.left T
  obtain ⟨ct, hct⟩ := ENat.ne_top_iff_exists.1 hfin
  have hsum := a3c_coheight_add_ringKrullDim_stalkIdeal X T u h
  rw [← hct] at hsum
  obtain ⟨cu, n, hcu, hn, hsum'⟩ := a3m_withBot_add_eq_nat hsum
  exact ⟨cu, ct, n, hcu, hct.symm, hn, hsum'⟩

/-- A point of `W = closure {w}` has codimension one in `W` exactly when its codimension in `X` is
one more than that of `w`. -/
theorem a3y_coheight_eq_one_iff (w : X.left) (D : cycleComponent X.left w) :
    coheight D = 1 ↔ coheight (cycleComponentι X.left w D) = coheight w + 1 := by
  have hX := a3m_height_add_coheight X
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (genericPoint X.left)
  have hD := hX (cycleComponentι X.left w D)
  have hw := hX w
  rw [hn] at hD hw
  have hgen : height w = height (genericPoint (cycleComponent X.left w)) :=
    (a3m_height_cycleComponent_genericPoint X.left w).symm
  have hW := a3m_height_add_coheight (a3m_component X w) D
  change height D + coheight D = height (genericPoint (cycleComponent X.left w)) at hW
  rw [← hgen, ← a3m_height_cycleComponentι] at hW
  -- everything is finite
  have fin : ∀ x : ℕ∞, ∀ y : ℕ∞, x + y = (n : ℕ∞) → x ≠ ⊤ ∧ y ≠ ⊤ := fun x y hxy => by
    constructor <;> intro htop <;> simp [htop] at hxy
  obtain ⟨h1, h2⟩ := fin _ _ hD
  obtain ⟨h3, h4⟩ := fin _ _ hw
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 h1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 h2
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 h3
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 h4
  rw [← ha, ← hb] at hD
  rw [← hc, ← hd] at hw
  rw [← ha, ← hc] at hW
  have hfinD : coheight D ≠ ⊤ := by
    intro htop; rw [htop, add_top] at hW; exact ENat.top_ne_natCast c hW
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 hfinD
  rw [← he] at hW ⊢
  rw [← hb, ← hd]
  have hD' : a + b = n := by exact_mod_cast hD
  have hw' : c + d = n := by exact_mod_cast hw
  have hW' : a + e = c := by exact_mod_cast hW
  constructor
  · intro h1
    have : e = 1 := by exact_mod_cast h1
    norm_cast; omega
  · intro h1
    have : b = d + 1 := by exact_mod_cast h1
    norm_cast; omega

omit [IsIntegral X.left] in
/-- Serre's multiplicity along a component `Z` through `T`, read in `𝒪_{X,T}` as an alternating sum
of localized lengths, truncated at any `m` at least the codimension of `Z`. -/
theorem a3y_serreMult_comp [Smooth X.hom] [IsIntegral X.left] {T z w v : X.left} (h : z ⤳ T)
    (hw : w ⤳ z) (hv : v ⤳ z) (m : ℕ) (hm : coheight z ≤ m) :
    (a3i_serreMult X.left z w v : ℤ) = ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      ((a3e_locLen ⟨a3i_stalkIdeal X.left T z, a3q_stalkIdeal_isPrime X.left h⟩
        (((Tor (ModuleCat.{0} (X.left.presheaf.stalk T)) i).obj
          (ModuleCat.of _ (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w))).obj
          (ModuleCat.of _ (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T v)))).toNat : ℤ) := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hreg := a3c_isRegularLocalRing_stalk X z
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 (a3c_coheight_ne_top X.left z)
  have hcm : c ≤ m := by rw [← hc] at hm; exact_mod_cast hm
  unfold a3i_serreMult
  rw [← hc, ENat.toNat_natCast]
  simp only [a3q_length_torModule X.left h hw hv]
  have hz : ∀ i, c < i → a3e_locLen ⟨a3i_stalkIdeal X.left T z, a3q_stalkIdeal_isPrime X.left h⟩
      (((Tor (ModuleCat.{0} (X.left.presheaf.stalk T)) i).obj
          (ModuleCat.of _ (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w))).obj
          (ModuleCat.of _ (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T v))) = 0 := by
    intro i hi
    rw [← a3q_length_torModule X.left h hw hv]
    have hdim : ringKrullDim (X.left.presheaf.stalk z) < i := by
      rw [ringKrullDim_stalk_eq_coheight, ← hc]
      exact_mod_cast hi
    have : Module.Finite (X.left.presheaf.stalk z)
        (ModuleCat.of (X.left.presheaf.stalk z)
          (X.left.presheaf.stalk z ⧸ a3i_stalkIdeal X.left z v)) :=
      (inferInstance : Module.Finite (X.left.presheaf.stalk z)
        (X.left.presheaf.stalk z ⧸ a3i_stalkIdeal X.left z v))
    exact Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (a3e_isZero_tor_regular _ _ i hdim))
  clear hm
  induction m, hcm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [Finset.sum_range_succ (n := n + 1), ← ih, hz (n + 1) (by omega)]
    simp

end dims

/-- The primes `𝔇 ⊇ P + (a)` with `dim A/𝔇 = dim A/P - 1` form a finite set. -/
theorem a3y_exists_F {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : Ideal A)
    [P.IsPrime] (a : A) (ha : a ∉ P)
    (hfin : ∀ 𝔮 : PrimeSpectrum A, ∃ n : ℕ, ringKrullDim (A ⧸ 𝔮.asIdeal) = n) :
    ∃ F : Finset (PrimeSpectrum A), ∀ 𝔇 : PrimeSpectrum A, 𝔇 ∈ F ↔
      (P ≤ 𝔇.asIdeal ∧ a ∈ 𝔇.asIdeal ∧ ringKrullDim (A ⧸ 𝔇.asIdeal) + 1 = ringKrullDim (A ⧸ P)) := by
  set S := {𝔇 : PrimeSpectrum A | P ≤ 𝔇.asIdeal ∧ a ∈ 𝔇.asIdeal ∧
    ringKrullDim (A ⧸ 𝔇.asIdeal) + 1 = ringKrullDim (A ⧸ P)}
  have hS : S.Finite := by
    refine ((P ⊔ Ideal.span {a}).finite_minimalPrimes_of_isNoetherianRing.preimage
      (fun x _ y _ h => PrimeSpectrum.ext h)).subset ?_
    rintro 𝔇 ⟨hP, ha𝔇, hd⟩
    refine ⟨⟨𝔇.isPrime, sup_le hP ((Ideal.span_singleton_le_iff_mem _).2 ha𝔇)⟩, fun 𝔮 h𝔮 hle => ?_⟩
    obtain ⟨h𝔮p, h𝔮⟩ := h𝔮
    by_contra hne
    have hlt : 𝔮 < 𝔇.asIdeal := lt_of_le_of_ne hle fun h => hne (h ▸ le_rfl)
    have h1 := a3s_ringKrullDim_quotient_add_one_le hlt
    have hP𝔮 : P < 𝔮 := lt_of_le_of_ne (le_sup_left.trans h𝔮) fun h =>
      ha (h ▸ (le_sup_right.trans h𝔮) (Ideal.mem_span_singleton_self a))
    have h2 := a3s_ringKrullDim_quotient_add_one_le hP𝔮
    obtain ⟨n₁, hn₁⟩ := hfin 𝔇
    obtain ⟨n₂, hn₂⟩ := hfin ⟨𝔮, h𝔮p⟩
    change ringKrullDim (A ⧸ 𝔮) = n₂ at hn₂
    rw [hn₁, hn₂] at h1
    rw [hn₂, ← hd, hn₁] at h2
    have h1' : n₁ + 1 ≤ n₂ := by exact_mod_cast h1
    have h2' : n₂ + 1 ≤ n₁ + 1 := by exact_mod_cast h2
    omega
  exact ⟨hS.toFinset, fun 𝔇 => hS.mem_toFinset⟩

section principalAt
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsNoetherian X.left]
  (w v : X.left)

/-- The point of `Spec 𝒪_{X,T}` of a generization of `T`, and the closed point otherwise. -/
def a3y_ptOr (T z : X.left) : PrimeSpectrum (X.left.presheaf.stalk T) := by
  classical
  exact if h : z ⤳ T then a3y_pt T z h else closedPoint _

/-- The components of `closure {w} ∩ closure {v}` through `T`. -/
def a3y_compsAt (T : X.left) : Finset X.left := by
  classical
  exact (a3y_comps_finite w v).toFinset.filter (· ⤳ T)

/-- The cycle form of the local identity at one point `T` and one function `a`: if the components
of `W ∩ V` through `T` have the expected codimension, `T` has codimension one more, and
`a ∈ 𝒪_{X,T}` vanishes neither on `W` nor on the components through `T`, then
`Σ_D ord_D(a|_W) · i(T; D · V) = Σ_Z i(Z; W · V) · ord_T(a|_Z)`. -/
theorem a3y_principal_at (T : X.left) (hwT : w ⤳ T) (hvT : v ⤳ T)
    (hloc : ∀ z ∈ a3y_comps w v, z ⤳ T → coheight z = coheight w + coheight v)
    (hT : coheight T = coheight w + coheight v + 1)
    (a : X.left.presheaf.stalk T) (ha : a ∉ a3i_stalkIdeal X.left T w)
    (haZ : ∀ z ∈ a3y_compsAt X w v T, a ∉ a3i_stalkIdeal X.left T z)
    (F : Finset (PrimeSpectrum (X.left.presheaf.stalk T)))
    (hF : ∀ 𝔇 : PrimeSpectrum (X.left.presheaf.stalk T), 𝔇 ∈ F ↔
      (a3i_stalkIdeal X.left T w ≤ 𝔇.asIdeal ∧ a ∈ 𝔇.asIdeal ∧
        ringKrullDim (X.left.presheaf.stalk T ⧸ 𝔇.asIdeal) + 1 =
          ringKrullDim (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w)))
    (m : ℕ) (hm : coheight T ≤ m) :
    ∑ 𝔇 ∈ F, ((a3e_locLen 𝔇 (QuotSMulTop a (X.left.presheaf.stalk T ⧸
        a3i_stalkIdeal X.left T w))).toNat : ℤ) *
        a3s_chi m (ModuleCat.of (X.left.presheaf.stalk T) (X.left.presheaf.stalk T ⧸ 𝔇.asIdeal))
          (ModuleCat.of (X.left.presheaf.stalk T)
            (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T v)) =
      ∑ z ∈ a3y_compsAt X w v T, (a3i_serreMult X.left z w v : ℤ) *
        a3e_herbrand a (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T z) := by
  classical
  have : IsLocallyNoetherian X.left := inferInstance
  have hP := a3q_stalkIdeal_isPrime X.left hwT
  have hQ := a3q_stalkIdeal_isPrime X.left hvT
  have hmem : ∀ z ∈ a3y_compsAt X w v T, z ∈ a3y_comps w v ∧ z ⤳ T := fun z hz => by
    simp only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset] at hz
    exact hz
  have hpt : ∀ z (h : z ⤳ T), a3y_ptOr X T z = a3y_pt T z h := fun z h => by
    simp [a3y_ptOr, h]
  -- the components through `T` as primes
  set Φ := (a3y_compsAt X w v T).image (a3y_ptOr X T)
  have hinj : Set.InjOn (a3y_ptOr X T) (a3y_compsAt X w v T) := by
    intro z hz z' hz' he
    rw [hpt z (hmem z hz).2, hpt z' (hmem z' hz').2] at he
    exact a3y_pt_injective T z z' _ _ he
  have hcohz : ∀ z ∈ a3y_compsAt X w v T, coheight z = coheight w + coheight v := fun z hz =>
    hloc z (hmem z hz).1 (hmem z hz).2
  have hzT : ∀ z ∈ a3y_compsAt X w v T, z ≠ T := fun z hz he => by
    have := hcohz z hz
    rw [he, hT] at this
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 (a3c_coheight_ne_top X.left w)
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 (a3c_coheight_ne_top X.left v)
    rw [← hc, ← hd] at this
    norm_cast at this
    omega
  have hgood := fun q (hw : w ⤳ q) (hv : v ⤳ q) (hq : q ⤳ T) => a3y_good w v hloc hT hw hv hq
  have hPpt : a3i_stalkIdeal X.left T w = (a3y_pt T w hwT).asIdeal := rfl
  have hQpt : a3i_stalkIdeal X.left T v = (a3y_pt T v hvT).asIdeal := rfl
  have hspec : ∀ 𝔮 : PrimeSpectrum (X.left.presheaf.stalk T), ∀ u (hu : u ⤳ T),
      (a3y_pt T u hu).asIdeal ≤ 𝔮.asIdeal → u ⤳ X.left.fromSpecStalk T 𝔮 := by
    intro 𝔮 u hu hle
    rw [← a3y_pt_le_iff T u _ hu (a3y_specializes_fromSpecStalk T 𝔮), a3y_pt_fromSpecStalk]
    exact hle
  have hΦm : ∀ Z ∈ Φ, Z ≠ closedPoint (X.left.presheaf.stalk T) := by
    intro Z hZ hcl
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hZ
    rw [hpt z (hmem z hz).2, ← a3y_pt_self] at hcl
    exact hzT z hz (a3y_pt_injective T z T _ _ hcl)
  have hΦdim : ∀ Z ∈ Φ, ∀ 𝔮 : PrimeSpectrum (X.left.presheaf.stalk T), Z < 𝔮 →
      𝔮 = closedPoint (X.left.presheaf.stalk T) := by
    intro Z hZ 𝔮 hlt
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hZ
    rw [hpt z (hmem z hz).2] at hlt
    set q := X.left.fromSpecStalk T 𝔮
    have hqT : q ⤳ T := a3y_specializes_fromSpecStalk T 𝔮
    have hzq : z ⤳ q := hspec 𝔮 z (hmem z hz).2 hlt.le
    have hzq' : z ≠ q := by
      intro he
      apply hlt.ne
      rw [← a3y_pt_fromSpecStalk T 𝔮]
      apply PrimeSpectrum.ext
      change a3i_stalkIdeal X.left T z = a3i_stalkIdeal X.left T q
      rw [he]
    obtain ⟨hwz, hvz, -⟩ := a3y_comps_spec w v (hmem z hz).1
    rcases hgood q (hwz.trans hzq) (hvz.trans hzq) hqT with hq | hq
    · rw [← a3y_pt_fromSpecStalk T 𝔮]
      have : a3y_pt T q (a3y_specializes_fromSpecStalk T 𝔮) = a3y_pt T T (specializes_refl T) :=
        PrimeSpectrum.ext (by change a3i_stalkIdeal X.left T q = a3i_stalkIdeal X.left T T; rw [hq])
      rw [this, a3y_pt_self]
    · exfalso
      have h1 := a3y_coheight_lt hzq hzq'
      rw [hloc q hq hqT, hloc z (hmem z hz).1 (hmem z hz).2] at h1
      exact lt_irrefl _ h1
  have hΦa : ∀ Z ∈ Φ, a ∉ Z.asIdeal := by
    intro Z hZ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hZ
    rw [hpt z (hmem z hz).2]
    exact haZ z hz
  have hPQ : ∀ 𝔮 : PrimeSpectrum (X.left.presheaf.stalk T),
      a3i_stalkIdeal X.left T w ≤ 𝔮.asIdeal → a3i_stalkIdeal X.left T v ≤ 𝔮.asIdeal →
        𝔮 = closedPoint (X.left.presheaf.stalk T) ∨ 𝔮 ∈ Φ := by
    intro 𝔮 h1 h2
    set q := X.left.fromSpecStalk T 𝔮
    have hqT : q ⤳ T := a3y_specializes_fromSpecStalk T 𝔮
    rcases hgood q (hspec 𝔮 w hwT h1) (hspec 𝔮 v hvT h2) hqT with hq | hq
    · left
      rw [← a3y_pt_fromSpecStalk T 𝔮]
      have : a3y_pt T q (a3y_specializes_fromSpecStalk T 𝔮) = a3y_pt T T (specializes_refl T) :=
        PrimeSpectrum.ext (by change a3i_stalkIdeal X.left T q = a3i_stalkIdeal X.left T T; rw [hq])
      rw [this, a3y_pt_self]
    · right
      have hqc : q ∈ a3y_compsAt X w v T := by
        simp only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hq, hqT⟩
      refine Finset.mem_image.2 ⟨q, hqc, ?_⟩
      rw [hpt q hqT, a3y_pt_fromSpecStalk]
  have hprop : ringKrullDim (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w) +
      ringKrullDim (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T v) =
        ringKrullDim (X.left.presheaf.stalk T) + 1 := by
    obtain ⟨cw, ct, nw, hcw, hct, hnw, hw'⟩ := a3y_dims X hwT
    obtain ⟨cv, ct', nv, hcv, hct', hnv, hv'⟩ := a3y_dims X hvT
    rw [hnw, hnv, ringKrullDim_stalk_eq_coheight, hct]
    rw [hct, hcw, hcv] at hT
    rw [hct] at hct'
    have h1 : ct = cw + cv + 1 := by exact_mod_cast hT
    have h2 : ct' = ct := by exact_mod_cast hct'.symm
    norm_cast
    omega
  have hm' : ringKrullDim (X.left.presheaf.stalk T) ≤ m := by
    rw [ringKrullDim_stalk_eq_coheight]; exact_mod_cast hm
  have key := a3w_principal_stalk X T _ _ a ha Φ hΦm hΦdim hΦa hPQ hprop F hF m hm'
  rw [key, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [hpt z (hmem z hz).2]
  obtain ⟨hwz, hvz, -⟩ := a3y_comps_spec w v (hmem z hz).1
  have hzm : coheight z ≤ m :=
    (Order.coheight_anti (Scheme.le_iff_specializes.2 (hmem z hz).2)).trans hm
  rw [a3y_serreMult_comp X (hmem z hz).2 hwz hvz m hzm]
  rfl

end principalAt

end HodgeLean.Adapters
