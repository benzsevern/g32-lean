import HodgeLean.Adapters.KleimanCoheightAlgebra
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension

/-!
# Pointwise dimension formulas on schemes of finite type

For step 8 of the Kleiman route, the coheight of an intersection component is computed from its
height in the product of the two component closures. This file turns affine charts satisfying
`ht P + dim R/P = n` into the pointwise formula `height y + coheight y = n`, applies it to products
of integral schemes of finite type over an algebraically closed field, and computes the coheight of
a point that is generic in its fibre under a flat morphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order TensorProduct IsLocalRing

namespace HodgeLean.Adapters

/-- In a preorder, the height of `y` is bounded once every chain below `y` lies in an upper set
in which `y` has bounded height.
Source: `Order.height_le_iff'`. -/
theorem hc9k8_height_le_of_upperSets {α : Type*} [Preorder α] (y : α) (N : ℕ∞)
    (h : ∀ z ≤ y, ∃ U : Set α, IsUpperSet U ∧ z ∈ U ∧
      ∀ hy : y ∈ U, height (⟨y, hy⟩ : U) ≤ N) : height y ≤ N := by
  refine height_le_iff'.mpr fun p hp => ?_
  obtain ⟨U, hU, hz, hN⟩ := h p.head (hp ▸ p.monotone (Fin.zero_le _))
  have hmem : ∀ i, p i ∈ U := fun i => hU (p.monotone (Fin.zero_le i)) hz
  let q : LTSeries U :=
    { length := p.length
      toFun := fun i => ⟨p i, hmem i⟩
      step := fun i => p.step i }
  have hy : y ∈ U := hp ▸ hmem (Fin.last _)
  have hq : q.last = ⟨y, hy⟩ := Subtype.ext hp
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ height (⟨y, hy⟩ : U) := hq ▸ length_le_height_last
    _ ≤ N := hN hy

/-- The height of a point of a subset is at most its height in the ambient preorder.
Source: `Order.height_le_height_apply_of_strictMono`. -/
theorem hc9k8_height_subtype_le {α : Type*} [Preorder α] (U : Set α) (y : U) :
    height y ≤ height (y : α) :=
  height_le_height_apply_of_strictMono (Subtype.val : U → α) (fun _ _ h => h) y

/-- In an affine scheme, the height of a point is the dimension of the quotient by its prime.
Source: `specOrderIsoPrimeSpectrum` and `ringKrullDim_quotient`. -/
theorem hc9k8_height_spec (R : CommRingCat) (p : Spec R) :
    (height p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
  let q : PrimeSpectrum R := p
  have h1 : height p = coheight q := by
    rw [← height_orderIso (specOrderIsoPrimeSpectrum R) p]; rfl
  have h2 : (Set.Ici q) = PrimeSpectrum.zeroLocus (R := R) q.asIdeal := by
    ext x; rfl
  rw [h1, ringKrullDim_quotient, coheight_eq_krullDim_Ici, h2]

/-- An open immersion from an affine scheme is an order isomorphism onto its range.
Source: `Topology.IsInducing.specializes_iff`. -/
noncomputable def hc9k8_rangeOrderIso {Y : Scheme} {R : CommRingCat} (f : Spec R ⟶ Y)
    [IsOpenImmersion f] : Spec R ≃o Set.range f.base where
  toEquiv := Equiv.ofInjective f.base f.isOpenEmbedding.injective
  map_rel_iff' {a b} := by
    change f.base a ≤ f.base b ↔ a ≤ b
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact f.isOpenEmbedding.isInducing.specializes_iff

example {Y : Scheme} {R : CommRingCat} (f : Spec R ⟶ Y) [IsOpenImmersion f] :
    Spec R ≃o Set.range f.base :=
  hc9k8_rangeOrderIso f

/-- Open sets of a scheme are upper sets of the specialization order.
Source: `Specializes.mem_open`. -/
theorem hc9k8_isUpperSet_of_isOpen {Y : Scheme} (U : Set Y) (hU : IsOpen U) : IsUpperSet U :=
  fun _ _ hab ha => (Scheme.le_iff_specializes.mp hab).mem_open hU ha

/-- At a point of an affine chart satisfying the dimension formula, coheight plus chart height is
the chart dimension.
Source: `idealHeight_eq_coheight` and `coheight_eq_of_isOpenImmersion`. -/
theorem hc9k8_coheight_add_height_chart {Y : Scheme} {R : CommRingCat} (f : Spec R ⟶ Y)
    [IsOpenImmersion f] (n : ℕ)
    (hR : ∀ P : Ideal R, P.IsPrime → (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) = n)
    (p : Spec R) : coheight (f.base p) + height p = n := by
  have h := hR p.asIdeal p.isPrime
  rw [← hc9k8_height_spec, idealHeight_eq_coheight, ← coheight_eq_of_isOpenImmersion f] at h
  exact_mod_cast h

/-- A scheme covered by affine charts satisfying the dimension formula `ht P + dim R/P = n`
satisfies `height y + coheight y = n` at every point.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.20. -/
theorem hc9k8_height_add_coheight_of_charts (Y : Scheme) (n : ℕ)
    (h : ∀ y : Y, ∃ (R : CommRingCat) (f : Spec R ⟶ Y), IsOpenImmersion f ∧
      y ∈ Set.range f.base ∧
      ∀ P : Ideal R, P.IsPrime → (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) = n)
    (y : Y) : height y + coheight y = n := by
  obtain ⟨R, f, hf, ⟨p, rfl⟩, hR⟩ := h y
  have hp := hc9k8_coheight_add_height_chart f n hR p
  have hfin : coheight (f.base p) ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at hp
    exact ENat.top_ne_natCast n hp
  have hle : height (f.base p) ≤ height p := by
    refine hc9k8_height_le_of_upperSets _ _ fun z _ => ?_
    obtain ⟨R', f', hf', ⟨p', rfl⟩, hR'⟩ := h z
    refine ⟨Set.range f'.base, hc9k8_isUpperSet_of_isOpen _ f'.isOpenEmbedding.isOpen_range,
      ⟨p', rfl⟩, fun hy => ?_⟩
    obtain ⟨q, hq⟩ := hy
    have e : (⟨f.base p, ⟨q, hq⟩⟩ : Set.range f'.base) = hc9k8_rangeOrderIso f' q :=
      Subtype.ext hq.symm
    rw [e, height_orderIso]
    have hq' := hc9k8_coheight_add_height_chart f' n hR' q
    rw [hq] at hq'
    rw [← hp] at hq'
    exact (WithTop.add_left_cancel hfin hq').le
  have hge : height p ≤ height (f.base p) := by
    have e : (⟨f.base p, ⟨p, rfl⟩⟩ : Set.range f.base) = hc9k8_rangeOrderIso f p := rfl
    calc height p = height (hc9k8_rangeOrderIso f p) := (height_orderIso _ _).symm
      _ ≤ _ := hc9k8_height_subtype_le _ _
  rw [le_antisymm hle hge, add_comm]
  exact hp

set_option maxHeartbeats 400000 in
/-- The product of two integral schemes of finite type over an algebraically closed field, whose
nonempty affine opens have dimensions `m` and `n`, satisfies `height u + coheight u = m + n`.
Source: Hartshorne, *Algebraic Geometry*, Exercises II.3.15 and II.3.20. -/
theorem hc9k8_pullback_height_add_coheight {k : Type} [Field k] [IsAlgClosed k]
    {Z W : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of k)) (g : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsIntegral Z] [AlgebraicGeometry.IsIntegral W] [LocallyOfFiniteType f] [LocallyOfFiniteType g] (m n : ℕ)
    (hZ : ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → ringKrullDim Γ(Z, U) = m)
    (hW : ∀ V : W.Opens, IsAffineOpen V → (V : Set W).Nonempty → ringKrullDim Γ(W, V) = n)
    (u : ↥(pullback f g)) : height u + coheight u = (m + n : ℕ) := by
  refine hc9k8_height_add_coheight_of_charts _ (m + n) (fun u => ?_) u
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.fst f g u ∈ (⊤ : Z.Opens) from trivial)
  obtain ⟨V, hV, hwV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.snd f g u ∈ (⊤ : W.Opens) from trivial)
  have : Nonempty U := ⟨⟨_, hzU⟩⟩
  have : Nonempty V := ⟨⟨_, hwV⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hV.fromSpec ≫ g)
  let R := Γ(Z, U)
  let T := Γ(W, V)
  let : Algebra k R := φ.hom.toAlgebra
  let : Algebra k T := ψ.hom.toAlgebra
  have : Algebra.FiniteType k R := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  have : Algebra.FiniteType k T := by
    have : LocallyOfFiniteType (Spec.map ψ) := hψ ▸ inferInstance
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  have : IsDomain (R ⊗[k] T) := hc9k8_isDomain_tensorProduct
  have : Algebra.FiniteType k (R ⊗[k] T) := Algebra.FiniteType.trans (S := R) inferInstance
    inferInstance
  have hdim : ringKrullDim (R ⊗[k] T) = (m + n : ℕ) := by
    rw [hc9k8_ringKrullDim_tensorProduct, hZ U hU ⟨_, hzU⟩, hW V hV ⟨_, hwV⟩]
    norm_cast
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫ 𝟙 _ = hU.fromSpec ≫ f := by
    rw [Category.comp_id, ← hφ]; rfl
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap k T)) ≫ 𝟙 _ = hV.fromSpec ≫ g := by
    rw [Category.comp_id, ← hψ]; rfl
  let c : Spec (CommRingCat.of (R ⊗[k] T)) ⟶ pullback f g :=
    (pullbackSpecIso k R T).inv ≫ pullback.map _ _ f g hU.fromSpec hV.fromSpec (𝟙 _) e₁ e₂
  refine ⟨CommRingCat.of (R ⊗[k] T), c, inferInstance, ?_, fun P hP => ?_⟩
  · have hr : Set.range c.base = Set.range (pullback.map _ _ f g hU.fromSpec hV.fromSpec
        (𝟙 _) e₁ e₂).base := by
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, (Scheme.Hom.comp_apply _ _ a).symm⟩
      · rintro ⟨b, rfl⟩
        refine ⟨(pullbackSpecIso k R T).hom b, ?_⟩
        rw [← Scheme.Hom.comp_apply]
        simp [c]
    rw [hr, Scheme.Pullback.range_map]
    exact ⟨by rw [hU.range_fromSpec]; exact hzU, by rw [hV.range_fromSpec]; exact hwV⟩
  · rw [← hdim]
    exact hc9k8_height_add_ringKrullDim_quotient (k := k) P

/-- On an integral scheme of finite type over a field whose closed points all have coheight `c`,
every nonempty affine open has coordinate ring of Krull dimension `c`.
Source: Jacobson property of finite-type schemes and
`Algebra.FiniteType.height_eq_ringKrullDim_of_isMaximal`. -/
theorem hc9k8_ringKrullDim_affineOpen {k : Type} [Field k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsIntegral Y] [LocallyOfFiniteType f]
    (c : ℕ) (hc : ∀ y : Y, IsClosed ({y} : Set Y) → coheight y = c)
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set Y).Nonempty) :
    ringKrullDim Γ(Y, U) = c := by
  have : Nonempty U := ⟨⟨_, hne.some_mem⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  let : Algebra k Γ(Y, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(Y, U)
  have hht := Algebra.FiniteType.height_eq_ringKrullDim_of_isMaximal (k := k) m
  let p : Spec Γ(Y, U) := ⟨m, hm.isPrime⟩
  have hp : IsClosed ({p} : Set (Spec Γ(Y, U))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hm
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  have hy : IsClosed ({hU.fromSpec p} : Set Y) := by
    have h := hU.fromSpec.isOpenEmbedding.preimage_closedPoints
    have hp' : p ∈ closedPoints (Spec Γ(Y, U)) := hp
    rw [← h] at hp'
    exact hp'
  have h1 : coheight (hU.fromSpec p) = m.height := by
    rw [coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  rw [← hht, ← h1, hc _ hy]
  rfl

set_option maxHeartbeats 400000 in
/-- For a flat morphism, a point that is maximal in its fibre for the specialization order has
the coheight of its image.
Source: Matsumura, *Commutative Ring Theory*, Theorem 15.1; Stacks Project, Tag 00ON. -/
theorem hc9k8_coheight_eq_of_flat {A Y : Scheme} (φ : A ⟶ Y) [Flat φ] [IsLocallyNoetherian A]
    [IsLocallyNoetherian Y]
    (u : A) (hmin : ∀ v : A, φ v = φ u → v ⤳ u → v = u) :
    coheight u = coheight (φ u) := by
  let R := Y.presheaf.stalk (φ u)
  let S := A.presheaf.stalk u
  let h := φ.stalkMap u
  let : Algebra R S := h.hom.toAlgebra
  have : Module.Flat R S := Flat.stalkMap φ u
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom h.hom)
  let p := maximalIdeal R
  let P := maximalIdeal S
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have hfib : (P.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).height = 0 := by
    let J := p.map (algebraMap R S)
    have hJP : J ≤ P := Ideal.map_le_iff_le_comap.mpr (le_of_eq (Ideal.LiesOver.over))
    have hmP : P ∈ J.minimalPrimes := by
      refine ⟨⟨inferInstance, hJP⟩, fun Q ⟨hQ, hJQ⟩ hQP => ?_⟩
      let q : Spec S := ⟨Q, hQ⟩
      let v := A.fromSpecStalk u q
      have hv1 : v ⤳ u :=
        ((IsLocalRing.specializes_closedPoint q).map (A.fromSpecStalk u).continuous).trans
          (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
      have hq : Spec.map h q = closedPoint R := by
        apply PrimeSpectrum.ext
        change Ideal.comap h.hom Q = maximalIdeal R
        have hle : maximalIdeal R ≤ Ideal.comap h.hom Q :=
          Ideal.map_le_iff_le_comap.mp hJQ
        exact ((maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.comap h.hom).ne_top hle).symm
      have hv2 : φ v = φ u := by
        have e := congrArg (fun g => g q) (Scheme.SpecMap_stalkMap_fromSpecStalk φ (x := u))
        simp only [Scheme.Hom.comp_apply] at e
        change φ (A.fromSpecStalk u q) = φ u
        rw [← e]
        change Y.fromSpecStalk (φ u) (Spec.map h q) = φ u
        rw [hq, Scheme.fromSpecStalk_closedPoint]
      have hvu := hmin v hv2 hv1
      have hqc : q = closedPoint S := (A.fromSpecStalk u).isEmbedding.injective
        (hvu.trans Scheme.fromSpecStalk_closedPoint.symm)
      have : Q = P := congrArg PrimeSpectrum.asIdeal hqc
      exact this.symm.le
    rw [Ideal.minimalPrimes_eq_comap] at hmP
    obtain ⟨Q', hQ', hQ'P⟩ := hmP
    rw [← hQ'P, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have : Q'.IsPrime := hQ'.1.1
    exact Ideal.height_eq_zero_iff.mpr hQ'
  have hP : (P.height : WithBot ℕ∞) = coheight u := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight]
  have hp : (p.height : WithBot ℕ∞) = coheight (φ u) := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight]
  rw [hfib, add_zero] at key
  have := hP.symm.trans ((congrArg _ key).trans hp)
  exact_mod_cast this

end HodgeLean.Adapters
