import HodgeLean.Adapters.KleimanCoheightCharts
import HodgeLean.Adapters.KleimanTransverseDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Expected coheight of a general translated intersection

This is step 8 of the Kleiman route. The difference map on the product of two component closures
is flat over a dense Zariski open of the group. Over that open, the generic point of each fibre
component has the coheight of a closed point in the product, so its height is
`dim Z + dim W - dim X`, and the translated intersection component has coheight
`coheight x + coheight y` in `X`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order

namespace HodgeLean.Adapters

/-- An embedding of schemes with closed range preserves the height of every point.
Source: `Order.height_eq_of_strictMono` and `Topology.IsInducing.specializes_iff`. -/
theorem hc9k8_height_eq_of_isEmbedding {P Q : Scheme} (j : P ⟶ Q)
    (hj : Topology.IsEmbedding j) (hc : IsClosed (Set.range j)) (p : P) :
    height (j p) = height p := by
  have hle : ∀ a b : P, j a ≤ j b ↔ a ≤ b := fun a b => by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact hj.isInducing.specializes_iff
  have hlt : ∀ a b : P, j a < j b ↔ a < b := fun a b => by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hle, hle]
  have hmono : StrictMono (j : P → Q) := fun a b hab => (hlt a b).mpr hab
  refine (height_eq_of_strictMono _ hmono (fun a b hb => ?_) p).symm
  have hspec : j a ⤳ b := Scheme.le_iff_specializes.mp hb.le
  obtain ⟨a', rfl⟩ : b ∈ Set.range j :=
    hc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨a, rfl⟩)
      (specializes_iff_mem_closure.mp hspec)
  exact ⟨a', (hlt a' a).mp hb, rfl⟩

/-- An integral scheme of finite type over a field whose nonempty affine opens all have Krull
dimension `n` satisfies `height y + coheight y = n`.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.20. -/
theorem hc9k8_height_add_coheight_of_integral {k : Type} [Field k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsIntegral Y] [LocallyOfFiniteType f]
    (n : ℕ) (hY : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      ringKrullDim Γ(Y, U) = n) (y : Y) : height y + coheight y = n := by
  refine hc9k8_height_add_coheight_of_charts _ n (fun y => ?_) y
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : Nonempty U := ⟨⟨_, hyU⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  let : Algebra k Γ(Y, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  refine ⟨Γ(Y, U), hU.fromSpec, inferInstance, by rw [hU.range_fromSpec]; exact hyU,
    fun P hP => ?_⟩
  rw [← hY U hU ⟨_, hyU⟩]
  exact hc9k8_height_add_ringKrullDim_quotient (k := k) P

set_option maxHeartbeats 400000 in
/-- Over a dense Zariski open of translation parameters, every irreducible component of the
translated intersection has coheight `coheight x + coheight y`, given that each fibre of the
difference map is isomorphic to the translated intersection.

The open set is the generic flatness locus of the difference map. At a generic point of a
fibre component, the flat height formula gives coheight `dim X` in the product of the two
component closures, and the dimension formulas on that product and on `X` turn its height into
the stated coheight.
Source: Kleiman, "The transversality of a general translate", Compositio Math. 28 (1974),
Theorem 2(i); Hartshorne, *Algebraic Geometry*, III.9.5 and Exercise II.3.20. -/
theorem hc9k8_expected_coheight
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (x y : X.left)
    (hiso : ∀ t : ComplexPoint X, Nonempty ((hc9k_actionMap X x y).fiber t.underlying ≅
        (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme)) :
    ∃ V : X.left.Opens, Dense (V : Set X.left) ∧
      ∀ t : ComplexPoint X, t.underlying ∈ V → ∀ w : (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme,
        closure ({w} : Set _) ∈ irreducibleComponents
            (ccm3_primeIdeal X.left x ⊔
              ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subscheme →
          Order.coheight ((ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left (hc9k_translatePoint X t y)).subschemeι w) =
              Order.coheight x + Order.coheight y := by
  obtain ⟨d, hd⟩ := Smooth.exists_smoothOfRelativeDimension X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  -- the pointwise dimension formula on `X`
  have hXcat : ∀ p : X.left, height p + coheight p = d := by
    refine hc9k8_height_add_coheight_of_integral X.hom d (fun U hU hne => ?_)
    exact hc9k8_ringKrullDim_affineOpen X.hom d
      (fun z hz => SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := X.hom) z hz)
      U hU hne
  have hfin : ∀ p : X.left, ∃ a : ℕ, coheight p = a ∧ a ≤ d := by
    intro p
    have h := hXcat p
    have hne : coheight p ≠ ⊤ := fun h' => by
      rw [h', add_top] at h; exact ENat.top_ne_natCast d h
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hne
    refine ⟨a, ha.symm, ?_⟩
    have : (a : ℕ∞) ≤ d := by rw [← h, ← ha]; exact le_add_self
    exact_mod_cast this
  obtain ⟨a, ha, had⟩ := hfin x
  obtain ⟨b, hb, hbd⟩ := hfin y
  -- the two component closures and their product
  let fZ := cycleComponentι X.left x ≫ X.hom
  let fW := cycleComponentι X.left y ≫ X.hom
  have hZdim : ∀ U : (cycleComponent X.left x).Opens, IsAffineOpen U → (U : Set (cycleComponent X.left x)).Nonempty →
      ringKrullDim Γ(cycleComponent X.left x, U) = (d - a : ℕ) := by
    refine fun U hU hne => hc9k8_ringKrullDim_affineOpen fZ (d - a) (fun z hz => ?_) U hU hne
    rw [cycleComponent_closedPoint_coheight_eq_sub (d := d) X x z ha hz, ENat.natCast_sub]
  have hWdim : ∀ U : (cycleComponent X.left y).Opens, IsAffineOpen U → (U : Set (cycleComponent X.left y)).Nonempty →
      ringKrullDim Γ(cycleComponent X.left y, U) = (d - b : ℕ) := by
    refine fun U hU hne => hc9k8_ringKrullDim_affineOpen fW (d - b) (fun z hz => ?_) U hU hne
    rw [cycleComponent_closedPoint_coheight_eq_sub (d := d) X y z hb hz, ENat.natCast_sub]
  let A := (hc9k_actionSource X x y).left
  let eA : A ≅ pullback fZ fW := Over.prodLeftIsoPullback (Over.mk fZ) (Over.mk fW)
  have hAcat : ∀ q : A, height q + coheight q = ((d - a : ℕ) + (d - b : ℕ) : ℕ) := by
    intro q
    have h := hc9k8_pullback_height_add_coheight fZ fW (d - a) (d - b) hZdim hWdim (eA.hom q)
    rwa [hc9k8_height_eq_of_isEmbedding eA.hom eA.hom.isOpenEmbedding.isEmbedding
      (by rw [Set.range_eq_univ.mpr eA.hom.surjective]; exact isClosed_univ),
      coheight_eq_of_isOpenImmersion] at h
  -- the action map is of finite type and quasi-compact
  let φ := hc9k_actionMap X x y
  have hAhom : (hc9k_actionSource X x y).hom = eA.hom ≫ pullback.fst fZ fW ≫ fZ := by
    have h1 := Over.prodLeftIsoPullback_hom_fst (Over.mk fZ) (Over.mk fW)
    rw [← Category.assoc]
    erw [h1]
    exact (Over.w (Limits.prod.fst : hc9k_actionSource X x y ⟶ Over.mk fZ)).symm
  have : LocallyOfFiniteType (hc9k_actionSource X x y).hom := by
    rw [hAhom]; infer_instance
  have : QuasiCompact (hc9k_actionSource X x y).hom := by
    rw [hAhom]; infer_instance
  have hφw : φ ≫ X.hom = (hc9k_actionSource X x y).hom := Over.w _
  have : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ X.hom) := by rw [hφw]; infer_instance
    exact locallyOfFiniteType_of_comp φ X.hom
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace (hc9k_actionSource X x y).hom
  have : QuasiCompact φ := inferInstance
  have : IsLocallyNoetherian A :=
    LocallyOfFiniteType.isLocallyNoetherian (hc9k_actionSource X x y).hom
  obtain ⟨V, hVd, hVflat⟩ := gfs_exists_flat_over_dense_open φ
  refine ⟨V, hVd, fun t ht w hw => ?_⟩
  have htc : IsClosed ({t.underlying} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨t.left, by simp⟩).2
  obtain ⟨e⟩ := hiso t
  let I := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left (hc9k_translatePoint X t y)
  let u' := e.inv w
  have hwu' : e.hom u' = w := by simp [u']
  let u := φ.fiberι t.underlying u'
  have hu : φ u = t.underlying := by
    have h := (φ.range_fiberι t.underlying).le ⟨u', rfl⟩
    exact h
  -- `u` is maximal in its fibre
  have hmin : ∀ v : A, φ v = φ u → v ⤳ u → v = u := by
    intro v hv hvu
    obtain ⟨v', rfl⟩ : v ∈ Set.range (φ.fiberι t.underlying) := by
      rw [φ.range_fiberι]; exact hv.trans hu
    have h1 : v' ⤳ u' := (φ.fiberι t.underlying).isEmbedding.isInducing.specializes_iff.mp hvu
    have h2 : e.hom v' ⤳ w := hwu' ▸ h1.map e.hom.continuous
    have h3 : e.hom v' = w := by
      have hsub : closure ({w} : Set _) ⊆ closure {e.hom v'} :=
        specializes_iff_closure_subset.mp h2
      have heq := hw.2 isIrreducible_singleton.closure hsub
      exact (h2.antisymm (specializes_iff_closure_subset.mpr heq)).eq
    have h5 : v' = u' := by
      change v' = e.inv w
      rw [← h3]
      simp
    rw [h5]
  -- the coheight of `u` is that of the closed point `t`
  have hcu : coheight u = d := by
    let U := φ ⁻¹ᵁ V
    have huU : u ∈ U := by
      change φ u ∈ V
      rw [hu]; exact ht
    let ψ := U.ι ≫ φ
    have : Flat ψ := by
      have h : ψ = (φ ∣_ V) ≫ V.ι := (morphismRestrict_ι φ V).symm
      rw [h]; infer_instance
    let u0 : U.toScheme := ⟨u, huU⟩
    have h := hc9k8_coheight_eq_of_flat ψ u0 (fun v hv hvu => by
      have h1 : U.ι v = u := hmin (U.ι v) hv (hvu.map U.ι.continuous)
      exact Subtype.ext h1)
    have h2 : coheight (U.ι u0) = coheight u0 := coheight_eq_of_isOpenImmersion U.ι
    have h3 : ψ u0 = t.underlying := hu
    rw [h3, SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed (f := X.hom) (d := d) _ htc,
      ← h2] at h
    exact h
  -- heights along the closed immersion, the isomorphism and the fibre
  have hh1 : height (I.subschemeι w) = height w :=
    hc9k8_height_eq_of_isEmbedding _ I.subschemeι.isClosedEmbedding.isEmbedding
      I.subschemeι.isClosedEmbedding.isClosed_range w
  have hh2 : height w = height u' := by
    rw [← hwu']
    exact hc9k8_height_eq_of_isEmbedding e.hom e.hom.isOpenEmbedding.isEmbedding
      (by rw [Set.range_eq_univ.mpr e.hom.surjective]; exact isClosed_univ) u'
  have hh3 : height u = height u' :=
    hc9k8_height_eq_of_isEmbedding (φ.fiberι t.underlying)
      (φ.fiberι t.underlying).isEmbedding
      (by rw [φ.range_fiberι]; exact htc.preimage φ.continuous) u'
  have hA := hAcat u
  have hX := hXcat (I.subschemeι w)
  rw [hh1, hh2, ← hh3] at hX
  rw [hcu] at hA
  rw [ha, hb]
  have hne : height u ≠ ⊤ := fun h => by
    rw [h, top_add] at hA; exact ENat.top_ne_natCast _ hA
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hne
  have hne2 : coheight (I.subschemeι w) ≠ ⊤ := fun h' => by
    rw [h', add_top] at hX; exact ENat.top_ne_natCast _ hX
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hne2
  rw [← hh] at hA hX
  rw [← hc] at hX ⊢
  norm_cast at hA hX ⊢
  omega

end HodgeLean.Adapters
