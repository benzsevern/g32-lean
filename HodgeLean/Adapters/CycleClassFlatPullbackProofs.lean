import HodgeLean.Adapters.CycleClassFlatPullbackDefs
import HodgeLean.Adapters.CycleClassPullbackCore
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.AlgebraicGeometry.Group.Smooth

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Topology
open MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs
namespace HodgeLean.Adapters

private lemma ccm3_constructible_has_locallyClosed_subset {T : Type*} [TopologicalSpace T]
    {s : Set T} (hs : IsConstructible s) {x : T} (hx : x ∈ s) :
    ∃ t : Set T, x ∈ t ∧ t ⊆ s ∧ IsLocallyClosed t := by
  let P : ∀ s : Set T, IsConstructible s → Prop := fun s _ ↦
    (∀ x ∈ s, ∃ t : Set T, x ∈ t ∧ t ⊆ s ∧ IsLocallyClosed t) ∧
    (∀ x ∈ sᶜ, ∃ t : Set T, x ∈ t ∧ t ⊆ sᶜ ∧ IsLocallyClosed t)
  have hP : P s hs := hs.empty_union_induction
    (p := P)
    (fun U hU _ ↦ ⟨
      (fun x hx ↦ ⟨U, hx, Set.Subset.rfl, hU.isLocallyClosed⟩),
      (fun x hx ↦ ⟨Uᶜ, hx, Set.Subset.rfl, hU.isClosed_compl.isLocallyClosed⟩)⟩)
    (fun a ha b hb hpa hpb ↦ by
      constructor
      · intro x hx
        rcases hx with hx | hx
        · obtain ⟨t, hxt, hta, ht⟩ := hpa.1 x hx
          exact ⟨t, hxt, hta.trans Set.subset_union_left, ht⟩
        · obtain ⟨t, hxt, htb, ht⟩ := hpb.1 x hx
          exact ⟨t, hxt, htb.trans Set.subset_union_right, ht⟩
      · intro x hx
        have hxa : x ∈ aᶜ := by exact fun h ↦ hx (Or.inl h)
        have hxb : x ∈ bᶜ := by exact fun h ↦ hx (Or.inr h)
        obtain ⟨u, hxu, hua, hu⟩ := hpa.2 x hxa
        obtain ⟨v, hxv, hvb, hv⟩ := hpb.2 x hxb
        refine ⟨u ∩ v, ⟨hxu, hxv⟩, ?_, hu.inter hv⟩
        rw [Set.compl_union]
        exact Set.inter_subset_inter hua hvb)
    (fun a ha hpa ↦ by
      constructor
      · exact hpa.2
      · intro x hx
        simpa only [compl_compl] using hpa.1 x (by simpa only [compl_compl] using hx))
  exact hP.1 x hx

/-- Source: Stacks Project, Tags 054K (Chevalley) and 01T9 (Jacobson schemes and finite-type points). -/
theorem ccm3_points_surjective_aux {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (hf : Function.Surjective (Point.map f)) :
    Surjective f.left ∧ IsDominant f.left := by
  haveI : LocallyOfFiniteType (f.left ≫ Z.hom) := f.w ▸ inferInstance
  letI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Z.hom
  letI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  letI : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  letI : IsNoetherian Z.left := { }
  haveI : QuasiCompact (f.left ≫ Z.hom) := f.w ▸ inferInstance
  letI : QuasiCompact f.left := QuasiCompact.of_comp f.left Z.hom
  letI : LocallyOfFinitePresentation f.left := inferInstance
  letI : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  have himage : IsConstructible (Set.range f.left) := by
    rw [← Set.image_univ]
    exact f.left.isConstructible_image IsConstructible.univ
  have hsurj : Function.Surjective f.left := by
    rw [← Set.range_eq_univ]
    apply Set.eq_univ_of_forall
    intro z
    by_contra hz
    have hz' : z ∈ (Set.range f.left)ᶜ := hz
    obtain ⟨t, hzt, ht, htlc⟩ :=
      ccm3_constructible_has_locallyClosed_subset himage.compl hz'
    obtain ⟨z', hz't, hz'closed⟩ :=
      nonempty_inter_closedPoints ⟨z, hzt⟩ htlc
    let pz : ComplexPoint Z :=
      Over.homMk ((pointEquivClosedPoint Z.hom).symm ⟨z', hz'closed⟩).1
        ((pointEquivClosedPoint Z.hom).symm ⟨z', hz'closed⟩).2
    obtain ⟨px, hpx⟩ := hf pz
    have hz'range : z' ∈ Set.range f.left := by
      refine ⟨px.left (IsLocalRing.closedPoint ℂ), ?_⟩
      have hleft : px.left ≫ f.left = pz.left := congrArg Over.Hom.left hpx
      calc
        f.left (px.left (IsLocalRing.closedPoint ℂ)) =
            (px.left ≫ f.left) (IsLocalRing.closedPoint ℂ) := rfl
        _ = pz.left (IsLocalRing.closedPoint ℂ) := by rw [hleft]
        _ = z' := pointOfClosedPoint_apply Z.hom z' hz'closed _
    exact ht hz't hz'range
  letI : Surjective f.left := ⟨hsurj⟩
  exact ⟨inferInstance, inferInstance⟩

/-- Source: Hartshorne, Algebraic Geometry, III.10.7 (generic smoothness), applied on the regular locus of the source; Jacobson closed points on a nonempty open. -/
theorem ccm3_exists_relative_smooth_point_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [IsIntegral Z.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [LocallyOfFinitePresentation f.left] [IsDominant f.left] :
    ∃ p : ComplexPoint X, p.left (IsLocalRing.closedPoint ℂ) ∈ f.left.smoothLocus := by
  have hfg : f.left (genericPoint X.left) = genericPoint Z.left := by
    apply ((genericPoint_spec Z.left).eq _).symm
    convert (genericPoint_spec X.left).image f.left.continuous
    rw [Set.image_univ, f.left.denseRange.closure_range]
  have hgeneric : genericPoint X.left ∈ f.left.smoothLocus := by
    rw [Scheme.Hom.mem_smoothLocus]
    let g : Z.left ⟶ Spec ↧ℂ := Z.hom
    let K' : Type := (Spec ↧ℂ).presheaf.stalk (IsLocalRing.closedPoint ℂ)
    let e : K' ≃+* ℂ :=
      (stalkClosedPointIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    have hb : g (f.left (genericPoint X.left)) = IsLocalRing.closedPoint ℂ :=
      Subsingleton.elim _ _
    let φcat : CommRingCat.of K' ⟶ Z.left.presheaf.stalk (f.left (genericPoint X.left)) := by
      dsimp only [K']
      exact hb ▸ g.stalkMap (f.left (genericPoint X.left))
    let φ : K' →+* Z.left.presheaf.stalk (f.left (genericPoint X.left)) := φcat.hom
    letI : Field K' := (e.isField (Field.toIsField ℂ)).toField
    letI : CharZero K' := charZero_of_injective_ringHom
      (f := e.symm.toRingHom) e.symm.toRingHom.injective
    algebraize [φ]
    letI : Field (Z.left.presheaf.stalk (f.left (genericPoint X.left))) :=
      (isField_stalk_of_closure_mem_irreducibleComponents Z.left _ (by
        rw [hfg]
        simp [irreducibleComponents_eq_singleton])).toField
    letI : CharZero (Z.left.presheaf.stalk (f.left (genericPoint X.left))) :=
      charZero_of_injective_algebraMap (algebraMap K' _).injective
    letI : Field (X.left.presheaf.stalk (genericPoint X.left)) :=
      (isField_stalk_of_closure_mem_irreducibleComponents X.left _ (by
        simp [irreducibleComponents_eq_singleton])).toField
    algebraize [(f.left.stalkMap (genericPoint X.left)).hom]
    letI : Algebra.EssFiniteType
        (Z.left.presheaf.stalk (f.left (genericPoint X.left)))
        (X.left.presheaf.stalk (genericPoint X.left)) := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact LocallyOfFiniteType.stalkMap f.left (genericPoint X.left)
    exact Algebra.FormallySmooth.of_perfectField
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
    ⟨genericPoint X.left, hgeneric⟩ f.left.smoothLocus.2.isLocallyClosed
  let q := (pointEquivClosedPoint X.hom).symm ⟨x, hxc⟩
  let p : ComplexPoint X := Over.homMk q.1 q.2
  refine ⟨p, ?_⟩
  have hp : p.left (IsLocalRing.closedPoint ℂ) = x :=
    pointOfClosedPoint_apply X.hom x hxc _
  rw [hp]
  exact hx

private lemma ccm3_smoothLocus_comp_target_iso {X Y : Scheme}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (e : Y ≅ Y) :
    (f ≫ e.hom).smoothLocus = f.smoothLocus := by
  ext x
  change ((f ≫ e.hom).stalkMap x).hom.FormallySmooth ↔
    (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  change RingHom.FormallySmooth
      ((f.stalkMap x).hom.comp (e.hom.stalkMap (f x)).hom) ↔
    RingHom.FormallySmooth (f.stalkMap x).hom
  rw [RingHom.FormallySmooth.respectsIso.cancel_left_isIso]

private lemma ccm3_mulRight_naturality {X Z : Over (Spec ↧ℂ)}
    [GrpObj X] [GrpObj Z] (f : X ⟶ Z) [IsMonHom f] (p : ComplexPoint X) :
    (GrpObj.mulRight p).hom ≫ f = f ≫ (GrpObj.mulRight (p ≫ f)).hom := by
  dsimp only [GrpObj.mulRight, Iso.trans_hom]
  rw [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc (lift (X := X) (Y := X) (𝟙 X) (toUnit X ≫ p))]
  rw [lift_map]
  rw [← Category.assoc f]
  rw [comp_lift]
  simp [Category.assoc]

/-- Source: Mathlib CategoryTheory.GrpObj.mulRight; Stacks Project, Tag 01V4, smoothness invariant under isomorphisms. -/
theorem ccm3_translation_smoothLocus_aux {X Z : Over (Spec ↧ℂ)}
    [GrpObj X] [GrpObj Z] (f : X ⟶ Z) [IsMonHom f]
    [LocallyOfFinitePresentation f.left] (p : ComplexPoint X) (x : X.left) :
    (GrpObj.mulRight p).hom.left x ∈ f.left.smoothLocus ↔ x ∈ f.left.smoothLocus := by
  let eX := GrpObj.mulRight p
  let eZ := GrpObj.mulRight (p ≫ f)
  have hsquare : eX.hom.left ≫ f.left = f.left ≫ eZ.hom.left := by
    dsimp only [eX, eZ]
    exact congrArg (fun k : X ⟶ Z => k.left) (ccm3_mulRight_naturality f p)
  change eX.hom.left x ∈ f.left.smoothLocus ↔ x ∈ f.left.smoothLocus
  rw [← Scheme.Hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq]
  have hcomp : (eX.hom.left ≫ f.left).smoothLocus = f.left.smoothLocus := by
    rw! [hsquare]
    exact ccm3_smoothLocus_comp_target_iso f.left ((Over.forget _).mapIso eZ)
  rw [hcomp]

/-- Source: Mathlib Scheme.Hom.isOpen_smoothLocus and nonempty_inter_closedPoints; the closed-point test on a Jacobson scheme. -/
theorem ccm3_smooth_of_complex_points_aux {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (f : X ⟶ Z) [LocallyOfFinitePresentation f.left]
    (h : ∀ p : ComplexPoint X, p.left (IsLocalRing.closedPoint ℂ) ∈ f.left.smoothLocus) :
    Smooth f.left := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.left.smoothLocus.2.isClosed_compl.isLocallyClosed
  let p : ComplexPoint X :=
    Over.homMk _ ((pointEquivClosedPoint X.hom).symm ⟨x, hxc⟩).2
  rw [← AlgebraicGeometry.pointOfClosedPoint_apply X.hom x hxc] at hx
  exact hx (h p)

/-- Source: Assembly of ccm3_points_surjective, ccm3_exists_relative_smooth_point, ccm3_translation_smoothLocus and ccm3_smooth_of_complex_points. -/
theorem ccm3_smooth_surjective_group_hom_aux {X Z : Over (Spec ↧ℂ)}
    [GrpObj X] [GrpObj Z] [IsIntegral X.left] [IsIntegral Z.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [IsMonHom f]
    (hf : Function.Surjective (Point.map f)) : Smooth f.left := by
  obtain ⟨hsurj, hdom⟩ := ccm3_points_surjective_aux f hf
  letI : Surjective f.left := hsurj
  letI : IsDominant f.left := hdom
  haveI : LocallyOfFiniteType (f.left ≫ Z.hom) := f.w ▸ inferInstance
  haveI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Z.hom
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  letI : LocallyOfFinitePresentation f.left :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  obtain ⟨p, hp⟩ := ccm3_exists_relative_smooth_point_aux f
  apply ccm3_smooth_of_complex_points_aux f
  intro q
  let e : ComplexPoint X := η[X]
  have he_p : e.left (IsLocalRing.closedPoint ℂ) ∈ f.left.smoothLocus := by
    rw [← ccm3_translation_smoothLocus_aux f p]
    convert hp using 1
    have heq : e ≫ (GrpObj.mulRight p).hom = p := by
      dsimp [e, GrpObj.mulRight]
      rw [comp_lift_assoc]
      simp only [Category.comp_id, comp_toUnit_assoc]
      change (1 : ComplexPoint X) * p = p
      exact one_mul p
    exact congrArg (fun k : ComplexPoint X => k.left (IsLocalRing.closedPoint ℂ)) heq
  have hq := (ccm3_translation_smoothLocus_aux f q
    (e.left (IsLocalRing.closedPoint ℂ))).mpr he_p
  convert hq using 1
  have heq : e ≫ (GrpObj.mulRight q).hom = q := by
    dsimp [e, GrpObj.mulRight]
    rw [comp_lift_assoc]
    simp only [Category.comp_id, comp_toUnit_assoc]
    change (1 : ComplexPoint X) * q = q
    exact one_mul q
  exact (congrArg (fun k : ComplexPoint X => k.left (IsLocalRing.closedPoint ℂ)) heq).symm

/-- Source: ccm3_smooth_surjective_group_hom and ccm2_pwSumMap_surjective_of_ne_zero. -/
theorem ccm3_pwSumMap_smooth_of_ne_zero_aux {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}
    (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Smooth (P.pwSumMap θ a).left := by
  letI : IsMonHom (P.pwSumMap θ a) := spec_g4_isMonHom_sumMap P _
  exact ccm3_smooth_surjective_group_hom_aux (P.pwSumMap θ a)
    (ccm2_pwSumMap_surjective_of_ne_zero_aux P θ a ha)

private theorem ccm3_isArtinianRing_stalk_of_mem_irreducibleComponents
    {Y : Scheme} [IsLocallyNoetherian Y] (y : Y)
    (hy : closure ({y} : Set Y) ∈ irreducibleComponents Y) :
    IsArtinianRing (Y.presheaf.stalk y) := by
  letI : IsNoetherianRing (Y.presheaf.stalk y) := inferInstance
  have hzero : Order.coheight y = 0 := by
    rw [Order.coheight_eq_zero]
    refine fun z hyz ↦ ?_
    have hzy : z ⤳ y := hyz
    show y ⤳ z
    apply specializes_iff_closure_subset.mpr
    have hz : IsIrreducible (closure ({z} : Set Y)) := isIrreducible_singleton.closure
    exact hy.2 hz (specializes_iff_closure_subset.mp hzy)
  letI : Ring.KrullDimLE 0 (Y.presheaf.stalk y) :=
    krullDimLE_of_coheight_le hzero.le
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_genericLength_finite_pos_aux {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    0 < ccm3_genericLength f.left x y ∧ ccm3_genericLength f.left x y < ⊤ := by
  let Y := (ccm3_inverseIdeal f.left x).subscheme
  haveI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (ccm3_inverseIdeal f.left x).subschemeι
  haveI : IsArtinianRing (Y.presheaf.stalk y) :=
    ccm3_isArtinianRing_stalk_of_mem_irreducibleComponents y hy
  exact ⟨Module.length_pos, Module.length_ne_top.lt_top⟩

/-- Source: Mathlib NoetherianSpace.finite_irreducibleComponents; unique generic points of irreducible closed subsets of schemes. -/
theorem ccm3_inverse_components_finite_aux {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    Set.Finite {y : (ccm3_inverseIdeal f.left x).subscheme |
      closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
        irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme} := by
  let Y := (ccm3_inverseIdeal f.left x).subscheme
  haveI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (ccm3_inverseIdeal f.left x).subschemeι
  haveI : CompactSpace X.left :=
    (quasiCompact_iff_compactSpace X.hom).1 inferInstance
  haveI : CompactSpace Y :=
    (quasiCompact_iff_compactSpace (ccm3_inverseIdeal f.left x).subschemeι).1 inferInstance
  letI : IsNoetherian Y :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }
  exact genericPoints.finite
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullbackPrime_coeff_aux {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    ccm3_flatPullbackPrime f.left x ((ccm3_inverseIdeal f.left x).subschemeι y) =
      ((ccm3_genericLength f.left x y).toNat : ℚ) := by
  classical
  let S := {y : (ccm3_inverseIdeal f.left x).subscheme |
    closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme}
  have hS : S.Finite := ccm3_inverse_components_finite_aux f x
  rw [ccm3_flatPullbackPrime, finsum_eq_sum_of_support_subset (s := hS.toFinset)]
  · simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single y]
    · simp only [if_pos hy, Function.locallyFinsuppWithin.single_apply, ↓reduceIte]
    · intro y' hy'S hy'ne
      have hιne : (ccm3_inverseIdeal f.left x).subschemeι y' ≠
          (ccm3_inverseIdeal f.left x).subschemeι y := by
        exact fun h => hy'ne (Subtype.ext h)
      split
      · rw [Function.locallyFinsuppWithin.single_apply, if_neg hιne.symm]
      · rfl
    · intro hyS
      exact (hyS (hS.mem_toFinset.mpr hy)).elim
  · intro y' hy'
    by_contra hy'S
    have hncomp : ¬ closure ({y'} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
        irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme :=
      fun h => hy'S (hS.mem_toFinset.mpr h)
    change (if closure ({y'} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
        irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme then
          Function.locallyFinsuppWithin.single
            ((ccm3_inverseIdeal f.left x).subschemeι y')
            ((ccm3_genericLength f.left x y').toNat : ℚ)
        else 0) ≠ 0 at hy'
    rw [if_neg hncomp] at hy'
    exact hy' rfl

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullbackPrime_support_aux {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (z : X.left) :
    ccm3_flatPullbackPrime f.left x z ≠ 0 ↔
      ∃ y : (ccm3_inverseIdeal f.left x).subscheme,
        (ccm3_inverseIdeal f.left x).subschemeι y = z ∧
        closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
          irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme := by
  classical
  constructor
  · intro hz
    by_contra h
    push_neg at h
    apply hz
    let S := {y : (ccm3_inverseIdeal f.left x).subscheme |
      closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
        irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme}
    have hS : S.Finite := ccm3_inverse_components_finite_aux f x
    rw [ccm3_flatPullbackPrime, finsum_eq_sum_of_support_subset (s := hS.toFinset)]
    · simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro y hyS
      have hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
          irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme :=
        hS.mem_toFinset.mp hyS
      have hne : (ccm3_inverseIdeal f.left x).subschemeι y ≠ z :=
        fun heq => h y heq hy
      rw [if_pos hy, Function.locallyFinsuppWithin.single_apply, if_neg hne.symm]
    · intro y hy
      by_contra hyS
      have hncomp : ¬ closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
          irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme :=
        fun hcomp => hyS (hS.mem_toFinset.mpr hcomp)
      change (if closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
          irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme then
            Function.locallyFinsuppWithin.single
              ((ccm3_inverseIdeal f.left x).subschemeι y)
              ((ccm3_genericLength f.left x y).toNat : ℚ)
          else 0) ≠ 0 at hy
      rw [if_neg hncomp] at hy
      exact hy rfl
  · rintro ⟨y, rfl, hy⟩
    rw [ccm3_flatPullbackPrime_coeff_aux f x y hy]
    have hlen := ccm3_genericLength_finite_pos_aux f x y hy
    exact_mod_cast (ne_of_gt (ENat.toNat_pos (ne_of_gt hlen.1) (ne_of_lt hlen.2)))

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullbackPrime_ne_zero_aux {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [Surjective f.left] (x : Z.left) :
    ccm3_flatPullbackPrime f.left x ≠ 0 := by
  obtain ⟨u, hu⟩ := f.left.surjective x
  have hu_support : u ∈ (ccm3_inverseIdeal f.left x).support := by
    rw [ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap]
    change f.left u ∈ closure ({x} : Set Z.left)
    rw [hu]
    exact subset_closure (Set.mem_singleton x)
  let u' : (ccm3_inverseIdeal f.left x).subscheme := ⟨u, hu_support⟩
  let C : irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme :=
    ⟨irreducibleComponent u', irreducibleComponent_mem_irreducibleComponents u'⟩
  let y : (ccm3_inverseIdeal f.left x).subscheme := (genericPoints.ofComponent C).1
  have hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme :=
    (genericPoints.ofComponent C).2
  have hcoeff := (ccm3_flatPullbackPrime_support_aux f x
    ((ccm3_inverseIdeal f.left x).subschemeι y)).2 ⟨y, rfl, hy⟩
  intro hzero
  apply hcoeff
  exact congrArg (fun c : AlgebraicCycle X.left ℚ =>
    c ((ccm3_inverseIdeal f.left x).subschemeι y)) hzero

attribute [local instance] specializationOrder in
private lemma ccm3_coheight_eq_zero_of_component_generic
    {T : Type*} [TopologicalSpace T] [T0Space T]
    {y : T} (hy : closure ({y} : Set T) ∈ irreducibleComponents T) :
    Order.coheight y = 0 := by
  rw [Order.coheight_eq_zero]
  intro y' hyy'
  have hsub : closure ({y} : Set T) ⊆ closure ({y'} : Set T) := by
    change Specializes y' y at hyy'
    exact closure_minimal (Set.singleton_subset_iff.mpr
      (specializes_iff_mem_closure.mp hyy')) isClosed_closure
  have hrev : closure ({y'} : Set T) ⊆ closure ({y} : Set T) :=
    hy.2 isIrreducible_singleton.closure hsub
  change Specializes y y'
  exact specializes_iff_mem_closure.mpr
    (hrev (subset_closure (Set.mem_singleton y')))

attribute [local instance] specializationOrder in
private lemma ccm3_component_maps_to_point {X Z : Scheme} (f : X ⟶ Z) [Flat f]
    (x : Z) (y : (ccm3_inverseIdeal f x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f x).subscheme) :
    f ((ccm3_inverseIdeal f x).subschemeι y) = x := by
  let I := ccm3_inverseIdeal f x
  have hymax : IsMax y := Order.coheight_eq_zero.mp
    (ccm3_coheight_eq_zero_of_component_generic hy)
  have hzmem : I.subschemeι y ∈ I.support := by
    change I.subschemeι y ∈ (I.support : Set X)
    rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  have hfx : f (I.subschemeι y) ∈ closure ({x} : Set Z) := by
    change I.subschemeι y ∈ ((ccm3_primeIdeal Z x).comap f).support at hzmem
    rw [Scheme.IdealSheafData.support_comap] at hzmem
    change f (I.subschemeι y) ∈ (ccm3_primeIdeal Z x).support at hzmem
    change f (I.subschemeι y) ∈
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({x} : Set Z), isClosed_closure⟩).support : Set Z) at hzmem
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hzmem
    exact hzmem
  obtain ⟨z', hz', hfz'⟩ := (Flat.generalizingMap f)
    (specializes_iff_mem_closure.mpr hfx)
  have hz'mem : z' ∈ I.support := by
    change z' ∈ ((ccm3_primeIdeal Z x).comap f).support
    rw [Scheme.IdealSheafData.support_comap]
    change f z' ∈ (ccm3_primeIdeal Z x).support
    change f z' ∈
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure ({x} : Set Z), isClosed_closure⟩).support : Set Z)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hfz']
    exact subset_closure (Set.mem_singleton x)
  obtain ⟨y', hy'⟩ := (Set.mem_range.mp (I.range_subschemeι.symm.subset hz'mem))
  have hyy' : y ≤ y' := by
    change Specializes y' y
    apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
    simpa only [hy'] using hz'
  have := hymax hyy'
  have heq : y' = y := le_antisymm this hyy'
  simpa only [I, ← hy', heq] using hfz'

attribute [local instance] specializationOrder in
private lemma ccm3_coheight_eq_of_flat_component {X Z : Scheme}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] (f : X ⟶ Z) [Flat f]
    (x : Z) (z : X) (hfx : f z = x)
    (y : (ccm3_inverseIdeal f x).subscheme)
    (hyz : (ccm3_inverseIdeal f x).subschemeι y = z)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f x).subscheme) :
    Order.coheight z = Order.coheight x := by
  subst x
  let R := Z.presheaf.stalk (f z)
  let S := X.presheaf.stalk z
  let φ : R →+* S := (f.stalkMap z).hom
  letI : Algebra R S := φ.toAlgebra
  let p : Ideal R := IsLocalRing.maximalIdeal R
  let P : Ideal S := IsLocalRing.maximalIdeal S
  let P' : Ideal (S ⧸ p.map φ) := P.map (Ideal.Quotient.mk (p.map φ))
  haveI : Module.Flat R S := by
    have hφ : φ.Flat := Flat.stalkMap f z
    simpa only [RingHom.Flat] using hφ
  haveI : P.LiesOver p := ⟨by
    change p = P.comap φ
    exact (congrArg PrimeSpectrum.asIdeal
      (IsLocalRing.comap_closedPoint (f.stalkMap z).hom)).symm⟩
  have hpP : p.map φ ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact (Ideal.LiesOver.over (p := p) (P := P)).le
  haveI : P'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpP
  have hP' : P'.height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
    intro Q hQ hQP'
    haveI : Q.IsPrime := hQ.1
    let Q₀ : Ideal S := Q.comap (Ideal.Quotient.mk (p.map φ))
    haveI : Q₀.IsPrime := by dsimp [Q₀]; infer_instance
    have hpQ₀ : p.map φ ≤ Q₀ := by
      rw [← (p.map φ).mk_ker]
      exact Ideal.ker_le_comap (Ideal.Quotient.mk (p.map φ))
    have hQ₀P : Q₀ ≤ P := by
      simpa [Q₀, P', Ideal.comap_map_quotientMk, hpP] using
        (Ideal.comap_mono (f := Ideal.Quotient.mk (p.map φ)) hQP')
    let w : Spec (CommRingCat.of S) := ⟨Q₀, inferInstance⟩
    let wX : X := X.fromSpecStalk z w
    have hwgen : Specializes wX z := by
      have hw : wX ∈ Set.range (X.fromSpecStalk z) := ⟨w, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hw
      exact hw
    have hcomap : Q₀.comap φ = p := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal_of_isPrime _
      · rw [← Ideal.map_le_iff_le_comap]
        exact hpQ₀
    have hfw : f wX = f z := by
      change (X.fromSpecStalk z ≫ f) w = f z
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
      change Z.fromSpecStalk (f z) (PrimeSpectrum.comap φ w) = f z
      have hwmap : PrimeSpectrum.comap φ w = IsLocalRing.closedPoint R := by
        apply PrimeSpectrum.ext
        exact hcomap
      rw [hwmap, Scheme.fromSpecStalk_closedPoint]
    let I := ccm3_inverseIdeal f (f z)
    have hwmem : wX ∈ I.support := by
      change wX ∈ ((ccm3_primeIdeal Z (f z)).comap f).support
      rw [Scheme.IdealSheafData.support_comap]
      change f wX ∈
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨closure ({f z} : Set Z), isClosed_closure⟩).support : Set Z)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hfw]
      exact subset_closure (Set.mem_singleton (f z))
    obtain ⟨y', hy'⟩ := Set.mem_range.mp (I.range_subschemeι.symm.subset hwmem)
    have hyy' : y ≤ y' := by
      change Specializes y' y
      apply I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp
      simpa only [I, hy', hyz] using hwgen
    have hymax : IsMax y := Order.coheight_eq_zero.mp
      (ccm3_coheight_eq_zero_of_component_generic hy)
    have heq : y' = y := le_antisymm (hymax hyy') hyy'
    have hwz : wX = z := by rw [← hy', heq, hyz]
    have hwclosed : w = IsLocalRing.closedPoint S := by
      apply (X.fromSpecStalk z).isEmbedding.injective
      simpa only [wX, hwz] using
        (Scheme.fromSpecStalk_closedPoint (X := X) (x := z)).symm
    have hQ₀P' : Q₀ = P := congrArg PrimeSpectrum.asIdeal hwclosed
    change P.map (Ideal.Quotient.mk (p.map φ)) ≤ Q
    rw [Ideal.map_le_iff_le_comap, ← show Q₀ = Q.comap
      (Ideal.Quotient.mk (p.map φ)) from rfl, hQ₀P']
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  change P.height = p.height + P'.height at hheight
  rw [hP', add_zero] at hheight
  apply WithBot.coe_eq_coe.mp
  calc
    (Order.coheight z : WithBot ℕ∞) = ringKrullDim S :=
      (ringKrullDim_stalk_eq_coheight z).symm
    _ = P.height := IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ = p.height := congrArg ((↑) : ℕ∞ → WithBot ℕ∞) hheight
    _ = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
    _ = Order.coheight (f z) := ringKrullDim_stalk_eq_coheight (f z)

/-- Source: Fulton, Intersection Theory, second edition, §1.7, flat inverse-image dimension formula; Stacks Project, Lemma 42.13.1. -/
theorem ccm3_flatPullbackPrime_codimension_aux {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [IsIntegral X.left] [IsIntegral Z.left]
    [Flat f.left] (q : ℕ) (x : Z.left) (hx : Order.coheight x = q)
    (z : X.left) (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    Order.coheight z = q := by
  obtain ⟨y, hyz, hy⟩ := (ccm3_flatPullbackPrime_support_aux f x z).mp hz
  have hfx : f.left z = x := by
    simpa only [hyz] using ccm3_component_maps_to_point f.left x y hy
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  rw [← hx]
  exact ccm3_coheight_eq_of_flat_component f.left x z hfx y hyz hy

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullback_add_aux {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (c d : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (c + d) =
      ccm3_flatPullback f.left c + ccm3_flatPullback f.left d := by
  letI : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  unfold ccm3_flatPullback
  rw [show (fun x : Z.left ↦
      (ccm3_flatPullbackPrime f.left x).mapRange ((c + d) x * ·) (mul_zero _)) =
      fun x ↦ (ccm3_flatPullbackPrime f.left x).mapRange (c x * ·) (mul_zero _) +
        (ccm3_flatPullbackPrime f.left x).mapRange (d x * ·) (mul_zero _) by
    funext x
    apply Function.locallyFinsuppWithin.ext
    intro z
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
      Function.locallyFinsuppWithin.mapRange_apply, add_mul]]
  rw [finsum_add_distrib
    (c.finite_support.subset fun x hx h ↦ hx (by
      apply Function.locallyFinsuppWithin.ext
      intro z
      simp only [Function.locallyFinsuppWithin.mapRange_apply, h, zero_mul]
      change (0 : ℚ) = 0
      rfl))
    (d.finite_support.subset fun x hx h ↦ hx (by
      apply Function.locallyFinsuppWithin.ext
      intro z
      simp only [Function.locallyFinsuppWithin.mapRange_apply, h, zero_mul]
      change (0 : ℚ) = 0
      rfl))]

private theorem ccm3_vanishingIdeal_subscheme_isReduced (X : Scheme)
    (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  letI (U : X.affineOpens) : _root_.IsReduced
      ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.X U) := by
    change _root_.IsReduced (Γ(X, U) ⧸
      (Scheme.IdealSheafData.vanishingIdeal Z).ideal U)
    rw [← Ideal.isRadical_iff_quotient_reduced]
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  letI : ∀ U : (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.I₀,
      IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) :=
    fun U ↦ by
      change X.affineOpens at U
      letI : _root_.IsReduced
          ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.X U) := by
        change _root_.IsReduced (Γ(X, U) ⧸
          (Scheme.IdealSheafData.vanishingIdeal Z).ideal U)
        rw [← Ideal.isRadical_iff_quotient_reduced]
        rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
        exact PrimeSpectrum.isRadical_vanishingIdeal _
      change IsReduced
        (Spec ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.X U))
      infer_instance
  exact IsReduced.of_openCover _
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

private theorem ccm3_genericLength_id_eq_one (X : Scheme) (x : X)
    (y : (ccm3_inverseIdeal (𝟙 X) x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal (𝟙 X) x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal (𝟙 X) x).subscheme) :
    ccm3_genericLength (𝟙 X) x y = 1 := by
  have hI : ccm3_inverseIdeal (𝟙 X) x = ccm3_primeIdeal X x := by
    simp only [ccm3_inverseIdeal, Scheme.IdealSheafData.comap_id]
  letI : IsReduced (ccm3_inverseIdeal (𝟙 X) x).subscheme := by
    rw [hI]
    exact ccm3_vanishingIdeal_subscheme_isReduced X
      ⟨closure ({x} : Set X), isClosed_closure⟩
  have hfield : IsField ((ccm3_inverseIdeal (𝟙 X) x).subscheme.presheaf.stalk y) :=
    isField_stalk_of_closure_mem_irreducibleComponents
      (ccm3_inverseIdeal (𝟙 X) x).subscheme y hy
  letI : Field ((ccm3_inverseIdeal (𝟙 X) x).subscheme.presheaf.stalk y) :=
    hfield.toField
  unfold ccm3_genericLength
  exact Module.length_eq_one _ _

private theorem ccm3_identity_component_map (X : Scheme) (x : X)
    (y : (ccm3_inverseIdeal (𝟙 X) x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal (𝟙 X) x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal (𝟙 X) x).subscheme) :
    (ccm3_inverseIdeal (𝟙 X) x).subschemeι y = x := by
  let I := ccm3_inverseIdeal (𝟙 X) x
  have hs : (I.support : Set X) = closure ({x} : Set X) := by
    simp only [I, ccm3_inverseIdeal, Scheme.IdealSheafData.comap_id,
      ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  letI : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [← isIrreducible_iff_irreducibleSpace, hs]
    exact isIrreducible_singleton.closure
  symm
  apply isGenericPoint_closure.eq
  rw [IsGenericPoint]
  change closure ({y.1} : Set X) = closure ({x} : Set X)
  apply le_antisymm
  · apply closure_minimal
    · rw [Set.singleton_subset_iff, ← hs]
      exact y.2
    · rw [← hs]
      exact I.support.isClosed
  · rw [← hs]
    have hd : Dense ({y} : Set I.subscheme) := by
      rw [dense_iff_closure_eq]
      rw [irreducibleComponents_eq_singleton] at hy
      exact Set.mem_singleton_iff.mp hy
    have he : Subtype.val '' ({y} : Set I.subscheme) = ({y.1} : Set X) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa only [Set.mem_singleton_iff] using congrArg Subtype.val
          (Set.mem_singleton_iff.mp hw)
      · intro hz
        refine ⟨y, Set.mem_singleton y, ?_⟩
        exact Set.mem_singleton_iff.mp hz |>.symm
    rw [← he]
    exact Subtype.dense_iff.mp hd

set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullback_id_aux {X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (c : AlgebraicCycle X.left ℚ) :
    ccm3_flatPullback (𝟙 X.left) c = c := by
  classical
  have hprime (x z : X.left) :
      ccm3_flatPullbackPrime (Over.Hom.left (𝟙 X : X ⟶ X)) x z =
        if z = x then 1 else 0 := by
    by_cases hv : ccm3_flatPullbackPrime (Over.Hom.left (𝟙 X : X ⟶ X)) x z = 0
    · by_cases hzx : z = x
      · subst z
        exfalso
        exact (ccm3_flatPullbackPrime_ne_zero_aux (𝟙 X) x) (by
            apply Function.locallyFinsuppWithin.ext
            intro w
            change ccm3_flatPullbackPrime (Over.Hom.left (𝟙 X : X ⟶ X)) x w = 0
            by_cases hw : ccm3_flatPullbackPrime (Over.Hom.left (𝟙 X : X ⟶ X)) x w = 0
            · exact hw
            · obtain ⟨y, hyw, hy⟩ := (ccm3_flatPullbackPrime_support_aux (𝟙 X) x w).mp hw
              have : w = x := hyw.symm.trans (ccm3_identity_component_map X.left x y hy)
              rw [this]
              exact hv)
      · rw [hv, if_neg hzx]
    · obtain ⟨y, hyz, hy⟩ := (ccm3_flatPullbackPrime_support_aux (𝟙 X) x z).mp hv
      have hzx : z = x := hyz.symm.trans (ccm3_identity_component_map X.left x y hy)
      rw [if_pos hzx]
      calc
        ccm3_flatPullbackPrime (Over.Hom.left (𝟙 X : X ⟶ X)) x z =
            ccm3_flatPullbackPrime (Over.Hom.left (𝟙 X : X ⟶ X)) x
              ((ccm3_inverseIdeal (Over.Hom.left (𝟙 X : X ⟶ X)) x).subschemeι y) := by rw [hyz]
        _ = ((ccm3_genericLength (Over.Hom.left (𝟙 X : X ⟶ X)) x y).toNat : ℚ) :=
          ccm3_flatPullbackPrime_coeff_aux (𝟙 X) x y hy
        _ = 1 := by
          have hg : ccm3_genericLength (Over.Hom.left (𝟙 X : X ⟶ X)) x y = 1 :=
            ccm3_genericLength_id_eq_one X.left x y hy
          rw [hg]
          rfl
  have hprime' (x z : X.left) :
      ccm3_flatPullbackPrime (𝟙 X.left) x z = if z = x then 1 else 0 := by
    rw [← Over.id_left X]
    exact hprime x z
  unfold ccm3_flatPullback
  rw [finsum_congr fun x ↦ show
    (ccm3_flatPullbackPrime (𝟙 X.left) x).mapRange
        (c x * ·) (mul_zero _) =
      Function.locallyFinsuppWithin.single x (c x) by
    apply Function.locallyFinsuppWithin.ext
    intro z
    rw [Function.locallyFinsuppWithin.mapRange_apply, hprime']
    by_cases hzx : z = x
    · subst z
      simp only [if_pos, _root_.mul_one, Function.locallyFinsuppWithin.single_apply,
        Pi.single_eq_same]
    · simp only [if_neg hzx, mul_zero,
        Function.locallyFinsuppWithin.single_apply, Pi.single_eq_of_ne hzx]]
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  calc
    ∑ᶠ x, Function.locallyFinsuppWithin.single x (c x) =
        ∑ᶠ x, (Function.locallyFinsuppWithin.single x (c x)).restrict
          (Set.subset_univ _) := by
      apply finsum_congr
      intro x
      apply Function.locallyFinsuppWithin.ext
      intro z
      simp only [Function.locallyFinsuppWithin.restrict_apply, Set.mem_univ, if_true]
    _ = c := Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self c.finite_support

end HodgeLean.Adapters
