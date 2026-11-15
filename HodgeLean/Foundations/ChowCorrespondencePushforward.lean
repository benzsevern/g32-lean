import HodgeLean.Foundations.ChowCorrespondenceValuation
import HodgeLean.Foundations.ChowCorrespondenceRat

/-! # Proper pushforward of principal cycles

Helpers for lane A2 (rational equivalence), the geometric part. On an integral scheme `W` of finite
type over `ℂ`, the order of a rational function at a point of codimension one is the sum of its
orders at the valuations of the function field centred there, weighted by residue degrees
(`ChowCorrespondenceValuation`). For a proper dominant morphism `h : W ⟶ V` of such schemes, the
valuative criterion matches the valuations centred over a point `y` of `V` with the points of the
fibre over `y`. Summing gives Fulton's Proposition 1.4: `h_*[div φ] = [div N(φ)]` when
`dim V = dim W`, and `h_*[div φ] = 0` otherwise (degree of a principal divisor on the generic
fibre).
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing HodgeLean.Foundations.Curves Order

namespace HodgeLean.Adapters

/-! ## Stalks of an integral scheme of finite type over `ℂ` -/

section stalks

variable {W : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom] [IsIntegral W.left]

instance (priority := low) a2r_isLocallyNoetherian_left : IsLocallyNoetherian W.left :=
  LocallyOfFiniteType.isLocallyNoetherian W.hom

/-- The normalization of a stalk of an integral scheme of finite type over `ℂ` is finite.
Source: Eisenbud, *Commutative Algebra*, Corollary 13.13; Atiyah–Macdonald, Proposition 5.12. -/
theorem a2r_finite_integralClosure_stalk (z : W.left) :
    Module.Finite (W.left.presheaf.stalk z)
      (integralClosure (W.left.presheaf.stalk z) W.left.functionField) := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show z ∈ (⊤ : W.left.Opens) from trivial)
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  let : Algebra ℂ Γ(W.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ W.hom.appLE ⊤ U (by simp)).hom.toAlgebra
  have : Algebra.FiniteType ℂ Γ(W.left, U) := by
    refine RingHom.finiteType_algebraMap.mp ?_
    change ((W.hom.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).FiniteType
    refine RingHom.FiniteType.comp ?_ ?_
    · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) W.hom ‹_›
        ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
    · exact RingHom.FiniteType.of_surjective _
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  have : IsFractionRing Γ(W.left, U) W.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen W.left U hU
  have : Module.Finite Γ(W.left, U) (integralClosure Γ(W.left, U) W.left.functionField) :=
    a2r_finite_integralClosure (k := ℂ)
  let x : U := ⟨z, hzU⟩
  let := TopCat.Presheaf.algebra_section_stalk W.left.presheaf x
  have := hU.isLocalization_stalk x
  have := functionField_isScalarTower W.left U x
  exact a2r_finite_integralClosure_localization (A := Γ(W.left, U))
    (hU.primeIdealOf x).asIdeal.primeCompl

/-- Mathlib's order of vanishing at a codimension-one point is the integer order on the stalk. -/
theorem a2r_ord_eq_ordZ {z : W.left} (hz : coheight z = 1) (φ : W.left.functionField) :
    have : Ring.KrullDimLE 1 (W.left.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    W.left.ord φ z = a2r_ordZ (W.left.presheaf.stalk z) W.left.functionField φ := by
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz]
  rfl

/-- **The order at a codimension-one point as a sum over valuations.**
Source: Fulton, *Intersection Theory*, second edition, Example A.3.1. -/
theorem a2r_ord_eq_finsum {z : W.left} (hz : coheight z = 1) {φ : W.left.functionField}
    (hφ : φ ≠ 0) :
    (a2r_Dom (W.left.presheaf.stalk z) W.left.functionField).Finite ∧
      W.left.ord φ z = ∑ᶠ v ∈ a2r_Dom (W.left.presheaf.stalk z) W.left.functionField,
        a2r_vord v φ * a2r_resDeg (W.left.presheaf.stalk z) v := by
  have : Ring.KrullDimLE 1 (W.left.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have := a2r_finite_integralClosure_stalk z
  have hO : maximalIdeal (W.left.presheaf.stalk z) ≠ ⊥ := by
    intro h
    have hfield : IsField (W.left.presheaf.stalk z) :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
    have hdim := ringKrullDim_stalk_eq_coheight z
    rw [hz, ringKrullDim_eq_zero_of_isField hfield] at hdim
    exact absurd hdim (by decide)
  obtain ⟨hfin, h⟩ := a2r_ordZ_eq_finsum (W.left.presheaf.stalk z) W.left.functionField hO
  exact ⟨hfin, (a2r_ord_eq_ordZ hz φ).trans (h φ hφ)⟩

/-- The valuations dominating the stalk at a codimension-one point are DVRs. -/
theorem a2r_isDVR_of_mem_Dom_stalk {z : W.left} (hz : coheight z = 1)
    (v : ValuationSubring W.left.functionField)
    (hv : v ∈ a2r_Dom (W.left.presheaf.stalk z) W.left.functionField) :
    IsDiscreteValuationRing v := by
  have : Ring.KrullDimLE 1 (W.left.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have := a2r_finite_integralClosure_stalk z
  have hO : maximalIdeal (W.left.presheaf.stalk z) ≠ ⊥ := by
    intro h
    have hfield : IsField (W.left.presheaf.stalk z) :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
    have hdim := ringKrullDim_stalk_eq_coheight z
    rw [hz, ringKrullDim_eq_zero_of_isField hfield] at hdim
    exact absurd hdim (by decide)
  exact a2r_isDVR_of_mem_Dom _ _ hO v hv

omit [LocallyOfFiniteType W.hom] in
/-- At the generic point no proper valuation subring dominates the stalk. -/
theorem a2r_Dom_eq_empty_of_eq_genericPoint {z : W.left} (hz : z = genericPoint W.left) :
    a2r_Dom (W.left.presheaf.stalk z) W.left.functionField = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hv, hdom⟩
  apply hv
  refine a2r_eq_top_of_forall_mem v fun x => ?_
  have hfield : IsField (W.left.presheaf.stalk z) := by
    subst hz
    exact Field.toIsField W.left.functionField
  obtain ⟨a, rfl⟩ := (IsFractionRing.surjective_iff_isField
    (R := W.left.presheaf.stalk z) (K := W.left.functionField)).mpr hfield x
  exact (hdom a).1

end stalks

/-! ## Finiteness of principal divisors -/

/-- On a Noetherian integral scheme the order of a rational function is nonzero at finitely many
points.
Source: Hartshorne, *Algebraic Geometry*, II, Lemma 6.1. -/
theorem a2r_ord_support_finite (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    [TopologicalSpace.NoetherianSpace X] (f : X.functionField) :
    (Function.support (ordAt X f)).Finite := by
  classical
  by_cases hf : f = 0
  · subst hf
    rw [show ordAt X 0 = 0 from funext fun P => congrFun Scheme.ord_zero P]
    simp
  obtain ⟨U, -, f', _, hf', hunit⟩ := exists_isUnit_germ_eq X f hf
  have hC : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have hηU : genericPoint X ∈ U := by
    obtain ⟨u⟩ := ‹Nonempty U›
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨u.1, trivial, u.2⟩
  refine (hSfin.image fun t => if h : t ∈ S then (hSirr t h).genericPoint else genericPoint X)
    |>.subset fun z hz => ?_
  have hz1 : coheight z = 1 := by
    by_contra h
    exact hz (Scheme.ord_eq_zero_of_coheight_neq_one h f)
  change X.ord f z ≠ 0 at hz
  have hzU : z ∉ U := by
    intro hzU
    apply hz
    rw [← hf']
    exact Scheme.ord_of_isUnit hunit hzU
  have hzC : z ∈ ⋃₀ S := hSeq ▸ hzU
  obtain ⟨t, htS, hzt⟩ := hzC
  refine ⟨t, htS, ?_⟩
  simp only [htS, dite_true]
  set g := (hSirr t htS).genericPoint
  have hg : IsGenericPoint g t := by
    have := (hSirr t htS).isGenericPoint_genericPoint_closure
    rwa [(hScl t htS).closure_eq] at this
  have hzg : z ≤ g := Scheme.le_iff_specializes.mpr (hg.specializes hzt)
  have hgC : g ∉ U := by
    have : g ∈ ⋃₀ S := ⟨t, htS, hg.mem⟩
    rw [← hSeq] at this
    exact this
  have hgη : g < genericPoint X := by
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr
      ((genericPoint_spec X).specializes trivial)) fun h => hgC ?_
    have h' : g ⤳ genericPoint X := Scheme.le_iff_specializes.mp h
    have h'' : genericPoint X ⤳ g := (genericPoint_spec X).specializes trivial
    exact (h''.antisymm h').eq ▸ hηU
  by_contra hne
  have hzg' : z < g := by
    refine lt_of_le_not_ge hzg fun h => hne ?_
    exact ((Scheme.le_iff_specializes.mp hzg).antisymm (Scheme.le_iff_specializes.mp h)).eq
  have h1 := Order.coheight_add_one_le hzg'
  have h2 : coheight g ≠ 0 := fun h0 => (Order.coheight_eq_zero.mp h0).not_lt hgη
  rw [hz1] at h1
  have hg1 : (1 : ℕ∞) ≤ coheight g := Order.one_le_iff_ne_zero.mpr h2
  have h3 : (2 : ℕ∞) ≤ 1 := calc
    (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ coheight g + 1 := by gcongr
    _ ≤ 1 := h1
  norm_num at h3

/-- The coefficients of a principal divisor on a Noetherian integral scheme are the orders. -/
theorem a2r_principalDivisor_apply (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    [TopologicalSpace.NoetherianSpace X] (f : X.functionField) (z : X) :
    (principalDivisor X f : AlgebraicCycle X ℤ) z = X.ord f z := by
  classical
  unfold principalDivisor
  split_ifs with h
  · rfl
  · exact absurd (a2r_ord_support_finite X f) h

/-! ## The function field map of a dominant morphism -/

section centers

variable {W V : Scheme} [IsIntegral W] [IsIntegral V] (h : W ⟶ V)
  (hdom : h (genericPoint W) = genericPoint V)

include hdom in
theorem a2r_spec_generic (y : V) : h (genericPoint W) ⤳ y :=
  hdom ▸ (genericPoint_spec V).specializes trivial

/-- The map of function fields `K(V) → K(W)` of a dominant morphism. -/
def a2r_ffHom : V.functionField →+* W.functionField :=
  (V.presheaf.stalkSpecializes (show h (genericPoint W) ⤳ genericPoint V from
    hdom ▸ specializes_rfl) ≫ h.stalkMap (genericPoint W)).hom

/-- The composite `𝒪_{V,y} → K(V) → K(W)`. -/
def a2r_stalkHom (y : V) : V.presheaf.stalk y →+* W.functionField :=
  (a2r_ffHom h hdom).comp (algebraMap (V.presheaf.stalk y) V.functionField)

theorem a2r_stalkHom_eq (y : V) :
    a2r_stalkHom h hdom y =
      (V.presheaf.stalkSpecializes (a2r_spec_generic h hdom y) ≫
        h.stalkMap (genericPoint W)).hom := by
  rw [a2r_stalkHom, a2r_ffHom, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

/-- Compatibility of the stalk maps with the function field map. -/
theorem a2r_stalkHom_comp (z : W) :
    (algebraMap (W.presheaf.stalk z) W.functionField).comp (h.stalkMap z).hom =
      a2r_stalkHom h hdom (h z) := by
  rw [a2r_stalkHom_eq, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
  congr 1
  rw [← Scheme.Hom.stalkSpecializes_stalkMap h (genericPoint W) z
    ((genericPoint_spec W).specializes trivial)]

/-- The valuation subrings of `K(W)` dominating `𝒪_{V,y}`. -/
def a2r_DomV (y : V) : Set (ValuationSubring W.functionField) :=
  letI := (a2r_stalkHom h hdom y).toAlgebra
  a2r_Dom (V.presheaf.stalk y) W.functionField

/-- The residue degree of a valuation subring of `K(W)` over `𝒪_{V,y}`. -/
def a2r_resDegV (y : V) (v : ValuationSubring W.functionField) : ℕ :=
  letI := (a2r_stalkHom h hdom y).toAlgebra
  a2r_resDeg (V.presheaf.stalk y) v

/-- A valuation dominating `𝒪_{W,z}` dominates `𝒪_{V,h z}`. -/
theorem a2r_mem_DomV_of_mem_Dom (z : W) (v : ValuationSubring W.functionField)
    (hv : v ∈ a2r_Dom (W.presheaf.stalk z) W.functionField) : v ∈ a2r_DomV h hdom (h z) := by
  let := (a2r_stalkHom h hdom (h z)).toAlgebra
  refine ⟨hv.1, fun a => ?_⟩
  have hc : algebraMap (V.presheaf.stalk (h z)) W.functionField a =
      algebraMap (W.presheaf.stalk z) W.functionField (h.stalkMap z a) := by
    rw [RingHom.algebraMap_toAlgebra, ← a2r_stalkHom_comp]
    rfl
  rw [hc]
  refine ⟨(hv.2 _).1, fun ha => (hv.2 _).2 ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  exact fun hu => ha (isUnit_of_map_unit _ _ hu)

/-- Residue degrees along `h`: `[κ(v) : κ(h z)] = deg_h(z) · [κ(v) : κ(z)]`. -/
theorem a2r_resDegV_eq (z : W) (v : ValuationSubring W.functionField)
    (hv : v ∈ a2r_Dom (W.presheaf.stalk z) W.functionField) :
    a2r_resDegV h hdom (h z) v = a1p_degree h z * a2r_resDeg (W.presheaf.stalk z) v := by
  let := (a2r_stalkHom h hdom (h z)).toAlgebra
  have hv' := a2r_mem_DomV_of_mem_Dom h hdom z v hv
  have := a2r_domHom_isLocalHom v hv'.2
  have := a2r_domHom_isLocalHom v hv.2
  change a2r_resDeg (V.presheaf.stalk (h z)) v = _
  rw [a2r_resDeg_of v hv'.2, a2r_resDeg_of v hv.2]
  have hcomp : a2r_domHom v (fun a => (hv'.2 a).1) =
      (a2r_domHom v (fun a => (hv.2 a).1)).comp (h.stalkMap z).hom := by
    ext a
    change a2r_stalkHom h hdom (h z) a =
      algebraMap (W.presheaf.stalk z) W.functionField (h.stalkMap z a)
    rw [← a2r_stalkHom_comp]
    rfl
  have hmap : ResidueField.map (a2r_domHom v (fun a => (hv'.2 a).1)) =
      (ResidueField.map (a2r_domHom v (fun a => (hv.2 a).1))).comp
        (ResidueField.map (h.stalkMap z).hom) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨x0, rfl⟩ := IsLocalRing.residue_surjective x
    simp only [RingHom.comp_apply, ResidueField.map_residue]
    rw [hcomp]
    rfl
  rw [hmap]
  exact a2r_finrank_comp _ _

/-- **Existence of centres.** For a universally closed `h`, every valuation of `K(W)` dominating
`𝒪_{V,y}` dominates the local ring of a point of the fibre over `y`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 4.7; Mathlib,
`UniversallyClosed.eq_valuativeCriterion`. -/
theorem a2r_exists_center [UniversallyClosed h] (y : V) (v : ValuationSubring W.functionField)
    (hv : v ∈ a2r_DomV h hdom y) :
    ∃ z, h z = y ∧ v ∈ a2r_Dom (W.presheaf.stalk z) W.functionField := by
  let := (a2r_stalkHom h hdom y).toAlgebra
  obtain ⟨hvtop, hvdom⟩ := hv
  let ι : V.presheaf.stalk y →+* v := a2r_domHom v (fun a => (hvdom a).1)
  have hιloc : IsLocalHom ι := a2r_domHom_isLocalHom v hvdom
  let sq : ValuativeCommSq h :=
    { R := v
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom ι) ≫ V.fromSpecStalk y
      commSq := ⟨by
        rw [← Scheme.SpecMap_stalkMap_fromSpecStalk h,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (a2r_spec_generic h hdom y),
          ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        refine congrArg (· ≫ V.fromSpecStalk y) (congrArg Spec.map ?_)
        ext a
        change (V.presheaf.stalkSpecializes (a2r_spec_generic h hdom y) ≫
          h.stalkMap (genericPoint W)).hom a = a2r_stalkHom h hdom y a
        rw [a2r_stalkHom_eq]⟩ }
  have hex : (ValuativeCriterion.Existence ⊓ @QuasiCompact) h :=
    UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed h)
  obtain ⟨⟨ℓ, hl₁, hl₂⟩⟩ := hex.1 sq
  refine ⟨ℓ (IsLocalRing.closedPoint v), ?_, ?_⟩
  · have e : h (ℓ (IsLocalRing.closedPoint v)) = sq.i₂ (IsLocalRing.closedPoint v) := by
      rw [← hl₂]; rfl
    rw [e]
    change V.fromSpecStalk y (Spec.map (CommRingCat.ofHom ι) (IsLocalRing.closedPoint v)) = y
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  · set z := ℓ (IsLocalRing.closedPoint v)
    let φ := Scheme.stalkClosedPointTo ℓ
    have hφloc : IsLocalHom φ.hom := inferInstance
    have hsp : genericPoint W ⤳ z := (genericPoint_spec W).specializes trivial
    have hℓ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ℓ
    have key : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap v W.functionField)) ≫
        W.fromSpecStalk z =
        Spec.map (W.presheaf.stalkSpecializes hsp) ≫ W.fromSpecStalk z := by
      rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Spec.map_comp, Category.assoc, hℓ]
      exact hl₁
    have hcomp := Spec.map_injective ((cancel_mono _).mp key)
    have hφ : ∀ s, algebraMap v W.functionField (φ s) =
        algebraMap (W.presheaf.stalk z) W.functionField s := fun s => congr($hcomp s)
    refine ⟨hvtop, fun s => ⟨?_, fun hs => ?_⟩⟩
    · rw [← hφ]
      exact (φ s).2
    · rw [← hφ]
      refine (ValuationSubring.valuation_lt_one_iff v (φ s)).mp ?_
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
      exact fun hu => hs (isUnit_of_map_unit φ.hom _ hu)

/-- The local ring map `𝒪_{W,z} → v` of a dominating valuation, followed by `Spec`, lifts the
valuative square over `y = h z`. -/
theorem a2r_lift_comp (y : V) (z : W) (hz : h z = y) (v : ValuationSubring W.functionField)
    (hvz : v ∈ a2r_Dom (W.presheaf.stalk z) W.functionField) (hvy : v ∈ a2r_DomV h hdom y) :
    (Spec.map (CommRingCat.ofHom (a2r_domHom v fun a => (hvz.2 a).1)) ≫ W.fromSpecStalk z) ≫ h =
      Spec.map (CommRingCat.ofHom (letI := (a2r_stalkHom h hdom y).toAlgebra
        a2r_domHom v fun a => (hvy.2 a).1)) ≫ V.fromSpecStalk y := by
  subst hz
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk h, ← Category.assoc,
    ← Spec.map_comp]
  refine congrArg (· ≫ V.fromSpecStalk (h z)) (congrArg Spec.map ?_)
  ext a
  change algebraMap (W.presheaf.stalk z) W.functionField (h.stalkMap z a) =
    a2r_stalkHom h hdom (h z) a
  rw [← a2r_stalkHom_comp]
  rfl

theorem a2r_lift_fac_left (z : W) (v : ValuationSubring W.functionField)
    (hvz : v ∈ a2r_Dom (W.presheaf.stalk z) W.functionField) :
    Spec.map (CommRingCat.ofHom (algebraMap v W.functionField)) ≫
      (Spec.map (CommRingCat.ofHom (a2r_domHom v fun a => (hvz.2 a).1)) ≫ W.fromSpecStalk z) =
    W.fromSpecStalk (genericPoint W) := by
  rw [← Category.assoc, ← Spec.map_comp,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec W).specializes trivial)]
  refine congrArg (· ≫ W.fromSpecStalk z) (congrArg Spec.map ?_)
  ext a
  rfl

include hdom in
/-- **Uniqueness of centres.** For a separated `h`, a valuation of `K(W)` dominates the local ring
of at most one point of each fibre.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 4.3; Mathlib,
`IsSeparated.valuativeCriterion`. -/
theorem a2r_center_unique [IsSeparated h] (y : V) {z z' : W} (hz : h z = y) (hz' : h z' = y)
    (v : ValuationSubring W.functionField)
    (hv : v ∈ a2r_Dom (W.presheaf.stalk z) W.functionField)
    (hv' : v ∈ a2r_Dom (W.presheaf.stalk z') W.functionField) : z = z' := by
  have hvy : v ∈ a2r_DomV h hdom y := hz ▸ a2r_mem_DomV_of_mem_Dom h hdom z v hv
  let := (a2r_stalkHom h hdom y).toAlgebra
  let ι : V.presheaf.stalk y →+* v := a2r_domHom v (fun a => (hvy.2 a).1)
  have hιloc : IsLocalHom ι := a2r_domHom_isLocalHom v hvy.2
  let sq : ValuativeCommSq h :=
    { R := v
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom ι) ≫ V.fromSpecStalk y
      commSq := ⟨by
        rw [← a2r_lift_fac_left z v hv, Category.assoc, a2r_lift_comp h hdom y z hz v hv hvy]⟩ }
  have huniq := IsSeparated.valuativeCriterion h sq
  let lz : sq.commSq.LiftStruct :=
    ⟨_, a2r_lift_fac_left z v hv, a2r_lift_comp h hdom y z hz v hv hvy⟩
  let lz' : sq.commSq.LiftStruct :=
    ⟨_, a2r_lift_fac_left z' v hv', a2r_lift_comp h hdom y z' hz' v hv' hvy⟩
  have heq : lz.l = lz'.l := congrArg CommSq.LiftStruct.l (huniq.elim lz lz')
  have hloc : IsLocalHom (a2r_domHom v fun a => (hv.2 a).1) := a2r_domHom_isLocalHom v hv.2
  have hloc' : IsLocalHom (a2r_domHom v fun a => (hv'.2 a).1) := a2r_domHom_isLocalHom v hv'.2
  have e1 : lz.l (IsLocalRing.closedPoint v) = z := by
    change W.fromSpecStalk z (Spec.map (CommRingCat.ofHom (a2r_domHom v fun a => (hv.2 a).1))
      (IsLocalRing.closedPoint v)) = z
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have e2 : lz'.l (IsLocalRing.closedPoint v) = z' := by
    change W.fromSpecStalk z' (Spec.map (CommRingCat.ofHom (a2r_domHom v fun a => (hv'.2 a).1))
      (IsLocalRing.closedPoint v)) = z'
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  rw [← e1, ← e2, heq]

end centers

/-! ## Dimensions over `ℂ` -/

section dims

/-- The constants `ℂ → K(W)` of an integral scheme over `ℂ`. -/
def a2r_ffC (W : Over (Spec ↧ℂ)) [IsIntegral W.left] : ℂ →+* W.left.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ W.hom.appTop ≫
    W.left.presheaf.germ ⊤ (genericPoint W.left) (show _ ∈ (⊤ : W.left.Opens) from trivial)).hom

/-- The function field is the residue field at the generic point, over `ℂ`. -/
theorem a2r_ff_trdeg (W : Over (Spec ↧ℂ)) [LocallyOfFiniteType W.hom] [IsIntegral W.left] :
    letI := (a2r_ffC W).toAlgebra
    Algebra.EssFiniteType ℂ W.left.functionField ∧ ∃ n : ℕ,
      height (genericPoint W.left) = n ∧ Algebra.trdeg ℂ W.left.functionField = n := by
  let := (a2r_ffC W).toAlgebra
  let : Algebra ℂ (W.left.residueField (genericPoint W.left)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ W.hom.appTop ≫
      W.left.Γevaluation (genericPoint W.left)).hom.toAlgebra
  obtain ⟨hfg, n, hn, htr⟩ := a1d_height_eq_trdeg (genericPoint W.left)
  have hbij : Function.Bijective (W.left.residue (genericPoint W.left)).hom := by
    refine ⟨fun a b hab => ?_, IsLocalRing.residue_surjective⟩
    have : a - b ∈ maximalIdeal (W.left.presheaf.stalk (genericPoint W.left)) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact hab
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  let e : W.left.functionField ≃ₐ[ℂ] W.left.residueField (genericPoint W.left) :=
    { RingEquiv.ofBijective _ hbij with commutes' := fun c => rfl }
  refine ⟨Algebra.EssFiniteType.of_surjective e.symm.toAlgHom e.symm.surjective, n, hn, ?_⟩
  rw [e.trdeg_eq, htr]

/-- An `Over` morphism maps constants to constants. -/
theorem a2r_ffHom_ffC {W V : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral V.left] (h : W ⟶ V)
    (hdom : h.left (genericPoint W.left) = genericPoint V.left) (c : ℂ) :
    a2r_ffHom h.left hdom (a2r_ffC V c) = a2r_ffC W c := by
  have hsp : h.left (genericPoint W.left) ⤳ genericPoint V.left := hdom ▸ specializes_rfl
  have hmV : genericPoint V.left ∈ (⊤ : V.left.Opens) := trivial
  have hmW : genericPoint W.left ∈ (⊤ : W.left.Opens) := trivial
  have key2 : ∀ x, h.left.app ⊤ (V.hom.appTop x) = W.hom.appTop x := by
    intro x
    rw [← Over.w h]
    rfl
  change (V.left.presheaf.stalkSpecializes hsp ≫ h.left.stalkMap (genericPoint W.left)).hom
    (V.left.presheaf.germ ⊤ (genericPoint V.left) hmV
      (V.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
    W.left.presheaf.germ ⊤ (genericPoint W.left) hmW
      (W.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply, key2]
  rfl

/-- The height of a point does not increase under a morphism of schemes of finite type over `ℂ`. -/
theorem a2r_height_map_le {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (x : X.left) : height (f.left x) ≤ height x := by
  let : Algebra ℂ (X.left.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
  let : Algebra ℂ (Y.left.residueField (f.left x)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appTop ≫
      Y.left.Γevaluation (f.left x)).hom.toAlgebra
  let : Algebra (Y.left.residueField (f.left x)) (X.left.residueField x) :=
    (f.left.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower ℂ (Y.left.residueField (f.left x)) (X.left.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = f.left.residueFieldMap x (Y.left.Γevaluation (f.left x) (Y.hom.appTop _))
    rw [Scheme.Γevaluation_naturality_apply]
    change _ = X.left.Γevaluation x ((Y.hom.appTop ≫ f.left.appTop) _)
    rw [← Scheme.Hom.comp_appTop, Over.w f]
    rfl
  obtain ⟨-, n, hn, htr⟩ := a1d_height_eq_trdeg x
  obtain ⟨-, m, hm, htr'⟩ := a1d_height_eq_trdeg (f.left x)
  have hadd := trdeg_add_eq ℂ (Y.left.residueField (f.left x)) (A := X.left.residueField x)
  rw [htr, htr'] at hadd
  rw [hn, hm, Nat.cast_le]
  have : (m : Cardinal) ≤ n := hadd ▸ le_self_add
  exact_mod_cast this

end dims

/-! ## The pushforward coefficient as a sum over valuations -/

section regroup

variable {W V : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsIntegral W.left] [IsIntegral V.left] (h : W ⟶ V) [IsProper h.left]
  (hdom : h.left (genericPoint W.left) = genericPoint V.left)

open Classical in
/-- A centre in `W` of a valuation dominating `𝒪_{V,y}` (junk value the generic point). -/
def a2r_center (y : V.left) (v : ValuationSubring W.left.functionField) : W.left :=
  if hv : v ∈ a2r_DomV h.left hdom y then
    Classical.choose (a2r_exists_center h.left hdom y v hv)
  else genericPoint W.left

omit [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] in
theorem a2r_center_spec (y : V.left) (v : ValuationSubring W.left.functionField)
    (hv : v ∈ a2r_DomV h.left hdom y) :
    h.left (a2r_center h hdom y v) = y ∧
      v ∈ a2r_Dom (W.left.presheaf.stalk (a2r_center h hdom y v)) W.left.functionField := by
  rw [a2r_center, dite_eq_left hv]
  exact Classical.choose_spec (a2r_exists_center h.left hdom y v hv)

/-- **Regrouping.** If every point of the fibre over `y` other than the generic point has
codimension one, and the summand has finite support, the coefficient of `h_*[div φ]` at `y` is the
sum of `v(φ) [κ(v) : κ(y)]` over the valuations dominating `𝒪_{V,y}`.
Source: Fulton, *Intersection Theory*, second edition, proof of Proposition 1.4. -/
theorem a2r_pushforward_principal_apply (y : V.left) {φ : W.left.functionField} (hφ : φ ≠ 0)
    (hfib : ∀ z, h.left z = y → z ≠ genericPoint W.left → coheight z = 1)
    (hsupp : (a2r_DomV h.left hdom y ∩ Function.support fun v =>
      a2r_vord v φ * a2r_resDegV h.left hdom y v).Finite) :
    a1p_pushforward h.left (principalDivisor W.left φ : AlgebraicCycle W.left ℤ) y =
      ∑ᶠ v ∈ a2r_DomV h.left hdom y, a2r_vord v φ * a2r_resDegV h.left hdom y v := by
  classical
  set g : ValuationSubring W.left.functionField → ℤ :=
    fun v => a2r_vord v φ * a2r_resDegV h.left hdom y v
  set D : AlgebraicCycle W.left ℤ := ↑(principalDivisor W.left φ)
  have hD : ∀ z, D z = W.left.ord φ z := a2r_principalDivisor_apply W.left φ
  have hDfin : (Function.support D).Finite := by
    have := a2r_ord_support_finite W.left φ
    refine this.subset fun z hz => ?_
    change W.left.ord φ z ≠ 0
    rw [← hD]; exact hz
  set F : Set W.left := h.left ⁻¹' {y}
  set T : Set W.left := (F ∩ Function.support D) ∪
    (a2r_center h hdom y '' (a2r_DomV h.left hdom y ∩ Function.support g))
  have hTfin : T.Finite := ((hDfin.subset Set.inter_subset_right)).union (hsupp.image _)
  have hTF : T ⊆ F := by
    rintro z (⟨hz, -⟩ | ⟨v, ⟨hv, -⟩, rfl⟩)
    · exact hz
    · exact (a2r_center_spec h hdom y v hv).1
  -- the coefficient as a sum over `T`
  change ∑ᶠ z ∈ F, D z * (a1p_degree h.left z : ℤ) = _
  rw [finsum_mem_inter_support_eq' _ F T fun z hz => ⟨fun hzF => Or.inl ⟨hzF, fun h0 => hz
    (by simp [h0])⟩, fun hzT => hTF hzT⟩]
  -- each term as a sum over valuations
  have hterm : ∀ z ∈ T, D z * (a1p_degree h.left z : ℤ) =
      ∑ᶠ v ∈ a2r_Dom (W.left.presheaf.stalk z) W.left.functionField, g v := by
    intro z hzT
    have hzy : h.left z = y := hTF hzT
    by_cases hη : z = genericPoint W.left
    · rw [a2r_Dom_eq_empty_of_eq_genericPoint hη, finsum_mem_empty, hD,
        Scheme.ord_eq_zero_of_coheight_neq_one, zero_mul]
      subst hη
      rw [Order.coheight_eq_zero.mpr]
      · exact zero_ne_one
      · intro b hb
        exact Scheme.le_iff_specializes.mpr ((genericPoint_spec W.left).specializes trivial)
    · have hz1 := hfib z hzy hη
      obtain ⟨hfin, hord⟩ := a2r_ord_eq_finsum hz1 hφ
      rw [hD, hord, finsum_mem_mul]
      refine finsum_mem_congr rfl fun v hv => ?_
      simp only [g]
      subst hzy
      rw [a2r_resDegV_eq h.left hdom z v hv]
      push_cast
      ring
  rw [finsum_mem_congr rfl hterm]
  have hdisj : T.PairwiseDisjoint fun z =>
      a2r_Dom (W.left.presheaf.stalk z) W.left.functionField := by
    intro z hz z' hz' hne
    refine Set.disjoint_left.mpr fun v hv hv' => hne ?_
    exact a2r_center_unique h.left hdom y (hTF hz) (hTF hz') v hv hv'
  have hfin2 : ∀ z ∈ T, (a2r_Dom (W.left.presheaf.stalk z) W.left.functionField).Finite := by
    intro z hzT
    by_cases hη : z = genericPoint W.left
    · rw [a2r_Dom_eq_empty_of_eq_genericPoint hη]
      exact Set.finite_empty
    · exact (a2r_ord_eq_finsum (hfib z (hTF hzT) hη) hφ).1
  rw [← finsum_mem_biUnion hdisj hTfin hfin2]
  refine finsum_mem_inter_support_eq' _ _ _ fun v hv => ⟨fun hvU => ?_, fun hvD => ?_⟩
  · simp only [Set.mem_iUnion, exists_prop] at hvU
    obtain ⟨z, hzT, hvz⟩ := hvU
    have := a2r_mem_DomV_of_mem_Dom h.left hdom z v hvz
    rwa [hTF hzT] at this
  · simp only [Set.mem_iUnion, exists_prop]
    exact ⟨a2r_center h hdom y v, Or.inr ⟨v, ⟨hvD, hv⟩, rfl⟩,
      (a2r_center_spec h hdom y v hvD).2⟩

end regroup

/-! ## Dimension bookkeeping -/

section bookkeeping

/-- Every point lies below the generic point, strictly unless it is the generic point. -/
theorem a2r_lt_genericPoint (X : Scheme) [IsIntegral X] {z : X} (hz : z ≠ genericPoint X) :
    z < genericPoint X := by
  refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr
    ((genericPoint_spec X).specializes trivial)) fun h => hz ?_
  exact ((genericPoint_spec X).specializes trivial).antisymm
    (Scheme.le_iff_specializes.mp h) |>.eq.symm

variable {W : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom] [IsIntegral W.left]

/-- A point of height equal to that of the generic point is the generic point. -/
theorem a2r_eq_genericPoint_of_height {y : W.left}
    (hy : height y = height (genericPoint W.left)) : y = genericPoint W.left := by
  by_contra hne
  have h1 := Order.height_add_one_le (a2r_lt_genericPoint W.left hne)
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (genericPoint W.left)
  rw [hy, hn] at h1
  have : ((n : ℕ∞) + 1) ≤ n := h1
  norm_cast at this
  omega

/-- `height z + coheight z = height η` with all values natural numbers. -/
theorem a2r_height_add_coheight_nat (z : W.left) :
    ∃ a b n : ℕ, height z = a ∧ coheight z = b ∧ height (genericPoint W.left) = n ∧ a + b = n := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (genericPoint W.left)
  obtain ⟨-, a, ha, -⟩ := a1d_height_eq_trdeg z
  have hsum := a2r_height_add_coheight W z
  rw [ha, hn] at hsum
  have hb : coheight z ≠ ⊤ := by
    intro htop
    rw [htop] at hsum
    simp at hsum
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hb
  refine ⟨a, b, n, ha, hb.symm, hn, ?_⟩
  rw [← hb] at hsum
  exact_mod_cast hsum

end bookkeeping

section fibres

variable {W V : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsIntegral W.left] [LocallyOfFiniteType V.hom] [IsIntegral V.left] (h : W ⟶ V)
  [QuasiCompact h.left]

omit [QuasiCompact W.hom] [IsIntegral V.left] [QuasiCompact h.left] in
/-- Over a point `y` with `height y + 1 = dim W`, every point of the fibre other than the generic
point has codimension one. -/
theorem a2r_fibre_coheight (y : V.left)
    (hy : height y + 1 = height (genericPoint W.left)) (z : W.left) (hz : h.left z = y)
    (hzη : z ≠ genericPoint W.left) : coheight z = 1 := by
  have h1 : height y ≤ height z := hz ▸ a2r_height_map_le h z
  have h2 := Order.height_add_one_le (a2r_lt_genericPoint W.left hzη)
  obtain ⟨a, b, n, ha, hb, hn, hab⟩ := a2r_height_add_coheight_nat z
  obtain ⟨-, m, hm, -⟩ := a1d_height_eq_trdeg y
  rw [ha, hm] at h1
  rw [ha, hn] at h2
  rw [hm, hn] at hy
  rw [hb]
  have h1' : m ≤ a := by exact_mod_cast h1
  have h2' : a + 1 ≤ n := by exact_mod_cast h2
  have hy' : m + 1 = n := by exact_mod_cast hy
  have : b = 1 := by omega
  rw [this]
  rfl

omit [IsIntegral V.left] in
/-- A point where `h_*[div φ]` has a nonzero coefficient has `height y + 1 = dim W`. -/
theorem a2r_height_of_pushforward_principal_ne_zero (φ : W.left.functionField) (y : V.left)
    (hy : a1p_pushforward h.left (principalDivisor W.left φ : AlgebraicCycle W.left ℤ) y ≠ 0) :
    height y + 1 = height (genericPoint W.left) := by
  change ∑ᶠ z ∈ h.left ⁻¹' {y}, (principalDivisor W.left φ : AlgebraicCycle W.left ℤ) z *
    (a1p_degree h.left z : ℤ) ≠ 0 at hy
  obtain ⟨z, hz, hzne⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  have hD : (principalDivisor W.left φ : AlgebraicCycle W.left ℤ) z ≠ 0 :=
    fun h0 => hzne (by rw [h0, zero_mul])
  have hdeg : a1p_degree h.left z ≠ 0 := fun h0 => hzne (by rw [h0]; simp)
  rw [a2r_principalDivisor_apply] at hD
  have hz1 : coheight z = 1 := by
    by_contra hne
    exact hD (Scheme.ord_eq_zero_of_coheight_neq_one hne φ)
  have hheight := (a1p_degree_pos_iff h z).mp (Nat.pos_of_ne_zero hdeg)
  have hz' : h.left z = y := hz
  rw [← hz', hheight, ← hz1]
  exact a2r_height_add_coheight W z

end fibres

/-! ## Transcendence degrees -/

section trdeg

open scoped IntermediateField

variable {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
  [IsScalarTower ℂ K L] [Algebra.EssFiniteType ℂ L]

/-- Equal transcendence degrees over `ℂ` make a finitely generated extension finite. -/
theorem a2r_finiteDimensional_of_trdeg {n : ℕ} (hK : Algebra.trdeg ℂ K = n)
    (hL : Algebra.trdeg ℂ L = n) : FiniteDimensional K L := by
  have hadd := trdeg_add_eq ℂ K (A := L)
  rw [hK, hL] at hadd
  have hlt : Algebra.trdeg K L < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_add_self.trans hadd.le) (Cardinal.natCast_lt_aleph0 (n := n))
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp hlt
  rw [ht] at hadd
  have : n + t = n := by exact_mod_cast hadd
  have ht0 : t = 0 := by omega
  rw [ht0, Nat.cast_zero, trdeg_eq_zero_iff] at ht
  exact a1d_finite_of_isAlgebraic (k := ℂ)

/-- In a function field of one variable over `K`, the field is finite over `K(t)` for every
transcendental `t`. -/
theorem a2r_finiteDimensional_adjoin_of_trdeg {m : ℕ} (hK : Algebra.trdeg ℂ K = m)
    (hL : Algebra.trdeg ℂ L = m + 1) (t : L) (ht : Transcendental K t) :
    FiniteDimensional K⟮t⟯ L := by
  have hadd := trdeg_add_eq ℂ K (A := L)
  rw [hK, hL] at hadd
  have hKL : Algebra.trdeg K L = 1 := by
    have hlt : Algebra.trdeg K L < Cardinal.aleph0 :=
      lt_of_le_of_lt (le_add_self.trans hadd.le)
        (by exact_mod_cast (Cardinal.natCast_lt_aleph0 : ((m + 1 : ℕ) : Cardinal) < _))
    obtain ⟨s, hs⟩ := Cardinal.lt_aleph0.mp hlt
    rw [hs] at hadd ⊢
    have : m + s = m + 1 := by exact_mod_cast hadd
    have hs1 : s = 1 := by omega
    rw [hs1, Nat.cast_one]
  have hadd2 := trdeg_add_eq K K⟮t⟯ (A := L)
  have htr : Transcendental K (IntermediateField.AdjoinSimple.gen K t) := by
    intro halg
    apply ht
    have := halg.algHom (IsScalarTower.toAlgHom K K⟮t⟯ L)
    simpa using this
  have : Algebra.Transcendental K K⟮t⟯ := ⟨⟨_, htr⟩⟩
  have hpos : 0 < Algebra.trdeg K K⟮t⟯ := trdeg_pos K K⟮t⟯
  rw [hKL] at hadd2
  have hlt1 : Algebra.trdeg K K⟮t⟯ < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_self_add.trans hadd2.le) Cardinal.one_lt_aleph0
  have hlt2 : Algebra.trdeg K⟮t⟯ L < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_add_self.trans hadd2.le) Cardinal.one_lt_aleph0
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.mp hlt1
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.mp hlt2
  rw [ha, hb] at hadd2
  rw [ha] at hpos
  have h1 : a + b = 1 := by exact_mod_cast hadd2
  have h2 : 0 < a := by exact_mod_cast hpos
  have hb0 : b = 0 := by omega
  rw [hb0, Nat.cast_zero, trdeg_eq_zero_iff] at hb
  have : IsScalarTower ℂ K⟮t⟯ L := IsScalarTower.of_algebraMap_eq fun c => rfl
  exact a1d_finite_of_isAlgebraic (k := ℂ)

end trdeg

/-! ## Fulton's Proposition 1.4 -/

section fulton

variable {W V : Over (Spec ↧ℂ)} [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
  [IsIntegral W.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsIntegral V.left]
  (h : W ⟶ V) [IsProper h.left] (hdom : h.left (genericPoint W.left) = genericPoint V.left)

include hdom in
/-- **Proper pushforward of a principal cycle, equal dimensions.** For a proper dominant `h`
between integral schemes of finite type over `ℂ` of the same dimension,
`h_*[div φ] = [div N(φ)]`, with `N` the norm of `K(W) / K(V)`.
Source: Fulton, *Intersection Theory*, second edition, Proposition 1.4 (b). -/
theorem a2r_pushforward_principal_of_height_eq
    (hdim : height (genericPoint V.left) = height (genericPoint W.left))
    {φ : W.left.functionField} (hφ : φ ≠ 0) :
    ∃ ψ : V.left.functionField, ψ ≠ 0 ∧
      a1p_pushforward h.left (principalDivisor W.left φ : AlgebraicCycle W.left ℤ) =
        (principalDivisor V.left ψ : AlgebraicCycle V.left ℤ) := by
  classical
  let := (a2r_ffHom h.left hdom).toAlgebra
  let := (a2r_ffC V).toAlgebra
  let := (a2r_ffC W).toAlgebra
  have : IsScalarTower ℂ V.left.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (a2r_ffHom_ffC h hdom c).symm
  obtain ⟨hessW, nW, hnW, htrW⟩ := a2r_ff_trdeg W
  obtain ⟨-, nV, hnV, htrV⟩ := a2r_ff_trdeg V
  have hnn : nV = nW := by
    rw [hnV, hnW] at hdim
    exact_mod_cast hdim
  have : FiniteDimensional V.left.functionField W.left.functionField :=
    a2r_finiteDimensional_of_trdeg (n := nW) (hnn ▸ htrV) htrW
  have : CharZero V.left.functionField :=
    charZero_of_injective_algebraMap (algebraMap ℂ V.left.functionField).injective
  set ψ := Algebra.norm V.left.functionField φ
  have hψ : ψ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hφ
  refine ⟨ψ, hψ, ?_⟩
  ext y
  rw [a2r_principalDivisor_apply V.left ψ y]
  by_cases hy1 : coheight y = 1
  · have hyh : height y + 1 = height (genericPoint W.left) := by
      rw [← hdim, ← hy1]
      exact a2r_height_add_coheight V y
    have hfib := a2r_fibre_coheight h y hyh
    let := (a2r_stalkHom h.left hdom y).toAlgebra
    have : IsScalarTower (V.left.presheaf.stalk y) V.left.functionField
        W.left.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨hfinK, hordK⟩ := a2r_ord_eq_finsum (W := V) hy1 hψ
    have hDVR := a2r_isDVR_of_mem_Dom_stalk (W := V) hy1
    have hfinL : ∀ u ∈ a2r_Dom (V.left.presheaf.stalk y) V.left.functionField,
        (a2r_Dom u W.left.functionField).Finite := fun u hu =>
      have := hDVR u hu
      (a2r_vord_norm_eq_finsum V.left.functionField W.left.functionField u).1
    have hDomV : (a2r_DomV h.left hdom y).Finite := by
      refine (hfinK.biUnion hfinL).subset fun v hv => ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨_, a2r_comap_mem_Dom v hv,
        (a2r_mem_Dom_tower_iff _ (a2r_comap_mem_Dom v hv) v).mpr ⟨hv, rfl⟩⟩
    rw [a2r_pushforward_principal_apply h hdom y hφ hfib (hDomV.subset Set.inter_subset_left)]
    change ∑ᶠ v ∈ a2r_Dom (V.left.presheaf.stalk y) W.left.functionField,
      a2r_vord v φ * (a2r_resDeg (V.left.presheaf.stalk y) v : ℤ) = _
    rw [a2r_finsum_tower _ hfinK hfinL, hordK]
    refine finsum_mem_congr rfl fun u hu => ?_
    have := hDVR u hu
    rw [(a2r_vord_norm_eq_finsum V.left.functionField W.left.functionField u).2 φ hφ, mul_comm,
      mul_finsum_mem' _ _ (hfinL u hu)]
    refine finsum_mem_congr rfl fun v hv => ?_
    rw [a2r_resDeg_tower u hu v hv]
    push_cast
    ring
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hy1]
    by_contra hne
    have hyW := a2r_height_of_pushforward_principal_ne_zero h φ y hne
    obtain ⟨a, b, n, ha, hb, hn, hab⟩ := a2r_height_add_coheight_nat (W := V) y
    rw [ha, ← hdim, hn] at hyW
    have : a + 1 = n := by exact_mod_cast hyW
    apply hy1
    rw [hb]
    have : b = 1 := by omega
    rw [this]
    rfl

omit [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [LocallyOfFiniteType V.hom]
  [QuasiCompact V.hom] [IsProper h.left] in
theorem a2r_stalkHom_genericPoint :
    a2r_stalkHom h.left hdom (genericPoint V.left) = a2r_ffHom h.left hdom := by
  ext a
  change a2r_ffHom h.left hdom ((V.left.presheaf.stalkSpecializes _).hom a) = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

omit [QuasiCompact V.hom] in
include hdom in
/-- **Proper pushforward of a principal cycle, dimension drop.** For a proper dominant `h`
between integral schemes of finite type over `ℂ` with `dim V < dim W`, `h_*[div φ] = 0`.
Source: Fulton, *Intersection Theory*, second edition, Proposition 1.4 (b). -/
theorem a2r_pushforward_principal_of_height_ne
    (hdim : height (genericPoint V.left) ≠ height (genericPoint W.left))
    {φ : W.left.functionField} (hφ : φ ≠ 0) :
    a1p_pushforward h.left (principalDivisor W.left φ : AlgebraicCycle W.left ℤ) = 0 := by
  classical
  ext y
  by_contra hne
  have hyW := a2r_height_of_pushforward_principal_ne_zero h φ y hne
  obtain ⟨hessW, nW, hnW, htrW⟩ := a2r_ff_trdeg W
  obtain ⟨-, nV, hnV, htrV⟩ := a2r_ff_trdeg V
  obtain ⟨-, m, hm, -⟩ := a1d_height_eq_trdeg y
  have hle1 : height y ≤ height (genericPoint V.left) :=
    Order.height_mono (Scheme.le_iff_specializes.mpr ((genericPoint_spec V.left).specializes
      trivial))
  have hle2 : height (genericPoint V.left) ≤ height (genericPoint W.left) :=
    hdom ▸ a2r_height_map_le h (genericPoint W.left)
  rw [hm, hnV] at hle1
  rw [hnV, hnW] at hle2
  rw [hm, hnW] at hyW
  rw [hnV, hnW] at hdim
  have h1 : m ≤ nV := by exact_mod_cast hle1
  have h2 : nV ≤ nW := by exact_mod_cast hle2
  have h3 : m + 1 = nW := by exact_mod_cast hyW
  have h4 : nV ≠ nW := fun h => hdim (by rw [h])
  have hmV : m = nV := by omega
  have hyη : y = genericPoint V.left := by
    apply a2r_eq_genericPoint_of_height
    rw [hm, hnV, hmV]
  subst hyη
  have hyh : height (genericPoint V.left) + 1 = height (genericPoint W.left) := by
    rw [hnV, hnW]; exact_mod_cast (show nV + 1 = nW by omega)
  have hfib := a2r_fibre_coheight h (genericPoint V.left) hyh
  let := (a2r_ffHom h.left hdom).toAlgebra
  let := (a2r_ffC V).toAlgebra
  let := (a2r_ffC W).toAlgebra
  have : IsScalarTower ℂ V.left.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (a2r_ffHom_ffC h hdom c).symm
  have : CharZero V.left.functionField :=
    charZero_of_injective_algebraMap (algebraMap ℂ V.left.functionField).injective
  have hfd : ∀ t : W.left.functionField, Transcendental V.left.functionField t →
      FiniteDimensional (IntermediateField.adjoin V.left.functionField {t})
        W.left.functionField := fun t ht =>
    a2r_finiteDimensional_adjoin_of_trdeg (m := nV) htrV
      (by rw [htrW]; exact_mod_cast (show nW = nV + 1 by omega)) t ht
  obtain ⟨hsuppF, hsumF⟩ := a2r_finsum_vord_eq_zero (K := V.left.functionField)
    (L := W.left.functionField) hφ hfd
  have hDomV : a2r_DomV h.left hdom (genericPoint V.left) =
      a2r_Dom V.left.functionField W.left.functionField := by
    unfold a2r_DomV
    rw [a2r_stalkHom_genericPoint h hdom]
  have hresV : ∀ v, a2r_resDegV h.left hdom (genericPoint V.left) v =
      a2r_resDeg V.left.functionField v := by
    intro v
    unfold a2r_resDegV
    rw [a2r_stalkHom_genericPoint h hdom]
  apply hne
  rw [a2r_pushforward_principal_apply h hdom _ hφ hfib (by
    rw [hDomV]
    refine hsuppF.subset fun v ⟨hv, hs⟩ => ⟨hv, ?_⟩
    simpa [hresV] using hs)]
  rw [hDomV]
  simp only [hresV]
  exact hsumF

end fulton

/-! ## Rational equivalence is preserved by proper pushforward -/

section rat

/-- Pushforward commutes with casting integer coefficients. -/
theorem a2r_pushforward_mapRange_intCast {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Ring R] (c : AlgebraicCycle X ℤ) :
    a1p_pushforward f (c.mapRange (Int.cast : ℤ → R) Int.cast_zero) =
      (a1p_pushforward f c).mapRange (Int.cast : ℤ → R) Int.cast_zero := by
  classical
  ext y
  set t := (a1p_fibre_inter_support_finite f c y).toFinset
  have ht : (t : Set X) ⊆ f ⁻¹' {y} := fun x hx =>
    ((Set.Finite.mem_toFinset _).mp hx).1
  rw [Function.locallyFinsuppWithin.mapRange_apply,
    a1p_pushforward_apply_eq_sum f c y t (fun x hx => (Set.Finite.mem_toFinset _).mpr hx) ht,
    a1p_pushforward_apply_eq_sum f _ y t (fun x hx => (Set.Finite.mem_toFinset _).mpr
      ⟨hx.1, fun h0 => hx.2 (by rw [Function.locallyFinsuppWithin.mapRange_apply, h0,
        Int.cast_zero])⟩) ht]
  push_cast
  rfl

instance a2r_component_quasiCompact (X : Over (Spec ↧ℂ)) [QuasiCompact X.hom] (w : X.left) :
    QuasiCompact (a2r_component X w).hom := by
  change QuasiCompact (cycleComponentι X.left w ≫ X.hom)
  infer_instance

/-- The pushforward depends only on the morphism. -/
theorem a2r_pushforward_congr {X Y : Scheme} {f g : X ⟶ Y} [QuasiCompact f] [QuasiCompact g]
    (hfg : f = g) {R : Type*} [Semiring R] (c : AlgebraicCycle X R) :
    a1p_pushforward f c = a1p_pushforward g c := by
  subst hfg
  rfl

/-- The map `f` restricts to the subvarieties `closure {w} → closure {f w}`. -/
theorem a2r_exists_restrict {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (w : X.left) :
    ∃ h : a2r_component X w ⟶ a2r_component Y (f.left w),
      h.left ≫ cycleComponentι Y.left (f.left w) = cycleComponentι X.left w ≫ f.left := by
  have H : (cycleComponentι Y.left (f.left w)).ker ≤ (cycleComponentι X.left w ≫ f.left).ker := by
    rw [Scheme.Hom.ker_comp]
    change (Scheme.IdealSheafData.vanishingIdeal ⟨closure {f.left w}, isClosed_closure⟩).subschemeι.ker
      ≤ (Scheme.IdealSheafData.vanishingIdeal ⟨closure {w}, isClosed_closure⟩).subschemeι.ker.map
        f.left
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    change closure (f.left '' closure {w}) ⊆ closure {f.left w}
    refine closure_minimal ?_ isClosed_closure
    refine (image_closure_subset_closure_image f.left.continuous).trans ?_
    rw [Set.image_singleton]
  let hl := IsClosedImmersion.lift (cycleComponentι Y.left (f.left w))
    (cycleComponentι X.left w ≫ f.left) H
  refine ⟨Over.homMk hl ?_, IsClosedImmersion.lift_fac _ _ _⟩
  change hl ≫ cycleComponentι Y.left (f.left w) ≫ Y.hom = cycleComponentι X.left w ≫ X.hom
  rw [← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, Over.w f]

/-- **Proper pushforward preserves rational equivalence.**
Source: Fulton, *Intersection Theory*, second edition, Theorem 1.4 and Proposition 1.4. -/
theorem a2r_pushforward_ratEquiv {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    [IsProper f.left] (R : Type*) [Ring R] (k : ℕ) (c : AlgebraicCycle X.left R)
    (hc : c ∈ a2_ratEquivDim X.left R k) :
    a1p_pushforward f.left c ∈ a2_ratEquivDim Y.left R k := by
  suffices a2_ratEquivDim X.left R k ≤
      (a2_ratEquivDim Y.left R k).comap (a2_pushforwardHom f.left R) from this hc
  rw [a2_ratEquivDim, AddSubgroup.closure_le]
  rintro _ ⟨w, φ, r, hw, hφ, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  change a1p_pushforward f.left ((a2_principalCycle X.left R w φ).mapRange (r * ·) _) ∈ _
  rw [a1p_pushforward_mul]
  set w' := f.left w with hw'
  obtain ⟨h, hcomm⟩ := a2r_exists_restrict f w
  have : IsProper (cycleComponentι X.left w ≫ f.left) := inferInstance
  have : IsProper (h.left ≫ cycleComponentι Y.left w') := hcomm ▸ this
  have : IsProper h.left := IsProper.of_comp h.left (cycleComponentι Y.left w')
  have hdom : h.left (genericPoint (a2r_component X w).left) =
      genericPoint (a2r_component Y w').left := by
    apply (cycleComponentι Y.left w').isEmbedding.injective
    change (h.left ≫ cycleComponentι Y.left w') _ = _
    rw [hcomm, Scheme.Hom.comp_apply]
    change f.left (cycleComponentι X.left w (genericPoint (cycleComponent X.left w))) =
      cycleComponentι Y.left w' (genericPoint (cycleComponent Y.left w'))
    rw [a2r_cycleComponentι_genericPoint, a2r_cycleComponentι_genericPoint]
  rw [a2_principalCycle, a2r_pushforward_mapRange_intCast, ← a1p_pushforward_comp,
    a2r_pushforward_congr hcomm.symm, a1p_pushforward_comp]
  by_cases heq : height (genericPoint (a2r_component Y w').left) =
    height (genericPoint (a2r_component X w).left)
  · obtain ⟨ψ, hψ, hψeq⟩ := a2r_pushforward_principal_of_height_eq h hdom heq hφ
    change a1p_pushforward h.left (principalDivisor (cycleComponent X.left w) φ :
      AlgebraicCycle (cycleComponent X.left w) ℤ) = _ at hψeq
    rw [hψeq]
    refine AddSubgroup.subset_closure ⟨w', ψ, r, ?_, hψ, rfl⟩
    change height (genericPoint (cycleComponent Y.left w')) =
      height (genericPoint (cycleComponent X.left w)) at heq
    rw [← a2r_height_cycleComponent_genericPoint, heq, a2r_height_cycleComponent_genericPoint, hw]
  · have h0 := a2r_pushforward_principal_of_height_ne h hdom heq hφ
    change a1p_pushforward h.left (principalDivisor (cycleComponent X.left w) φ :
      AlgebraicCycle (cycleComponent X.left w) ℤ) = 0 at h0
    rw [h0, show a1p_pushforward (cycleComponentι Y.left w') (0 : AlgebraicCycle _ ℤ) = 0 from
      (a2_pushforwardHom (cycleComponentι Y.left w') ℤ).map_zero]
    convert (a2_ratEquivDim Y.left R k).zero_mem
    ext y
    simp [Function.locallyFinsuppWithin.mapRange_apply]

end rat

end HodgeLean.Adapters
