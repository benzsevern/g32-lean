import HodgeLean.Foundations.Program.SchoenTowerCoverStalk
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

theorem s2v_finite_locallyConstant_extension {X A : Type*}
    [TopologicalSpace X] [T2Space X] (K : Set X) (hK : K.Finite) (a : K → A) :
    ∃ (U : Opens X) (hKU : K ⊆ U), ∃ s : LocallyConstant U A,
      ∀ x : K, s ⟨x.val, hKU x.property⟩ = a x := by
  classical
  obtain ⟨O, hO, hdis⟩ := hK.t2_separation
  let V : Set X := ⋃ x : K, O x.val
  have hV : IsOpen V := isOpen_iUnion fun x => (hO x.val).2
  have hKV : K ⊆ V := fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hO x).1⟩
  have hex (x : V) : ∃ k : K, x.val ∈ O k.val := Set.mem_iUnion.mp x.property
  choose k hk using hex
  have heq (x : V) (z : K) (hx : x.val ∈ O z.val) : k x = z := by
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hdis (k x).property z.property hne) (hk x) hx
  let s : LocallyConstant V A := ⟨fun x => a (k x), by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro x
    refine ⟨Subtype.val ⁻¹' O (k x).val,
      (hO (k x).val).2.preimage continuous_subtype_val, hk x, ?_⟩
    intro z hz
    exact congrArg a (heq z (k x) hz)⟩
  refine ⟨⟨V, hV⟩, hKV, s, ?_⟩
  intro x
  exact congrArg a (heq ⟨x.val, hKV x.property⟩ x (hO x.val).1)

theorem s2v_coverStalkEvaluation_surjective {X E : TopCat}
    [T2Space X] (f : X ⟶ E) (hf : IsProperMap f) (y : E)
    (hfin : Set.Finite {x : X | f x = y}) :
    Function.Surjective (s2v_coverStalkEvaluation f y) := by
  intro a
  obtain ⟨O, hKO, s, hs⟩ :=
    s2v_finite_locallyConstant_extension {x : X | f x = y} hfin a
  obtain ⟨V, hV, hyV, hVO⟩ := s3_fibre_neighborhood f hf y O O.isOpen hKO
  let U : Opens E := ⟨V, hV⟩
  let inc : {x : X // f x ∈ U} → O := fun x => ⟨x.val, hVO x.property⟩
  have hi : Continuous inc := continuous_subtype_val.subtype_mk _
  let t : LocallyConstant {x : X // f x ∈ U} ℂ := s.comap ⟨inc, hi⟩
  refine ⟨(s2c_coverPresheaf f).germ U y hyV t, ?_⟩
  funext x
  rw [s2v_coverStalkEvaluation_germ]
  exact hs x

def s2v_coverStalkEquiv_finite_fibre {X E : TopCat}
    [T2Space X] (f : X ⟶ E) (hf : IsProperMap f) (y : E)
    (hfin : Set.Finite {x : X | f x = y}) :
    (s2c_coverPresheaf f).stalk y ≃+ ({x : X // f x = y} → ℂ) :=
  AddEquiv.ofBijective (s2v_coverStalkEvaluation f y).hom
    ⟨s2v_coverStalkEvaluation_injective f hf y,
      s2v_coverStalkEvaluation_surjective f hf y hfin⟩

def s2v_coverSheafStalkEquiv_finite_fibre {X E : TopCat}
    [T2Space X] (f : X ⟶ E) (hf : IsProperMap f) (y : E)
    (hfin : Set.Finite {x : X | f x = y}) :
    ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := E) (s2c_coverSheaf f).obj y) ≃+
      ({x : X // f x = y} → ℂ) := by
  let J := Opens.grothendieckTopology E
  let τ : s2c_coverPresheaf f ⟶ (s2c_coverSheaf f).obj := toSheafify J _
  letI : IsIso τ := s2v_coverPresheaf_toSheafify_isIso f
  let φ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map τ
  haveI : IsIso φ := inferInstance
  let e := AddEquiv.ofBijective φ.hom
    ((ConcreteCategory.isIso_iff_bijective φ).mp inferInstance)
  exact e.symm.trans (s2v_coverStalkEquiv_finite_fibre f hf y hfin)

end HodgeLean.Foundations.Program
