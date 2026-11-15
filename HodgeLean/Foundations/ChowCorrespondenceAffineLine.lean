import HodgeLean.Foundations.ChowCorrespondenceRat
import HodgeLean.Foundations.Curves.ChartStalks

/-! # The origin of the affine line is rationally equivalent to zero

Helpers for lane A2 (rational equivalence). For the generic point `η` of `𝔸¹ = Spec ℂ[X]`, the
closed immersion `cycleComponentι 𝔸¹ η` is surjective onto a reduced scheme, hence an isomorphism;
its inverse is an affine chart of `closure {η}`. Through it, the coordinate function `x` has
order `1` at the origin (a DVR stalk with uniformizer `x`) and order `0` elsewhere (`x` is a unit
in the stalk). So `[div x] = [0]`, and `[0] ∈ Rat_0(𝔸¹)`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial HodgeLean.Foundations.Curves Order
open HodgeLean.Foundations.Curves.ChartStalks
namespace HodgeLean.Adapters

local notation "𝔸" => Spec (CommRingCat.of ℂ[X])

/-- The origin `(X)` is a maximal ideal of `ℂ[X]`. -/
theorem a2r_origin_isMax : Ideal.IsMaximal (Ideal.span {(X : ℂ[X])}) :=
  PrincipalIdealRing.isMaximal_of_irreducible irreducible_X

/-- `closure {η}` is all of `𝔸¹`. -/
instance a2r_ι_surjective :
    Surjective (cycleComponentι 𝔸 (genericPoint 𝔸)) := by
  constructor
  rw [← Set.range_eq_univ, range_cycleComponentι, (genericPoint_spec 𝔸).def]

/-- `closure {η} → 𝔸¹` is an isomorphism. -/
instance a2r_ι_isIso : IsIso (cycleComponentι 𝔸 (genericPoint 𝔸)) :=
  isIso_of_isClosedImmersion_of_surjective _

local notation "W" => cycleComponent 𝔸 (genericPoint 𝔸)
local notation "ι" => cycleComponentι 𝔸 (genericPoint 𝔸)

/-- The coordinate function on `closure {η} = 𝔸¹`. -/
def a2r_coord : Γ(W, ⊤) := Scheme.Hom.appTop ι ((Scheme.ΓSpecIso (CommRingCat.of ℂ[X])).inv X)

/-- The inverse chart pulls the coordinate back to `X`. -/
theorem a2r_coord_app : (inv ι).app ⊤ a2r_coord =
    (𝔸).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso (CommRingCat.of ℂ[X])).inv X) := by
  have h : (inv ι).app ⊤ a2r_coord = (inv ι ≫ ι).app ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ[X])).inv X) := rfl
  rw [h, Scheme.Hom.congr_app (IsIso.inv_hom_id ι) ⊤]
  rfl

instance a2r_top_nonempty : Nonempty (⊤ : (W).Opens) := ⟨⟨genericPoint W, trivial⟩⟩

/-- The coordinate function `x` as a rational function on `closure {η}`. -/
def a2r_coordFun : (W).functionField := (W).germToFunctionField ⊤ a2r_coord

/-- The origin of `𝔸¹` as a point of `Spec ℂ[X]`. -/
def a2r_origin : 𝔸 := ⟨Ideal.span {X}, a2r_origin_isMax.isPrime⟩

/-- Through the chart at `t`, `x` is the image of `X ∈ ℂ[X]` in the stalk. -/
theorem a2r_coordFun_eq (t : 𝔸) :
    letI := chartStalkAlgebra (inv ι) t
    a2r_coordFun = algebraMap ((W).presheaf.stalk ((inv ι) t)) (W).functionField
      (algebraMap ℂ[X] _ X) :=
  germToFunctionField_eq (inv ι) a2r_coord X a2r_coord_app t trivial

/-- `ord_0(x) = 1`. -/
theorem a2r_ord_origin : (W).ord a2r_coordFun ((inv ι) a2r_origin) = 1 := by
  let _ := chartStalkAlgebra (inv ι) a2r_origin
  have : a2r_origin.asIdeal.IsPrime := a2r_origin.isPrime
  have := chartStalk_isLocalization (inv ι) a2r_origin
  have hX0 : algebraMap ℂ[X] ((W).presheaf.stalk ((inv ι) a2r_origin)) X ≠ 0 := by
    intro h
    have := IsLocalization.injective ((W).presheaf.stalk ((inv ι) a2r_origin))
      (M := (a2r_origin.asIdeal).primeCompl) (Ideal.primeCompl_le_nonZeroDivisors _)
    exact X_ne_zero (this (h.trans (map_zero _).symm))
  obtain ⟨hdvr, hirr⟩ := dvr_of_span (A := ℂ[X]) a2r_origin.asIdeal
    ((W).presheaf.stalk ((inv ι) a2r_origin)) X X (by simp [a2r_origin])
    (Ideal.subset_span rfl) (Ideal.subset_span rfl) hX0
  have hf : a2r_coordFun ≠ 0 := by
    rw [a2r_coordFun_eq a2r_origin]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hX0
  refine ord_eq_of_dvr _ hf 1 ?_
  rw [a2r_coordFun_eq a2r_origin]
  exact Ring.ordFrac_irreducible hirr

/-- `x ≠ 0`. -/
theorem a2r_coordFun_ne_zero : a2r_coordFun ≠ 0 := by
  intro h
  have := a2r_ord_origin
  rw [h, Scheme.ord_zero] at this
  exact zero_ne_one this

/-- A prime of `ℂ[X]` containing `X` is the origin. -/
theorem a2r_eq_origin_of_X_mem (t : 𝔸) (h : (X : ℂ[X]) ∈ t.asIdeal) : t = a2r_origin := by
  apply PrimeSpectrum.ext
  exact (a2r_origin_isMax.eq_of_le t.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr h)).symm

/-- Away from the origin `x` has order `0`. -/
theorem a2r_ord_of_ne (t : 𝔸) (ht : t ≠ a2r_origin) : (W).ord a2r_coordFun ((inv ι) t) = 0 := by
  by_cases hz : coheight ((inv ι) t) = 1
  · rw [Scheme.ord_eq_iff hz a2r_coordFun_ne_zero]
    let _ := chartStalkAlgebra (inv ι) t
    have : t.asIdeal.IsPrime := t.isPrime
    have := chartStalk_isLocalization (inv ι) t
    have hu : IsUnit (algebraMap ℂ[X] ((W).presheaf.stalk ((inv ι) t)) X) :=
      IsLocalization.map_units _ (⟨X, fun h => ht (a2r_eq_origin_of_X_mem t h)⟩ :
        t.asIdeal.primeCompl)
    have : Ring.KrullDimLE 1 ((W).presheaf.stalk ((inv ι) t)) := krullDimLE_of_coheight_le hz.le
    unfold Scheme.ordHom
    rw [a2r_coordFun_eq t]
    exact Ring.ordFrac_of_isUnit hu
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _

theorem a2r_inv_ι_apply (z : W) : (inv ι) (ι z) = z := by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
  rfl

theorem a2r_ι_inv_apply (t : 𝔸) : ι ((inv ι) t) = t := by
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

/-- `[div x] = [0]` on `closure {η}`. -/
theorem a2r_principalDivisor_coordFun [DecidableEq W] :
    (principalDivisor W a2r_coordFun : AlgebraicCycle W ℤ) =
      Function.locallyFinsuppWithin.single ((inv ι) a2r_origin) 1 := by
  have hval : ∀ z : W, ordAt W a2r_coordFun z = if z = (inv ι) a2r_origin then 1 else 0 := by
    intro z
    change (W).ord a2r_coordFun z = _
    rw [← a2r_inv_ι_apply z]
    by_cases h : ι z = a2r_origin
    · rw [h, a2r_ord_origin]
      simp
    · have h' : ¬ (inv ι) (ι z) = (inv ι) a2r_origin := fun h' =>
        h (by simpa [a2r_ι_inv_apply] using congrArg ι h')
      rw [a2r_ord_of_ne _ h]
      simp [h']
  have hfin : (Function.support (ordAt W a2r_coordFun)).Finite :=
    (Set.finite_singleton ((inv ι) a2r_origin)).subset fun z hz => by
      by_contra h
      exact hz (by simpa [hval] using h)
  ext z
  rw [Function.locallyFinsuppWithin.single_apply]
  unfold principalDivisor
  simp only [hfin, ↓reduceDIte]
  change ordAt W a2r_coordFun z = _
  rw [hval]

/-- The isomorphism `closure {η} → 𝔸¹` has degree `1` everywhere. -/
theorem a2r_degree_ι (z : W) : a1p_degree ι z = 1 :=
  a1x_degree_eq_one_of_surjective _ _
    (ConcreteCategory.bijective_of_isIso (Scheme.Hom.residueFieldMap ι z)).2

/-- The origin is a closed point, of height `0`. -/
theorem a2r_height_origin : height a2r_origin = 0 := by
  rw [height_eq_zero]
  intro y hy
  rw [Scheme.le_iff_specializes] at hy ⊢
  have hc : IsClosed ({a2r_origin} : Set 𝔸) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr a2r_origin_isMax
  have : y = a2r_origin := by
    have := hy.mem_closed hc rfl
    exact this
  rw [this]

/-- The generic point of `𝔸¹` has height `1`. -/
theorem a2r_height_genericPoint : height (genericPoint 𝔸) = 1 := by
  have hcoh : coheight ((inv ι) a2r_origin) = 1 := by
    by_contra h
    have := a2r_ord_origin
    rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at this
    exact zero_ne_one this
  have := a2r_component_locallyOfFiniteType a1p_affineLine (genericPoint 𝔸)
  have := a2r_component_isIntegral a1p_affineLine (genericPoint 𝔸)
  have hsum := a2r_height_add_coheight (a2r_component a1p_affineLine (genericPoint 𝔸))
    ((inv ι) a2r_origin)
  change height ((inv ι) a2r_origin) + coheight ((inv ι) a2r_origin) =
    height (genericPoint W) at hsum
  rw [a2r_height_cycleComponent_genericPoint, hcoh, ← a2r_height_cycleComponentι,
    a2r_ι_inv_apply, a2r_height_origin, zero_add] at hsum
  exact hsum.symm

/-- `[0] ∈ Rat_0(𝔸¹)`: it is `[div x]`.
Source: Hartshorne, *Algebraic Geometry*, II.6, Example 6.2.1. -/
theorem a2r_affineLineOrigin_mem_ratEquivDim [h : DecidableEq a1p_affineLine.left] :
    Function.locallyFinsuppWithin.single a2_affineLineOrigin (1 : ℤ) ∈
      a2_ratEquivDim a1p_affineLine.left ℤ 0 := by
  let _ : DecidableEq 𝔸 := h
  change Function.locallyFinsuppWithin.single a2r_origin (1 : ℤ) ∈ a2_ratEquivDim 𝔸 ℤ 0
  let _ : DecidableEq W := Classical.decEq _
  refine AddSubgroup.subset_closure ⟨genericPoint 𝔸, a2r_coordFun, 1,
    by rw [a2r_height_genericPoint]; rfl, a2r_coordFun_ne_zero, ?_⟩
  ext p
  change _ = 1 * ((a1p_pushforward ι (principalDivisor W a2r_coordFun :
    AlgebraicCycle W ℤ) p : ℤ) : ℤ)
  rw [a2r_principalDivisor_coordFun, a1p_pushforward_single, a2r_degree_ι, a2r_ι_inv_apply,
    Nat.cast_one, mul_one, one_mul]

end HodgeLean.Adapters
