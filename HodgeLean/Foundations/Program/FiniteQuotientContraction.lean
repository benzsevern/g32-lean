module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Contractions through orbit quotients
A fibre-preserving contraction descends through an open quotient map.
-/
public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The quotient inherits a contraction when each time slice preserves fibres.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3, universal property of orbit quotients. -/
theorem open_quotient_contractible_of_fibre_preserving_contraction
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (q : C(A, B)) (hq : IsOpenQuotientMap q) (x₀ : A)
    (H : ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A x₀))
    (hH : ∀ (t : unitInterval) (x y : A), q x = q y → q (H (t, x)) = q (H (t, y))) :
    ContractibleSpace B := by
  let p : C(unitInterval × A, unitInterval × B) :=
    ⟨Prod.map id q, continuous_id.prodMap q.continuous⟩
  have hp : Topology.IsQuotientMap p :=
    (IsOpenQuotientMap.id.prodMap hq).isQuotientMap
  let h : C(unitInterval × A, B) := q.comp H.toContinuousMap
  have hfac : Function.FactorsThrough h p := by
    rintro ⟨t, x⟩ ⟨s, y⟩ he
    have ht : t = s := congrArg Prod.fst he
    have hx : q x = q y := congrArg Prod.snd he
    subst s
    exact hH t x y hx
  let K := hp.lift h hfac
  have hK (t : unitInterval) (x : A) : K (t, q x) = q (H (t, x)) := by
    exact ContinuousMap.congr_fun (hp.lift_comp h hfac) (t, x)
  let KH : ContinuousMap.Homotopy (ContinuousMap.id B)
      (ContinuousMap.const B (q x₀)) := {
    toContinuousMap := K
    map_zero_left := by
      intro y
      obtain ⟨x, rfl⟩ := hq.surjective y
      change K (0, q x) = q x
      rw [hK]
      exact congrArg q (H.map_zero_left x)
    map_one_left := by
      intro y
      obtain ⟨x, rfl⟩ := hq.surjective y
      change K (1, q x) = q x₀
      rw [hK]
      exact congrArg q (H.map_one_left x) }
  exact (contractible_iff_id_nullhomotopic B).mpr ⟨q x₀, ⟨KH⟩⟩

/-- An equivariant contraction contracts the orbit space, with stabilizers allowed.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3, homotopies on orbit spaces. -/
theorem orbit_quotient_contractible_of_equivariant_contraction
    (G : Type*) [Group G] (A : Type*) [TopologicalSpace A]
    [MulAction G A] [ContinuousConstSMul G A] (x₀ : A)
    (H : ContinuousMap.Homotopy (ContinuousMap.id A) (ContinuousMap.const A x₀))
    (hH : ∀ (t : unitInterval) (g : G) (x : A), H (t, g • x) = g • H (t, x)) :
    ContractibleSpace (MulAction.orbitRel.Quotient G A) := by
  letI : Setoid A := MulAction.orbitRel G A
  let q : C(A, MulAction.orbitRel.Quotient G A) :=
    ⟨Quotient.mk', continuous_quotient_mk'⟩
  apply open_quotient_contractible_of_fibre_preserving_contraction q
    (MulAction.isOpenQuotientMap_quotientMk) x₀ H
  intro t x y he
  have hr := Quotient.exact he
  change ∃ g : G, g • y = x at hr
  obtain ⟨g, rfl⟩ := hr
  rw [hH]
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

/-- Radial contraction contracts the quotient of an invariant star-convex set.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3; Hatcher, Algebraic Topology, Chapter 0, radial contractions. -/
theorem starConvex_subMulAction_orbit_quotient_contractible
    (G : Type*) [Group G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MulAction G E] [ContinuousConstSMul G E] [SMulCommClass ℝ G E]
    (S : SubMulAction G E) (hzero : (0 : E) ∈ S) (hstar : StarConvex ℝ (0 : E) (S : Set E)) :
    ContractibleSpace (MulAction.orbitRel.Quotient G S) := by
  letI : ContinuousConstSMul G S := ⟨fun g =>
    (show Continuous (fun x : S => g • (x : E)) from
      (continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
  let x₀ : S := ⟨0, hzero⟩
  let radial : unitInterval × S → S := fun p =>
    ⟨(1 - (p.1 : ℝ)) • (p.2 : E), hstar.smul_mem p.2.property
      (sub_nonneg.mpr p.1.property.2) (sub_le_self 1 p.1.property.1)⟩
  have hc : Continuous (fun p : unitInterval × S => (1 - (p.1 : ℝ)) • (p.2 : E)) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)
  let H : ContinuousMap.Homotopy (ContinuousMap.id S) (ContinuousMap.const S x₀) := {
    toContinuousMap := ⟨radial, hc.subtype_mk _⟩
    map_zero_left := by
      intro x
      apply Subtype.ext
      change (1 - (0 : ℝ)) • (x : E) = (x : E)
      rw [sub_zero, one_smul]
    map_one_left := by
      intro x
      apply Subtype.ext
      change (1 - (1 : ℝ)) • (x : E) = 0
      rw [sub_self, zero_smul] }
  apply orbit_quotient_contractible_of_equivariant_contraction G S x₀ H
  intro t g x
  apply Subtype.ext
  change (1 - (t : ℝ)) • (g • (x : E)) = g • ((1 - (t : ℝ)) • (x : E))
  exact smul_comm _ _ _

/-- Radial contraction in an equivariant star-convex coordinate image gives an
actual equivariant contraction on the source domain.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3; Hatcher, Algebraic Topology, Chapter 0, radial contractions. -/
theorem equivariant_chart_radial_contraction
    (G : Type*) [Group G] {A E : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MulAction G A]
    (S : SubMulAction G A) (e : OpenPartialHomeomorph A E)
    (hS : (S : Set A) ⊆ e.source) (x₀ : S) (hezero : e x₀ = 0)
    (hstar : StarConvex ℝ (0 : E) (e '' (S : Set A)))
    (ρ : G →* (E ≃L[ℝ] E))
    (hequiv : ∀ g (x : S), e (g • (x : A)) = ρ g (e x)) :
    ∃ H : ContinuousMap.Homotopy (ContinuousMap.id S) (ContinuousMap.const S x₀),
      ∀ (t : unitInterval) (g : G) (x : S), H (t, g • x) = g • H (t, x) := by
  let h := e.homeomorphOfImageSubsetSource hS rfl
  have hc : Continuous (fun p : unitInterval × S => (1 - (p.1 : ℝ)) • (h p.2 : E)) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      ((continuous_subtype_val.comp h.continuous).comp continuous_snd)
  let R : C(unitInterval × S, (e '' (S : Set A))) :=
    ⟨fun p => ⟨(1 - (p.1 : ℝ)) • (h p.2 : E),
      hstar.smul_mem (h p.2).property (sub_nonneg.mpr p.1.property.2)
        (sub_le_self 1 p.1.property.1)⟩, hc.subtype_mk _⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id S) (ContinuousMap.const S x₀) := {
    toContinuousMap := ⟨fun p => h.symm (R p), h.symm.continuous.comp R.continuous⟩
    map_zero_left := by
      intro x
      apply h.injective
      change h (h.symm (R (0, x))) = h x
      rw [h.apply_symm_apply]
      apply Subtype.ext
      change (1 - (0 : ℝ)) • e x = e x
      rw [sub_zero, one_smul]
    map_one_left := by
      intro x
      apply h.injective
      change h (h.symm (R (1, x))) = h x₀
      rw [h.apply_symm_apply]
      apply Subtype.ext
      change (1 - (1 : ℝ)) • e x = e x₀
      rw [sub_self, zero_smul, hezero] }
  have hval (t : unitInterval) (x : S) :
      e (H (t, x) : A) = (1 - (t : ℝ)) • e x := by
    change (h (h.symm (R (t, x))) : E) = _
    rw [h.apply_symm_apply]
    rfl
  refine ⟨H, ?_⟩
  intro t g x
  apply h.injective
  apply Subtype.ext
  change e (H (t, g • x) : A) = e (g • (H (t, x) : A))
  rw [hval]
  change (1 - (t : ℝ)) • e (g • (x : A)) = e (g • (H (t, x) : A))
  rw [hequiv g x, hequiv g (H (t, x)), hval]
  exact (map_smul (ρ g) (1 - (t : ℝ)) (e x)).symm

end HodgeLean.Foundations.Program
