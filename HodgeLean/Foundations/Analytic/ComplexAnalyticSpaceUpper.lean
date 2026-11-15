import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceBase
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFibreDim

/-! # Manifold pieces near a point have at most the Krull dimension there

Helpers prefixed `anb_`. Near `p`, a locally analytic set `B ⊆ ℂⁿ` is the union of the zero sets
of the minimal primes of the vanishing ideal of its germ (`adim3_minimal_prime_cover`); each
projects with finite fibres onto a space of dimension the Krull dimension of the prime
(`adim5_finite_parameters`, `adim6_confined_projection`). A manifold piece of `B` near `p` has an
open part inside one of them (finitely many relatively closed sets cover an open set), so it maps
with finite fibres to that space, which bounds its dimension (`anb_le_of_finite_fibres`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- A finite infimum of germs of propositions is the germ of the conjunction. -/
theorem anb_germ_finset_inf {α ι : Type*} {l : Filter α} (t : Finset ι) (P : ι → α → Prop) :
    t.inf (fun j ↦ (Filter.Germ.ofFun (P j) : Filter.Germ l Prop)) =
      Filter.Germ.ofFun (fun z ↦ ∀ j ∈ t, P j z) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty]
    exact (Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)).symm
  | insert a t ha ih =>
    rw [Finset.inf_insert, ih]
    exact Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)

/-- A finite supremum of germs of propositions is the germ of the disjunction. -/
theorem anb_germ_finset_sup {α ι : Type*} {l : Filter α} (t : Finset ι) (P : ι → α → Prop) :
    t.sup (fun j ↦ (Filter.Germ.ofFun (P j) : Filter.Germ l Prop)) =
      Filter.Germ.ofFun (fun z ↦ ∃ j ∈ t, P j z) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact (Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)).symm
  | insert a t ha ih =>
    rw [Finset.sup_insert, ih]
    exact Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)

/-- A chosen representative of an analytic germ. -/
def anb_rep {n : ℕ} (g : AnalyticGerm n) : (Fin n → ℂ) → ℂ := g.property.choose

theorem anb_rep_analyticAt {n : ℕ} (g : AnalyticGerm n) : AnalyticAt ℂ (anb_rep g) 0 :=
  g.property.choose_spec.1

theorem anb_rep_germ {n : ℕ} (g : AnalyticGerm n) : Filter.Germ.ofFun (anb_rep g) = g.val :=
  g.property.choose_spec.2

theorem anb_zero_eq {n : ℕ} (g : AnalyticGerm n) :
    adim2_zero n g = Filter.Germ.ofFun (fun z ↦ anb_rep g z = 0) := by
  rw [adim2_zero, ← anb_rep_germ g]
  rfl

/-- If finitely many sets, each relatively closed in an open nonempty `V`, cover `V`, one of them
contains an open nonempty subset of `V`. -/
theorem anb_exists_open_of_finite_cover {E ι : Type*} [TopologicalSpace E] (t : Finset ι)
    (C : ι → Set E) : ∀ {V : Set E}, IsOpen V → V.Nonempty → (∀ i ∈ t, IsOpen (V \ C i)) →
      V ⊆ ⋃ i ∈ t, C i → ∃ i ∈ t, ∃ V' : Set E, IsOpen V' ∧ V'.Nonempty ∧ V' ⊆ V ∧ V' ⊆ C i := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro V _ hne _ hcov
    obtain ⟨v, hv⟩ := hne
    simpa using hcov hv
  | insert a t ha ih =>
    intro V hV hne hC hcov
    by_cases h : V ⊆ C a
    · exact ⟨a, Finset.mem_insert_self a t, V, hV, hne, subset_rfl, h⟩
    · obtain ⟨v, hvV, hva⟩ := not_subset.1 h
      obtain ⟨i, hi, V', hV', hne', hV'V, hV'C⟩ := ih (hC a (Finset.mem_insert_self a t))
        ⟨v, hvV, hva⟩
        (fun i hi ↦ by
          have : (V \ C a) \ C i = (V \ C i) ∩ (V \ C a) := by
            ext x; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
          rw [this]
          exact (hC i (Finset.mem_insert_of_mem hi)).inter (hC a (Finset.mem_insert_self a t)))
        (fun x hx ↦ by
          have := hcov hx.1
          simp only [Finset.mem_insert, mem_iUnion, exists_prop] at this
          obtain ⟨j, hj | hj, hxj⟩ := this
          · exact absurd (hj ▸ hxj) hx.2
          · exact mem_biUnion hj hxj)
      exact ⟨i, Finset.mem_insert_of_mem hi, V', hV', hne', hV'V.trans sdiff_subset, hV'C⟩

/-- **A prime germ projects with finite fibres.** For a prime `P` of the analytic germs, a
representative of its zero germ on an open `W ∋ 0` maps by a linear `π` to `ℂ^{d}` with finite
fibres, where `d` is the Krull dimension of `𝒪/P`. -/
theorem anb_prime_projection {n : ℕ} (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime) :
    ∃ (dP : ℕ) (π : (Fin n → ℂ) →L[ℂ] (Fin dP → ℂ)) (W : Set (Fin n → ℂ)) (m : ℕ)
      (f : Fin m → (Fin n → ℂ) → ℂ),
      IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ (∀ j, ContinuousOn (f j) W) ∧
      adim2_zeroSet n P = Filter.Germ.ofFun (fun z ↦ ∀ j, f j z = 0) ∧
      (∀ w, {z | z ∈ W ∧ (∀ j, f j z = 0) ∧ π z = w}.Finite) ∧
      ((dP : ℕ∞) : WithBot ℕ∞) = ringKrullDim (AnalyticGerm n ⧸ P) := by
  obtain ⟨dP, π, θ, -, hfinite, -, hcomp, hdim⟩ := adim5_finite_parameters n P hP
  set gs := adim2_generators n P
  have hgs : Ideal.span (gs : Set (AnalyticGerm n)) = P :=
    ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) P).choose_spec
  let m := gs.card
  let e := gs.equivFin
  let g : Fin m → AnalyticGerm n := fun j ↦ (e.symm j).1
  have hrange : Set.range g = (gs : Set (AnalyticGerm n)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact (e.symm j).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp [g]⟩
  have hgen : Ideal.span (Set.range g) = P := by rw [hrange, hgs]
  let f : Fin m → (Fin n → ℂ) → ℂ := fun j ↦ anb_rep (g j)
  let U := ⋂ j, {z | AnalyticAt ℂ (f j) z}
  have hU : IsOpen U := isOpen_iInter_of_finite fun j ↦ isOpen_analyticAt ℂ (f j)
  have hU0 : (0 : Fin n → ℂ) ∈ U := mem_iInter.2 fun j ↦ anb_rep_analyticAt (g j)
  have hf : ∀ j, AnalyticOnNhd ℂ (f j) U := fun j z hz ↦ mem_iInter.1 hz j
  obtain ⟨W, V, hW, hW0, hWU, hV, -, prj, hprj, -, hfib, -⟩ :=
    adim6_confined_projection n dP m P hP.ne_top π θ hfinite hcomp g hgen f U hU hU0 hf
      (fun j ↦ anb_rep_germ (g j))
  refine ⟨dP, π, W, m, f, hW, hW0, fun j ↦ (hf j).continuousOn.mono hWU, ?_, fun w ↦ ?_, ?_⟩
  · rw [adim2_zeroSet, Finset.inf_congr rfl fun g _ ↦ anb_zero_eq g, anb_germ_finset_inf]
    refine Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦
      propext ⟨fun h j ↦ ?_, fun h x hx ↦ ?_⟩)
    · exact h _ (e.symm j).2
    · have := h (e ⟨x, hx⟩)
      simpa [f, g] using this
  · by_cases hw : w ∈ V
    · refine ((hfib ⟨w, hw⟩).image Subtype.val).subset ?_
      rintro z ⟨hzW, hz0, hzw⟩
      refine ⟨⟨z, hzW, hz0⟩, ?_, rfl⟩
      exact Subtype.ext ((hprj _).trans hzw)
    · convert Set.finite_empty
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hzW hz0 hzw
      exact hw (hzw ▸ hprj ⟨z, hzW, hz0⟩ ▸ (prj ⟨z, hzW, hz0⟩).2)
  · rw [← hdim, adim6_parameter_dimension]
    rfl

/-- The germ of a set cut out near `p` by finitely many analytic functions is a finite
infimum of zero germs. -/
theorem anb_germ_eq_inf {n k : ℕ} {B O : Set (Fin n → ℂ)} {p : Fin n → ℂ} (hO : IsOpen O)
    (hpO : p ∈ O) {F : (Fin n → ℂ) → (Fin k → ℂ)} (hF : AnalyticOnNhd ℂ F O)
    (hBF : ∀ z ∈ O, (z ∈ B ↔ F z = 0)) :
    ∃ s : Finset (AnalyticGerm n), adim2_germ n B p = s.inf (adim2_zero n) := by
  classical
  have hFa : ∀ j, AnalyticAt ℂ (fun z ↦ F (p + z) j) 0 := fun j ↦
    analyticAt_pi_iff.1 ((hF p hpO).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)) j
  let fj : Fin k → AnalyticGerm n := fun j ↦
    ⟨Filter.Germ.ofFun (fun z ↦ F (p + z) j), _, hFa j, rfl⟩
  refine ⟨Finset.univ.image fj, ?_⟩
  rw [Finset.inf_image]
  have : (Finset.univ.inf (adim2_zero n ∘ fj)) =
      Finset.univ.inf (fun j ↦ (Filter.Germ.ofFun (fun z ↦ F (p + z) j = 0) :
        Filter.Germ (𝓝 (0 : Fin n → ℂ)) Prop)) := rfl
  rw [this, anb_germ_finset_inf]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [anb_eventually_add_mem hO hpO] with z hz
  rw [hBF _ hz]
  simp [funext_iff]

end HodgeLean.Foundations.Analytic
