import HodgeLean.Adapters.IntersectionProductSpecialize
import HodgeLean.Adapters.IntersectionProductRatEquiv

/-! # Intersection with a cycle rationally equivalent to zero, from the moving lemma for rational
equivalence

`a3o_MovingRatEquiv X` is the moving lemma for rational equivalence in families over `ℙ¹`: a cycle
`γ` rationally equivalent to zero that meets `β` properly is a rational combination of the cycles
`[Y(0)] − [Y(1)] = q_*[div (t|_Y)]` of subvarieties `Y` of `X × ℙ¹` dominating `ℙ¹`, each in the
position of `a3o_specialize` with respect to every component of `β` (`a3o_Good`). This is the
degree-one case of Bloch's moving lemma (S. Bloch, *The moving lemma for higher Chow groups*,
J. Algebraic Geom. 3 (1994), 537–568, main theorem: `z^p_W(X, •) → z^p(X, •)` is a
quasi-isomorphism for smooth quasi-projective `X`), read on `X × Δ¹ ⊆ X × ℙ¹` with the faces
`t₁ = 0` and `t₁ = 1`.

Given it, `a3o_intersect_ratEquiv_of_moving` derives the independence statement
`a3i_intersect_ratEquiv`: by bilinearity of `a3i_intersect` it suffices to treat one cycle
`q_*[div (t|_Y)]` and one component `V` of `β`, which is `a3o_specialize`.

Source: Fulton, *Intersection Theory*, second edition, §1.6, §8.2 and §8.3; S. Bloch, *The moving
lemma for higher Chow groups* (1994). HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

namespace HodgeLean.Adapters

section linear
variable (X : Scheme.{0}) [IsNoetherian X]

theorem a3o_intersect_zero_left (d : AlgebraicCycle X ℚ) : a3i_intersect X 0 d = 0 := by
  have h := a3e_intersect_sub_left X 0 0 d
  rw [sub_self, sub_self] at h
  exact h

theorem a3o_intersect_neg_left (c d : AlgebraicCycle X ℚ) :
    a3i_intersect X (-c) d = -a3i_intersect X c d := by
  have h := a3e_intersect_sub_left X 0 c d
  rw [zero_sub, a3o_intersect_zero_left, zero_sub] at h
  exact h

theorem a3o_intersect_add_left (c c' d : AlgebraicCycle X ℚ) :
    a3i_intersect X (c + c') d = a3i_intersect X c d + a3i_intersect X c' d := by
  have h := a3e_intersect_sub_left X c (-c') d
  rw [sub_neg_eq_add, a3o_intersect_neg_left, sub_neg_eq_add] at h
  exact h

/-- `a3i_intersect` is `ℚ`-linear in the first variable. -/
theorem a3o_intersect_smul_left (r : ℚ) (c d : AlgebraicCycle X ℚ) :
    a3i_intersect X (a3m_smul r c) d = a3m_smul r (a3i_intersect X c d) := by
  classical
  let s := (a3c_support_finite c).toFinset
  let t := (a3c_support_finite d).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by simpa [s] using hu
  have hs' : ∀ u ∉ s, a3m_smul r c u = 0 := fun u hu => by rw [a3m_smul_apply, hs u hu, mul_zero]
  have ht : ∀ v ∉ t, d v = 0 := fun v hv => by simpa [t] using hv
  rw [a3c_intersect_eq_sum X _ d s t hs' ht, a3c_intersect_eq_sum X c d s t hs ht, a3m_smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [a3m_smul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ext x
  simp only [Function.locallyFinsuppWithin.mapRange_apply, a3m_smul_apply]
  ring

open Classical in
/-- `a3i_intersect` is linear in the second variable: `c · d = Σ_v d(v) (c · [v])`. -/
theorem a3o_intersect_eq_sum_right (c d : AlgebraicCycle X ℚ) (t : Finset X)
    (ht : ∀ v ∉ t, d v = 0) :
    a3i_intersect X c d =
      ∑ v ∈ t, a3m_smul (d v) (a3i_intersect X c (Function.locallyFinsuppWithin.single v 1)) := by
  classical
  let s := (a3c_support_finite c).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by simpa [s] using hu
  rw [a3c_intersect_eq_sum X c d s t hs ht]
  have h1 : ∀ v ∈ t, a3i_intersect X c (Function.locallyFinsuppWithin.single v 1) =
      ∑ u ∈ s, (a3i_intersectPrime X u v).mapRange (c u * ·) (mul_zero _) := by
    intro v _
    have ht' : ∀ v' ∉ ({v} : Finset X),
        (Function.locallyFinsuppWithin.single v (1 : ℚ)) v' = 0 := by
      intro v' hv'
      rw [Finset.mem_singleton] at hv'
      rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right_iff]
      exact fun h => absurd h hv'
    rw [a3c_intersect_eq_sum X c _ s {v} hs ht']
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_singleton]
    ext x
    simp [Function.locallyFinsuppWithin.mapRange_apply,
      Function.locallyFinsuppWithin.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [h1 v hv, a3m_smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  ext x
  simp only [Function.locallyFinsuppWithin.mapRange_apply, a3m_smul_apply]
  ring

end linear

section moving
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The subvariety `Y = closure {y}` of `X × ℙ¹`, dominating `ℙ¹`, is in the position of
`a3o_specialize` with respect to every component of `β`: the components of `Y ∩ (V × ℙ¹)` over
`ℙ¹ ∖ {∞}` meet properly, the components of `div (t|_Y)` meet `V × ℙ¹` properly, and no component
of `Y ∩ (V × ℙ¹)` lies over `t₁ ∈ {0, 1}`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §1 (the
subcomplex `z^p_W(X, •)` of cycles meeting the faces and `W × faces` properly). -/
def a3o_Good (β : AlgebraicCycle X.left ℚ) (y : (a3n_T X).left)
    (hy : a3n_h X y = genericPoint (g3c_P 1)) : Prop :=
  ∀ v, β v ≠ 0 →
    (∀ z ∈ a3y_comps y (a3n_b X v), a3n_p X z ∈ Set.range (a3m_Pnκ 1 0) →
      coheight z = coheight y + coheight (a3n_b X v)) ∧
    (∀ d, a3o_cyc X y hy d ≠ 0 → a3i_MeetProperly (a3n_T X).left d (a3n_b X v)) ∧
    (∀ z ∈ a3y_comps y (a3n_b X v), a3n_h X z ∉ a3m_Z0 ∧ a3n_h X z ∉ a3m_Zinf)

example (y : (a3n_T X).left) (hy : a3n_h X y = genericPoint (g3c_P 1)) :
    a3o_Good X 0 y hy := fun _ h => (h rfl).elim

/-- The moving lemma for rational equivalence in families over `ℙ¹`: every cycle rationally
equivalent to zero that meets `β` properly is a rational combination of the cycles
`q_*[div (t|_Y)] = [Y(0)] − [Y(1)]` of subvarieties `Y` of `X × ℙ¹` in good position
(`a3o_Good`).
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, main theorem (degree one); Fulton, *Intersection Theory*, second edition,
Proposition 1.6. -/
def a3o_MovingRatEquiv : Prop :=
  ∀ γ β : AlgebraicCycle X.left ℚ, γ ∈ a3i_ratAll X.left → a3i_CyclesMeetProperly X.left γ β →
    γ ∈ AddSubgroup.closure {c | ∃ (y : (a3n_T X).left)
      (hy : a3n_h X y = genericPoint (g3c_P 1)) (r : ℚ), a3o_Good X β y hy ∧
        c = a3m_smul r (a1p_pushforward (a3n_q X).left (a3o_cyc X y hy))}

example : a3o_MovingRatEquiv X → ∀ β : AlgebraicCycle X.left ℚ,
    (0 : AlgebraicCycle X.left ℚ) ∈ AddSubgroup.closure {c | ∃ (y : (a3n_T X).left)
      (hy : a3n_h X y = genericPoint (g3c_P 1)) (r : ℚ), a3o_Good X β y hy ∧
        c = a3m_smul r (a1p_pushforward (a3n_q X).left (a3o_cyc X y hy))} :=
  fun _ _ => AddSubgroup.zero_mem _

/-- The independence statement `a3i_intersect_ratEquiv` from the moving lemma for rational
equivalence.
Source: Fulton, *Intersection Theory*, second edition, §8.3; S. Bloch, *The moving lemma for
higher Chow groups* (1994). -/
theorem a3o_intersect_ratEquiv_of_moving (H : a3o_MovingRatEquiv X)
    (α α' β : AlgebraicCycle X.left ℚ) (hα : α - α' ∈ a3i_ratAll X.left)
    (h : a3i_CyclesMeetProperly X.left α β) (h' : a3i_CyclesMeetProperly X.left α' β) :
    a3i_intersect X.left α β - a3i_intersect X.left α' β ∈ a3i_ratAll X.left := by
  classical
  have : IsNoetherian X.left := by
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : CompactSpace X.left := by
      have h := QuasiCompact.isCompact_preimage (f := X.hom) _ isOpen_univ isCompact_univ
      rw [Set.preimage_univ] at h
      exact isCompact_univ_iff.mp h
    exact ⟨⟩
  refine a3e_intersect_ratEquiv_of_zero X.left (fun γ β hγ hγβ => ?_) α α' β hα h h'
  have hcl := H γ β hγ hγβ
  clear hγ hγβ
  set t := (a3c_support_finite β).toFinset
  have ht : ∀ v ∉ t, β v = 0 := fun v hv => by simpa [t] using hv
  induction hcl using AddSubgroup.closure_induction with
  | mem c hc =>
    obtain ⟨y, hy, r, hgood, rfl⟩ := hc
    rw [a3o_intersect_smul_left]
    refine a3m_smul_mem_ratAll X.left r ?_
    rw [a3o_intersect_eq_sum_right X.left _ β t ht]
    refine AddSubgroup.sum_mem _ fun v _ => ?_
    by_cases hv : β v = 0
    · rw [hv]
      convert (a3i_ratAll X.left).zero_mem
      ext x
      simp
    obtain ⟨hi, hii, hiii⟩ := hgood v hv
    exact a3m_smul_mem_ratAll X.left _ (a3o_specialize X y hy v hi hii hiii)
  | zero =>
    rw [a3o_intersect_zero_left]
    exact zero_mem _
  | add c d _ _ hc hd =>
    rw [a3o_intersect_add_left]
    exact add_mem hc hd
  | neg c _ hc =>
    rw [a3o_intersect_neg_left]
    exact neg_mem hc

end moving

end HodgeLean.Adapters
