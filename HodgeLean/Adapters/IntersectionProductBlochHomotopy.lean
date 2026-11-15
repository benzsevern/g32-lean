import HodgeLean.Adapters.IntersectionProductBlochSquare

/-! # The relative moving step from a homotopy on `X × ℙ¹ × ℙ¹`

Stage A3.3. Bloch's proof of the moving lemma moves a chain `Z` on `X × ℙ¹_t` through a
two-parameter chain `W` on `(X × ℙ¹_t) × ℙ¹_s`: the boundary of `W` in `s` is `Z` minus a chain
of smaller excess, and the boundary of `W` in `t` is a chain on `X × ℙ¹_s` in good position.
`a3k_Homotopy X` asks for such a `W` (in square position, `a3k_SquarePos`) for every chain of
excess at most `k + 1` whose boundary meets `β` properly.

Given it, the relative moving step `a3k_Step X` follows (`a3k_step_of_homotopy`): with
`Z' = Z − ∂_s W` restricted to its members dominating `ℙ¹` (`a3k_dom`, which keeps the
boundary), `∂Z − ∂Z' = ∂_t ∂_s W = ∂_s ∂_t W` (`a3k_bd_bd`) lies in `a3k_G X β`, and so `∂Z'`
meets `β` properly (`a3k_G_le_proper`).

The homotopy itself comes from Bloch's homotopy operators by linearity
(`a3k_homotopy_of_operators`): an assignment `H` of two-parameter chains to the members and `h`
of chains on `X × ℙ¹_s` to the points of `X` with `∂_t (H y) = h(∂ y)` (`a3k_BlochOperators`);
then `W = Σ_y Z(y) H(y)` has `∂_t W = h(∂Z)`, and the components of `∂Z` meet `β` properly,
which is where the hypothesis on `∂Z` enters.

In Bloch's construction `W` is built from a finite linear projection `π : X → ℙⁿ` and a family
of translations of `ℙⁿ` over `ℙ¹_s`: for a member `Y`, `W_Y` is the pull-back along
`π × id × id` of the family of translates of `(π × id)(Y)`; its fibre over `s = 0` is
`(π × id)^*(π × id)_*[Y] = [Y] + R` with `R` of smaller excess (Roberts' main lemma over `ℙ¹_t`),
its fibre over `s = 1` is a general translate, and its faces over `t = a` are the same
construction applied to the faces of `Y`, so that `∂_t W = h(∂Z)` for the linear operator `h` on
cycles of `X`; the components of `∂Z` meet `β` properly, so the members of `h(∂Z)` are in good
position.

Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2 and §1; J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970*
(1972), 89–96, Main Lemma. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

namespace HodgeLean.Adapters

section dom
variable (X : Over (Spec ↧ℂ)) [IsProper X.hom]

open Classical in
/-- The members of a chain dominating `ℙ¹`.
Source: S. Bloch, *The moving lemma for higher Chow groups* (1994), §1 (the group `z^p(X, 1)`
of cycles on `X × Δ¹` meeting the faces properly). -/
def a3k_dom (Z : AlgebraicCycle (a3n_T X).left ℚ) : AlgebraicCycle (a3n_T X).left ℚ :=
  ∑ y ∈ (a3m_support_finite Z).toFinset.filter (fun y => a3n_h X y = genericPoint (g3c_P 1)),
    a3m_smul (Z y) (Function.locallyFinsuppWithin.single y 1)

example : a3k_dom X 0 = 0 := by
  classical
  rw [a3k_dom]
  convert Finset.sum_empty
  ext y
  simp

open Classical in
theorem a3k_dom_apply (Z : AlgebraicCycle (a3n_T X).left ℚ) (y : (a3n_T X).left) :
    a3k_dom X Z y = if a3n_h X y = genericPoint (g3c_P 1) then Z y else 0 := by
  rw [a3k_dom, a3m_sum_apply]
  simp only [a3m_smul_apply, Function.locallyFinsuppWithin.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Finset.mem_filter.1 h1).2 h2
  · by_contra hZ
    exact h1 (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 (Ne.symm hZ), h2⟩)
  · rfl

/-- Restricting to the members dominating `ℙ¹` keeps the boundary. -/
theorem a3k_bd_dom (Z : AlgebraicCycle (a3n_T X).left ℚ) : a3k_bd X (a3k_dom X Z) = a3k_bd X Z := by
  classical
  set s := (a3m_support_finite Z).toFinset
  have hs : ∀ y ∉ s, Z y = 0 := fun y hy => by simpa [s] using hy
  have hs' : ∀ y ∉ s, a3k_dom X Z y = 0 := fun y hy => by
    rw [a3k_dom_apply, hs y hy, ite_self]
  rw [a3k_bd_eq_sum X _ s hs', a3k_bd_eq_sum X _ s hs]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [a3k_dom_apply]
  split_ifs with hy
  · rfl
  · have : a3k_piece X y = 0 := by
      unfold a3k_piece
      rw [dite_eq_right hy]
    rw [this]
    ext x
    simp

end dom

section homotopy
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- **The homotopy of the relative moving step.** For every chain `Z` on `X × ℙ¹` of excess at
most `k + 1` against `β` whose boundary meets `β` properly there is a two-parameter chain `W` on
`(X × ℙ¹_t) × ℙ¹_s` whose members are in square position, such that the members of
`Z − ∂_s W` dominating `ℙ¹` have excess at most `k`, and the members of `∂_t W` dominating
`ℙ¹` are in good position with respect to `β`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2 (the homotopy built from a finite linear projection and a family of translations);
J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96, Main Lemma
(the residual of the cone has smaller excess). -/
def a3k_Homotopy : Prop :=
  ∀ (β : AlgebraicCycle X.left ℚ) (k : ℕ) (Z : AlgebraicCycle (a3n_T X).left ℚ),
    a3k_ChainLE X β Z (k + 1) → a3i_CyclesMeetProperly X.left (a3k_bd X Z) β →
      ∃ W : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ,
        (∀ w, W w ≠ 0 → a3k_SquarePos X w) ∧
        (∀ y, (Z - a3k_bd (a3n_T X) W) y ≠ 0 → a3n_h X y = genericPoint (g3c_P 1) →
          a3k_ExcessLE X β y k) ∧
        (∀ y, a3k_dt X W y ≠ 0 → ∀ hy : a3n_h X y = genericPoint (g3c_P 1), a3o_Good X β y hy)

/-- A chain of excess at most `k + 1` with no members needs no homotopy. -/
example (β : AlgebraicCycle X.left ℚ) (k : ℕ) :
    ∃ W : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ,
      (∀ w, W w ≠ 0 → a3k_SquarePos X w) ∧
      (∀ y, ((0 : AlgebraicCycle (a3n_T X).left ℚ) - a3k_bd (a3n_T X) W) y ≠ 0 →
        a3n_h X y = genericPoint (g3c_P 1) → a3k_ExcessLE X β y k) ∧
      (∀ y, a3k_dt X W y ≠ 0 → ∀ hy : a3n_h X y = genericPoint (g3c_P 1), a3o_Good X β y hy) := by
  refine ⟨0, fun _ h => (h rfl).elim, fun y hy _ => ?_, fun y hy _ => ?_⟩
  · exact absurd (by rw [a3k_bd_zero, sub_zero]; rfl) hy
  · classical
    have h0 : a3i_intersect (a3n_T (a3n_T X)).left 0
        (Function.locallyFinsuppWithin.single (a3k_E X 0) 1) = 0 := a3o_intersect_zero_left _ _
    have h1 : a3i_intersect (a3n_T (a3n_T X)).left 0
        (Function.locallyFinsuppWithin.single (a3k_E X 1) 1) = 0 := a3o_intersect_zero_left _ _
    refine absurd ?_ hy
    rw [a3k_dt, h0, h1]
    have : a3m_smul (a3k_cycT X (a3n_σ X 0 (genericPoint X.left)))
        (0 : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ) +
        a3m_smul (a3k_cycT X (a3n_σ X 1 (genericPoint X.left))) 0 = 0 := by ext; simp
    rw [this, a3k_pushforward_zero]
    rfl

/-- **The relative moving step from the homotopy.** -/
theorem a3k_step_of_homotopy (H : a3k_Homotopy X) : a3k_Step X := by
  intro β k Z hZ hm
  obtain ⟨W, hW, hexc, hgood⟩ := H β k Z hZ hm
  refine ⟨a3k_dom X (Z - a3k_bd (a3n_T X) W), fun y hy => ?_, ?_, ?_⟩
  · rw [a3k_dom_apply] at hy
    split_ifs at hy with hd
    · exact ⟨hd, hexc y hy hd⟩
    · exact (hy rfl).elim
  · have hG : a3k_bd X Z - a3k_bd X (a3k_dom X (Z - a3k_bd (a3n_T X) W)) ∈ a3k_G X β := by
      rw [a3k_bd_dom, a3k_bd_sub, sub_sub_cancel, a3k_bd_bd X W hW]
      exact a3k_bd_mem_G X β _ hgood
    have hp := (a3k_properSub X β).sub_mem (show a3k_bd X Z ∈ a3k_properSub X β from hm)
      (a3k_G_le_proper X β hG)
    rwa [sub_sub_cancel] at hp
  · rw [a3k_bd_dom, a3k_bd_sub, sub_sub_cancel, a3k_bd_bd X W hW]
    exact a3k_bd_mem_G X β _ hgood

end homotopy

section linear
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The linear extension of an assignment of cycles to points.
Source: Fulton, *Intersection Theory*, second edition, §1.3 (cycles are finite formal sums). -/
def a3k_lin {A B : Scheme.{0}} [IsNoetherian A] (F : A → AlgebraicCycle B ℚ)
    (c : AlgebraicCycle A ℚ) : AlgebraicCycle B ℚ :=
  ∑ y ∈ (a3m_support_finite c).toFinset, a3m_smul (c y) (F y)

example {A B : Scheme.{0}} [IsNoetherian A] (F : A → AlgebraicCycle B ℚ) : a3k_lin F 0 = 0 := by
  simp [a3k_lin]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_lin_eq_sum {A B : Scheme.{0}} [IsNoetherian A] (F : A → AlgebraicCycle B ℚ)
    (c : AlgebraicCycle A ℚ) (s : Finset A) (hs : ∀ y ∉ s, c y = 0) :
    a3k_lin F c = ∑ y ∈ s, a3m_smul (c y) (F y) := by
  classical
  have h0 : ∀ y, a3m_smul 0 (F y) = 0 := fun y => by ext; simp
  rw [a3k_lin, ← Finset.sum_subset (s₁ := (a3m_support_finite c).toFinset ∩ s)
      Finset.inter_subset_left, ← Finset.sum_subset (s₁ := (a3m_support_finite c).toFinset ∩ s)
      Finset.inter_subset_right]
  · intro y _ hy
    rw [Finset.mem_inter, not_and_or] at hy
    rcases hy with hy | hy
    · rw [show c y = 0 by simpa using hy, h0]
    · exact absurd ‹y ∈ s› hy
  · intro y hy hy'
    rw [Finset.mem_inter, not_and_or] at hy'
    rcases hy' with hy' | hy'
    · exact absurd hy hy'
    · rw [hs y hy', h0]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_lin_add {A B : Scheme.{0}} [IsNoetherian A] (F : A → AlgebraicCycle B ℚ)
    (c d : AlgebraicCycle A ℚ) : a3k_lin F (c + d) = a3k_lin F c + a3k_lin F d := by
  classical
  set s := (a3m_support_finite c).toFinset ∪ (a3m_support_finite d).toFinset
  have hc : ∀ y ∉ s, c y = 0 := fun y hy => by
    simp only [s, Finset.mem_union, Set.Finite.mem_toFinset, Function.mem_support, not_or,
      not_not] at hy
    exact hy.1
  have hd : ∀ y ∉ s, d y = 0 := fun y hy => by
    simp only [s, Finset.mem_union, Set.Finite.mem_toFinset, Function.mem_support, not_or,
      not_not] at hy
    exact hy.2
  have hcd : ∀ y ∉ s, (c + d) y = 0 := fun y hy => by
    rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hc y hy, hd y hy, add_zero]
  rw [a3k_lin_eq_sum F _ s hcd, a3k_lin_eq_sum F _ s hc, a3k_lin_eq_sum F _ s hd,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ext x
  simp [add_mul]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_lin_smul {A B : Scheme.{0}} [IsNoetherian A] (F : A → AlgebraicCycle B ℚ) (r : ℚ)
    (c : AlgebraicCycle A ℚ) : a3k_lin F (a3m_smul r c) = a3m_smul r (a3k_lin F c) := by
  classical
  set s := (a3m_support_finite c).toFinset
  have hs : ∀ y ∉ s, c y = 0 := fun y hy => by simpa [s] using hy
  have hs' : ∀ y ∉ s, a3m_smul r c y = 0 := fun y hy => by rw [a3m_smul_apply, hs y hy, mul_zero]
  rw [a3k_lin_eq_sum F _ s hs', a3k_lin_eq_sum F _ s hs, a3m_smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ext x
  simp [mul_assoc]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_lin_sum {A B : Scheme.{0}} [IsNoetherian A] (F : A → AlgebraicCycle B ℚ) {ι : Type*}
    (s : Finset ι) (G : ι → AlgebraicCycle A ℚ) :
    a3k_lin F (∑ i ∈ s, G i) = ∑ i ∈ s, a3k_lin F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [a3k_lin]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, a3k_lin_add, ih]

theorem a3k_dt_add (W W' : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ) :
    a3k_dt X (W + W') = a3k_dt X W + a3k_dt X W' := by
  rw [a3k_dt, a3k_dt, a3k_dt, a3o_intersect_add_left, a3o_intersect_add_left, ← a1p_pushforward_add]
  congr 1
  ext x
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, a3m_smul_apply]
  ring

theorem a3k_dt_smul (r : ℚ) (W : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ) :
    a3k_dt X (a3m_smul r W) = a3m_smul r (a3k_dt X W) := by
  rw [a3k_dt, a3k_dt, a3o_intersect_smul_left, a3o_intersect_smul_left, ← a3k_pushforward_smul]
  congr 1
  ext x
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, a3m_smul_apply]
  ring

theorem a3k_dt_sum {ι : Type*} (s : Finset ι) (G : ι → AlgebraicCycle (a3n_T (a3n_T X)).left ℚ) :
    a3k_dt X (∑ i ∈ s, G i) = ∑ i ∈ s, a3k_dt X (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := a3k_dt_add X 0 0
    rw [add_zero] at h
    simpa using h
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, a3k_dt_add, ih]

end linear

section operators
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

open Classical in
/-- **Bloch's homotopy operators** for finitely many members `S` of excess at most `k + 1`:
an assignment `H` of two-parameter chains to the members and `h` of chains on `X × ℙ¹_s` to the
points of `X` such that the members of `H y` are in square position, `∂_t (H y) = h(∂ y)`,
`[y] − ∂_s (H y)` has excess at most `k`, and `h D` is in good position with respect to `β` for
every face component `D` of the members meeting `β` properly.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2 (the homotopy `h` with `∂h + h∂ = id − φ`, built from a finite linear projection and
a family of translations); J. Roberts, *Chow's moving lemma* (1972), Main Lemma. -/
def a3k_BlochOperators (β : AlgebraicCycle X.left ℚ) (k : ℕ) (S : Finset (a3n_T X).left) :
    Prop :=
  ∃ (H : (a3n_T X).left → AlgebraicCycle (a3n_T (a3n_T X)).left ℚ)
    (h : X.left → AlgebraicCycle (a3n_T X).left ℚ),
    (∀ y ∈ S, ∀ w, H y w ≠ 0 → a3k_SquarePos X w) ∧
    (∀ y ∈ S, a3k_dt X (H y) = a3k_lin h (a3k_piece X y)) ∧
    (∀ y ∈ S, ∀ y', ((Function.locallyFinsuppWithin.single y 1 : AlgebraicCycle (a3n_T X).left ℚ) -
      a3k_bd (a3n_T X) (H y)) y' ≠ 0 →
      a3n_h X y' = genericPoint (g3c_P 1) → a3k_ExcessLE X β y' k) ∧
    (∀ D : X.left, (∃ y ∈ S, a3k_piece X y D ≠ 0) →
      (∀ v, β v ≠ 0 → a3i_MeetProperly X.left D v) →
      ∀ y', h D y' ≠ 0 → ∀ hy' : a3n_h X y' = genericPoint (g3c_P 1), a3o_Good X β y' hy')

/-- With no members there is nothing to move. -/
example (β : AlgebraicCycle X.left ℚ) (k : ℕ) : a3k_BlochOperators X β k ∅ :=
  ⟨fun _ => 0, fun _ => 0, fun _ h => (Finset.notMem_empty _ h).elim,
    fun _ h => (Finset.notMem_empty _ h).elim, fun _ h => (Finset.notMem_empty _ h).elim,
    fun _ ⟨_, h, _⟩ => (Finset.notMem_empty _ h).elim⟩

/-- Bloch's homotopy operators exist for every finite set of members dominating `ℙ¹` of excess
at most `k + 1`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §2; J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972),
89–96. -/
def a3k_HomotopyOperators : Prop :=
  ∀ (β : AlgebraicCycle X.left ℚ) (k : ℕ) (S : Finset (a3n_T X).left),
    (∀ y ∈ S, a3n_h X y = genericPoint (g3c_P 1) ∧ a3k_ExcessLE X β y (k + 1)) →
      a3k_BlochOperators X β k S

example (H : a3k_HomotopyOperators X) (β : AlgebraicCycle X.left ℚ) (k : ℕ) :
    a3k_BlochOperators X β k ∅ :=
  H β k ∅ fun _ h => (Finset.notMem_empty _ h).elim

/-- **The homotopy from the operators**: `W = Σ_y Z(y) H(y)`, with `∂_t W = h(∂Z)`. -/
theorem a3k_homotopy_of_operators (HO : a3k_HomotopyOperators X) : a3k_Homotopy X := by
  classical
  intro β k Z hZ hm
  set S := (a3m_support_finite Z).toFinset
  have hS : ∀ y ∉ S, Z y = 0 := fun y hy => by simpa [S] using hy
  have hS' : ∀ y ∈ S, Z y ≠ 0 := fun y hy => by simpa [S] using hy
  obtain ⟨H, h, h1, h2, h3, h4⟩ := HO β k S fun y hy => hZ y (hS' y hy)
  refine ⟨∑ y ∈ S, a3m_smul (Z y) (H y), fun w hw => ?_, fun y' hy' hd => ?_, fun y' hy' hd => ?_⟩
  · obtain ⟨y, hy, hyw⟩ := a3m_exists_of_sum_apply_ne_zero S _ w hw
    exact h1 y hy w fun h0 => hyw (by rw [a3m_smul_apply, h0, mul_zero])
  · have hdec : Z - a3k_bd (a3n_T X) (∑ y ∈ S, a3m_smul (Z y) (H y)) = ∑ y ∈ S,
        a3m_smul (Z y) (Function.locallyFinsuppWithin.single y 1 - a3k_bd (a3n_T X) (H y)) := by
      rw [a3k_bd_sum]
      simp only [a3k_bd_smul, a3m_smul_sub, Finset.sum_sub_distrib]
      rw [← a3m_eq_sum_single Z S hS]
    rw [hdec] at hy'
    obtain ⟨y, hy, hyy⟩ := a3m_exists_of_sum_apply_ne_zero S _ y' hy'
    exact h3 y hy y' (fun h0 => hyy (by rw [a3m_smul_apply, h0, mul_zero])) hd
  · have hdt : a3k_dt X (∑ y ∈ S, a3m_smul (Z y) (H y)) = a3k_lin h (a3k_bd X Z) := by
      rw [a3k_dt_sum, a3k_bd, a3k_lin_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [a3k_dt_smul, a3k_lin_smul, h2 y hy]
    rw [hdt, a3k_lin] at hy'
    obtain ⟨D, hD, hDy⟩ := a3m_exists_of_sum_apply_ne_zero _ _ y' hy'
    have hD' : a3k_bd X Z D ≠ 0 := by simpa using hD
    have hDp : ∀ v, β v ≠ 0 → a3i_MeetProperly X.left D v := fun v hv => hm D v hD' hv
    have hDS : ∃ y ∈ S, a3k_piece X y D ≠ 0 := by
      rw [a3k_bd] at hD'
      obtain ⟨y, hy, hyD⟩ := a3m_exists_of_sum_apply_ne_zero _ _ D hD'
      exact ⟨y, hy, fun h0 => hyD (by rw [a3m_smul_apply, h0, mul_zero])⟩
    exact h4 D hDS hDp y' (fun h0 => hDy (by rw [a3m_smul_apply, h0, mul_zero])) hd

end operators

end HodgeLean.Adapters
