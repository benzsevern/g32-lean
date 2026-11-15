import HodgeLean.Adapters.IntersectionProductBlochChain

/-! # The excess of a member of a chain, and the induction on the excess

Stage A3.3, the degree-one moving lemma. For a member `Y = closure {y}` of `T = X × ℙ¹` and a
component `V = closure {v}` of `β`, the excess is measured against three subvarieties of `T`:
`V × ℙ¹` (only for the components of the intersection over `ℙ¹ ∖ {∞}`), `V × {0}` and `V × {1}`
(`a3k_ExcessLE`). Excess `0`, with the dimension inequality on the smooth variety `T`, is the good
position `a3o_Good` (`a3k_good_of_excessLE_zero`): the components of `div (t|_Y)` lie in `σ₀(X)` and
`σ₁(X)`, and a component of `Y ∩ (V × ℙ¹)` over `t₁ ∈ {0, 1}` lies in `Y ∩ (V × {0})` or
`Y ∩ (V × {1})`, whose components have codimension `codim Y + codim V + 1`.

Given a step lowering the excess of a chain by one while keeping its boundary in proper position
with respect to `β` and changing the boundary by an element of `a3k_G X β` (`a3k_Step`), every
chain whose boundary meets `β` properly has its boundary in `a3k_G X β`
(`a3k_chain_mem_G_of_step`), and with Fulton's description of rational equivalence through
`X × ℙ¹` this is `a3o_MovingRatEquiv X` (`a3k_movingRatEquiv_of_step`).

Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §1 and §2 (the subcomplex `z^p_W(X, •)`, faces and `W × faces` in proper position);
J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96 (the
induction on the excess); Fulton, *Intersection Theory*, second edition, §1.6 and §11.4.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

namespace HodgeLean.Adapters

section excess
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

/-- The excess of `Y = closure {y} ⊆ X × ℙ¹` with respect to the components `V` of `β` is at most
`k`: every component of `Y ∩ (V × ℙ¹)` over `ℙ¹ ∖ {∞}`, of `Y ∩ (V × {0})` and of
`Y ∩ (V × {1})` has codimension at least the expected one minus `k`.
Source: J. Roberts, *Chow's moving lemma* (1972), the excess `e(V, W)`; S. Bloch, *The moving
lemma for higher Chow groups* (1994), §1 (proper position with `W × faces`). -/
def a3k_ExcessLE (β : AlgebraicCycle X.left ℚ) (y : (a3n_T X).left) (k : ℕ) : Prop :=
  ∀ v, β v ≠ 0 →
    (∀ z ∈ a3y_comps y (a3n_b X v), a3n_p X z ∈ Set.range (a3m_Pnκ 1 0) →
      coheight y + coheight (a3n_b X v) ≤ coheight z + k) ∧
    (∀ z ∈ a3y_comps y (a3n_σ X 0 v), coheight y + coheight (a3n_σ X 0 v) ≤ coheight z + k) ∧
    (∀ z ∈ a3y_comps y (a3n_σ X 1 v), coheight y + coheight (a3n_σ X 1 v) ≤ coheight z + k)

example (y : (a3n_T X).left) (k : ℕ) : a3k_ExcessLE X 0 y k := fun _ h => (h rfl).elim

omit [IsIntegral X.left] [IsProper X.hom] in
theorem a3k_excessLE_mono {β : AlgebraicCycle X.left ℚ} {y : (a3n_T X).left} {k k' : ℕ}
    (hk : k ≤ k') (h : a3k_ExcessLE X β y k) : a3k_ExcessLE X β y k' := by
  have hk' : ((k : ℕ∞)) ≤ k' := by exact_mod_cast hk
  intro v hv
  obtain ⟨h1, h2, h3⟩ := h v hv
  exact ⟨fun z hz hc => (h1 z hz hc).trans (by gcongr),
    fun z hz => (h2 z hz).trans (by gcongr),
    fun z hz => (h3 z hz).trans (by gcongr)⟩

omit [IsIntegral X.left] in
/-- Every member has finite excess. -/
theorem a3k_exists_excessLE (β : AlgebraicCycle X.left ℚ) (y : (a3n_T X).left) :
    ∃ k, a3k_ExcessLE X β y k := by
  classical
  have : IsNoetherian X.left := by
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : CompactSpace X.left := by
      have h := QuasiCompact.isCompact_preimage (f := X.hom) _ isOpen_univ isCompact_univ
      rw [Set.preimage_univ] at h
      exact isCompact_univ_iff.mp h
    exact ⟨⟩
  set s := (a3m_support_finite β).toFinset
  set f : (a3n_T X).left → ℕ := fun τ => (coheight τ).toNat
  set K := f y + ∑ v ∈ s, (f (a3n_b X v) + f (a3n_σ X 0 v) + f (a3n_σ X 1 v))
  have hfin : ∀ τ : (a3n_T X).left, ((f τ : ℕ) : ℕ∞) = coheight τ := fun τ =>
    ENat.natCast_toNat (a3c_coheight_ne_top _ τ)
  have key : ∀ (τ z : (a3n_T X).left), f τ ≤ K - f y → coheight y + coheight τ ≤ coheight z + K := by
    intro τ z hτ
    rw [← hfin y, ← hfin τ]
    calc ((f y : ℕ) : ℕ∞) + (f τ : ℕ) = ((f y + f τ : ℕ) : ℕ∞) := by push_cast; rfl
      _ ≤ (K : ℕ∞) := by exact_mod_cast (by omega : f y + f τ ≤ K)
      _ ≤ coheight z + K := le_add_self
  have hle : ∀ v, β v ≠ 0 → f (a3n_b X v) + f (a3n_σ X 0 v) + f (a3n_σ X 1 v) ≤ K - f y := by
    intro v hv
    have : f (a3n_b X v) + f (a3n_σ X 0 v) + f (a3n_σ X 1 v) ≤
        ∑ v ∈ s, (f (a3n_b X v) + f (a3n_σ X 0 v) + f (a3n_σ X 1 v)) :=
      Finset.single_le_sum (f := fun v => f (a3n_b X v) + f (a3n_σ X 0 v) + f (a3n_σ X 1 v))
        (fun _ _ => Nat.zero_le _) (by simpa [s] using hv)
    omega
  refine ⟨K, fun v hv => ⟨fun z _ _ => key _ z ?_, fun z _ => key _ z ?_, fun z _ => key _ z ?_⟩⟩
  · have := hle v hv; omega
  · have := hle v hv; omega
  · have := hle v hv; omega

end excess

section base
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsIntegral X.left] [Smooth X.hom] in
theorem a3k_coheight_le_of_specializes {τ τ' : (a3n_T X).left} (h : τ ⤳ τ') :
    coheight τ ≤ coheight τ' := by
  by_cases he : τ = τ'
  · rw [he]
  · exact (a3y_coheight_lt h he).le

omit [IsProjective X.hom] in
/-- The dimension inequality on `X × ℙ¹`. -/
theorem a3k_coheight_comps_le {u w z : (a3n_T X).left} (hz : z ∈ a3y_comps u w) :
    coheight z ≤ coheight u + coheight w := by
  obtain ⟨w', hw', rfl⟩ := hz
  exact a3m_coheight_component_le_of_smooth (a3n_T X) u w w' hw'

omit [IsProjective X.hom] in
/-- A point of `V × ℙ¹` on the section `σ_c` lies on `σ_c(V)`. -/
theorem a3k_σ_specializes_of_b (c : ℂ) (v x : X.left)
    (h : a3n_b X v ⤳ a3n_σ X c x) : a3n_σ X c v ⤳ a3n_σ X c x := by
  rw [a3n_b_specializes_iff, a3n_q_σ_apply] at h
  exact h.map (a3n_σ X c).continuous

/-- `V × ℙ¹` has codimension at most that of `V`. -/
theorem a3k_coheight_b_le (v : X.left) : coheight (a3n_b X v) ≤ coheight v := by
  have hb0 : a3n_b X v ⤳ a3n_σ X 0 v := by rw [a3n_b_specializes_iff, a3n_q_σ_apply]
  have hb1 : a3n_b X v ⤳ a3n_σ X 1 v := by rw [a3n_b_specializes_iff, a3n_q_σ_apply]
  have hne : a3n_b X v ≠ a3n_σ X 0 v := by
    intro h
    rw [h] at hb1
    obtain ⟨x, hx⟩ := a3n_mem_range_σ_of_specializes X 0 hb1
    exact a3n_σ0_ne_σ1 X x v hx
  have hlt := a3y_coheight_lt hb0 hne
  rw [a3n_coheight_σ] at hlt
  exact (ENat.lt_add_one_iff (a3c_coheight_ne_top _ v)).1 hlt

/-- A point of `Y ∩ (V × {c})` has codimension at least `codim Y + codim V + 1` when the
excess of `Y` against `V × {c}` is `0`. -/
theorem a3k_coheight_of_σ (c : ℂ) (y : (a3n_T X).left) (v : X.left)
    (h : ∀ z ∈ a3y_comps y (a3n_σ X c v), coheight y + coheight (a3n_σ X c v) ≤ coheight z + 0)
    {τ : (a3n_T X).left} (hyτ : y ⤳ τ) (hvτ : a3n_σ X c v ⤳ τ) :
    coheight y + coheight v + 1 ≤ coheight τ := by
  obtain ⟨z, hz, hzτ⟩ := a3y_exists_comp y (a3n_σ X c v) hyτ hvτ
  have h1 := h z hz
  rw [a3n_coheight_σ, add_zero, ← add_assoc] at h1
  exact h1.trans (a3k_coheight_le_of_specializes X hzτ)

/-- **Excess zero is good position.** -/
theorem a3k_good_of_excessLE_zero (β : AlgebraicCycle X.left ℚ) (y : (a3n_T X).left)
    (hy : a3n_h X y = genericPoint (g3c_P 1)) (h : a3k_ExcessLE X β y 0) :
    a3o_Good X β y hy := by
  intro v hv
  obtain ⟨hb, h0, h1⟩ := h v hv
  have hfin : ∀ τ : (a3n_T X).left, coheight τ ≠ ⊤ := a3c_coheight_ne_top _
  have hbv := a3k_coheight_b_le X v
  refine ⟨fun z hz hc => le_antisymm (a3k_coheight_comps_le X hz) (by simpa using hb z hz hc),
    fun d hd => ?_, fun z hz => ⟨fun hz0 => ?_, fun hz1 => ?_⟩⟩
  · -- the components of `div (t|_Y)` meet `V × ℙ¹` properly
    obtain ⟨D, hD, hD1, -⟩ := a3z_principalCycle_ne_zero (a3n_T X).left y (a3o_φ X y hy)
      (a3o_φ_ne_zero X y hy) d hd
    have hcohd : coheight d = coheight y + 1 := by
      rw [← hD]
      exact (a3y_coheight_eq_one_iff (a3n_T X) y D).1 hD1
    have hyd : y ⤳ d := hD ▸ a3z_specializes_pt y D
    intro w hw
    have hz : (ccm3_primeIdeal (a3n_T X).left d ⊔ ccm3_primeIdeal (a3n_T X).left
        (a3n_b X v)).subschemeι w ∈ a3y_comps d (a3n_b X v) := ⟨w, hw, rfl⟩
    set z := (ccm3_primeIdeal (a3n_T X).left d ⊔ ccm3_primeIdeal (a3n_T X).left
        (a3n_b X v)).subschemeι w
    obtain ⟨hdz, hbz, -⟩ := a3y_comps_spec _ _ hz
    refine le_antisymm (a3k_coheight_comps_le X hz) ?_
    have hge : coheight y + coheight v + 1 ≤ coheight z := by
      rcases a3o_cyc_supp X y hy d hd with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · obtain ⟨x, hx⟩ := a3n_mem_range_σ_of_specializes X 0 hdz
        rw [← hx] at hbz ⊢
        exact a3k_coheight_of_σ X 0 y v h0 (hyd.trans (hx ▸ hdz))
          (a3k_σ_specializes_of_b X 0 v x hbz)
      · obtain ⟨x, hx⟩ := a3n_mem_range_σ_of_specializes X 1 hdz
        rw [← hx] at hbz ⊢
        exact a3k_coheight_of_σ X 1 y v h1 (hyd.trans (hx ▸ hdz))
          (a3k_σ_specializes_of_b X 1 v x hbz)
    calc coheight d + coheight (a3n_b X v) = coheight y + coheight (a3n_b X v) + 1 := by
          rw [hcohd, add_right_comm]
      _ ≤ coheight y + coheight v + 1 := by gcongr
      _ ≤ coheight z := hge
  · -- no component of `Y ∩ (V × ℙ¹)` lies over `t₁ = 0`
    obtain ⟨hyz, hbz, -⟩ := a3y_comps_spec _ _ hz
    have hz' := a3n_eq_σ0 X z hz0
    rw [hz'] at hbz
    have hge := a3k_coheight_of_σ X 0 y v h0 hyz (hz' ▸ a3k_σ_specializes_of_b X 0 v _ hbz)
    have hle := (a3k_coheight_comps_le X hz).trans (add_le_add_right hbv _)
    have := hge.trans hle
    exact absurd this (not_le.2 (ENat.lt_add_one_iff (by
      exact WithTop.add_ne_top.2 ⟨hfin y, a3c_coheight_ne_top _ v⟩) |>.2 le_rfl))
  · -- no component of `Y ∩ (V × ℙ¹)` lies over `t₁ = 1`
    obtain ⟨hyz, hbz, -⟩ := a3y_comps_spec _ _ hz
    have hz' := a3n_eq_σ1 X z hz1
    rw [hz'] at hbz
    have hge := a3k_coheight_of_σ X 1 y v h1 hyz (hz' ▸ a3k_σ_specializes_of_b X 1 v _ hbz)
    have hle := (a3k_coheight_comps_le X hz).trans (add_le_add_right hbv _)
    have := hge.trans hle
    exact absurd this (not_le.2 (ENat.lt_add_one_iff (by
      exact WithTop.add_ne_top.2 ⟨hfin y, a3c_coheight_ne_top _ v⟩) |>.2 le_rfl))

end base

section induction
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A chain whose members dominate `ℙ¹` and have excess at most `k`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §1
(the group `z^p(X, 1)`); J. Roberts, *Chow's moving lemma* (1972), the excess `e(V, W)`. -/
def a3k_ChainLE (β : AlgebraicCycle X.left ℚ) (Z : AlgebraicCycle (a3n_T X).left ℚ) (k : ℕ) :
    Prop :=
  ∀ y, Z y ≠ 0 → a3n_h X y = genericPoint (g3c_P 1) ∧ a3k_ExcessLE X β y k

example (β : AlgebraicCycle X.left ℚ) (k : ℕ) : a3k_ChainLE X β 0 k := fun _ h => (h rfl).elim

/-- The relative moving step: a chain of excess at most `k + 1` whose boundary meets `β`
properly has the same boundary, modulo `a3k_G X β`, as a chain of excess at most `k` whose
boundary meets `β` properly.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §2
(moving by the cone construction and general translates in families); J. Roberts, *Chow's moving
lemma* (1972), Main Lemma, read over `ℙ¹`. -/
def a3k_Step : Prop :=
  ∀ (β : AlgebraicCycle X.left ℚ) (k : ℕ) (Z : AlgebraicCycle (a3n_T X).left ℚ),
    a3k_ChainLE X β Z (k + 1) → a3i_CyclesMeetProperly X.left (a3k_bd X Z) β →
      ∃ Z' : AlgebraicCycle (a3n_T X).left ℚ, a3k_ChainLE X β Z' k ∧
        a3i_CyclesMeetProperly X.left (a3k_bd X Z') β ∧
        a3k_bd X Z - a3k_bd X Z' ∈ a3k_G X β

example (H : a3k_Step X) (β : AlgebraicCycle X.left ℚ) (k : ℕ) :
    ∃ Z' : AlgebraicCycle (a3n_T X).left ℚ, a3k_ChainLE X β Z' k ∧
      a3i_CyclesMeetProperly X.left (a3k_bd X Z') β ∧ a3k_bd X 0 - a3k_bd X Z' ∈ a3k_G X β :=
  H β k 0 (fun _ h => (h rfl).elim) (by rw [a3k_bd_zero]; exact fun _ _ h => (h rfl).elim)

/-- The induction on the excess. -/
theorem a3k_bd_mem_G_of_step (H : a3k_Step X) (β : AlgebraicCycle X.left ℚ) :
    ∀ (k : ℕ) (Z : AlgebraicCycle (a3n_T X).left ℚ), a3k_ChainLE X β Z k →
      a3i_CyclesMeetProperly X.left (a3k_bd X Z) β → a3k_bd X Z ∈ a3k_G X β := by
  intro k
  induction k with
  | zero =>
    intro Z hZ _
    refine a3k_bd_mem_G X β Z fun y hy hy' => ?_
    exact a3k_good_of_excessLE_zero X β y hy' (hZ y hy).2
  | succ k ih =>
    intro Z hZ hm
    obtain ⟨Z', hZ', hm', hG⟩ := H β k Z hZ hm
    have := add_mem hG (ih Z' hZ' hm')
    rwa [sub_add_cancel] at this

/-- Every chain of members dominating `ℙ¹` whose boundary meets `β` properly has its boundary
in `a3k_G X β`, given the relative moving step. -/
theorem a3k_chain_mem_G_of_step (H : a3k_Step X) (β : AlgebraicCycle X.left ℚ)
    (Z : AlgebraicCycle (a3n_T X).left ℚ)
    (hZ : ∀ y, Z y ≠ 0 → a3n_h X y = genericPoint (g3c_P 1))
    (hm : a3i_CyclesMeetProperly X.left (a3k_bd X Z) β) : a3k_bd X Z ∈ a3k_G X β := by
  classical
  choose K hK using a3k_exists_excessLE X β
  set s := (a3m_support_finite Z).toFinset
  refine a3k_bd_mem_G_of_step X H β (∑ y ∈ s, K y) Z (fun y hy => ⟨hZ y hy, ?_⟩) hm
  exact a3k_excessLE_mono X (Finset.single_le_sum (f := K) (fun _ _ => Nat.zero_le _)
    (by simpa [s] using hy)) (hK y)

/-- The moving lemma for rational equivalence from the relative moving step and the description
of the cycles rationally equivalent to zero as boundaries of chains.
Source: S. Bloch, *The moving lemma for higher Chow groups* (1994), §2; Fulton, *Intersection
Theory*, second edition, Proposition 1.6. -/
theorem a3k_movingRatEquiv_of_step (H : a3k_Step X)
    (hgraph : ∀ γ ∈ a3i_ratAll X.left, ∃ Z : AlgebraicCycle (a3n_T X).left ℚ,
      (∀ y, Z y ≠ 0 → a3n_h X y = genericPoint (g3c_P 1)) ∧ a3k_bd X Z = γ) :
    a3o_MovingRatEquiv X := by
  intro γ β hγ hm
  obtain ⟨Z, hZ, rfl⟩ := hgraph γ hγ
  exact a3k_chain_mem_G_of_step X H β Z hZ hm

end induction

end HodgeLean.Adapters
