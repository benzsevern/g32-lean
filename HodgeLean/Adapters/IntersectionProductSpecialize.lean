import HodgeLean.Adapters.IntersectionProductFamilyStalk

/-! # Specialization of Serre's product in families over `ℙ¹`

Let `Y = closure {y}` be a subvariety of `X × ℙ¹` dominating `ℙ¹`, with the rational function
`φ = t|_Y` of `a3m_P1curve` (zeros over `t₁ = 0`, poles over `t₁ = 1`). If `Y` meets
`V × ℙ¹` properly, the components of `div φ` meet `V × ℙ¹` properly and no component of
`Y ∩ (V × ℙ¹)` lies over `t₁ ∈ {0, 1}`, then `(q_*[div φ]) · [V]` is rationally equivalent to zero
on `X` (`a3o_specialize`). The proof applies the cycle form of Fulton, Theorem 2.4, on `X × ℙ¹`
(`a3z_principal_intersect_mem`), pushes the result to `X` (Fulton, Theorem 1.4), and identifies
`q_*([div φ] · [V × ℙ¹])` with `(q_*[div φ]) · [V]` along the sections `σ₀`, `σ₁`
(`a3n_intersectPrime_σ`).

Source: Fulton, *Intersection Theory*, second edition, Theorem 1.4, Theorem 2.4 and §10.1
(specialization); Serre, *Algèbre locale, multiplicités*, Chapitre V. HC no distance; AV
milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

section basics
variable (X : Over (Spec ↧ℂ))

theorem a3n_pt_ne : a3n_pt 0 a3n_o ≠ a3n_pt 1 a3n_o := by
  intro h
  rw [a3n_pt, a3n_pt, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  have h1 := (a3m_Pnκ 1 0).isOpenEmbedding.injective h
  have h2 := congrArg (fun r : Spec (a3m_PnT 1 0) => a3n_chartEquiv 0 Polynomial.X ∈ r.asIdeal) h1
  simp only at h2
  change (a3n_chartEquiv 0 Polynomial.X ∈ (⊥ : Ideal ℂ).comap (a3n_evc 0)) =
    (a3n_chartEquiv 0 Polynomial.X ∈ (⊥ : Ideal ℂ).comap (a3n_evc 1)) at h2
  simp [a3n_evc] at h2

theorem a3n_σ0_ne_σ1 (x x' : X.left) : a3n_σ X 0 x ≠ a3n_σ X 1 x' := by
  intro h
  have := congrArg (a3n_p X) h
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, a3n_σ_p, a3n_σ_p,
    Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    show X.hom x = a3n_o from Subsingleton.elim _ _,
    show X.hom x' = a3n_o from Subsingleton.elim _ _] at this
  exact a3n_pt_ne this

theorem a3n_σ_injective (c : ℂ) : Function.Injective (a3n_σ X c) := fun x x' h => by
  have := congrArg (a3n_q X).left h
  rwa [a3n_q_σ_apply, a3n_q_σ_apply] at this

/-- The projection has degree one along a section. -/
theorem a3n_degree_q_σ (c : ℂ) (x : X.left) : a1p_degree (a3n_q X).left (a3n_σ X c x) = 1 := by
  have h := a1p_degree_comp (a3n_σ X c) (a3n_q X).left x
  have h1 : a1p_degree (a3n_σ X c ≫ (a3n_q X).left) x = 1 := by
    rw [a3n_σ_q]
    exact a3m_degree_closedImmersion (𝟙 X.left) x
  rw [h1] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

end basics

/-- Proper pushforward preserves rational equivalence to zero in all dimensions.
Source: Fulton, *Intersection Theory*, second edition, Theorem 1.4. -/
theorem a3o_pushforward_ratAll {X Y : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    [IsProper f.left] (c : AlgebraicCycle X.left ℚ) (hc : c ∈ a3i_ratAll X.left) :
    a1p_pushforward f.left c ∈ a3i_ratAll Y.left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  refine AddSubgroup.iSup_induction (fun k : ℕ => a2_ratEquivDim X.left ℚ k)
    (C := fun c => a1p_pushforward f.left c ∈ a3i_ratAll Y.left) hc (fun k c hc => ?_) ?_
    (fun c d hc hd => ?_)
  · exact (le_iSup (fun k : ℕ => a2_ratEquivDim Y.left ℚ k) k)
      (a2_pushforward_ratEquiv_aux f ℚ k c hc)
  · have : a1p_pushforward f.left (0 : AlgebraicCycle X.left ℚ) = 0 := by
      have h := a1p_pushforward_add f.left (0 : AlgebraicCycle X.left ℚ) 0
      rw [add_zero] at h
      exact (left_eq_add.mp h)
    change a1p_pushforward f.left (0 : AlgebraicCycle X.left ℚ) ∈ a3i_ratAll Y.left
    rw [this]
    exact zero_mem _
  · change a1p_pushforward f.left (c + d) ∈ a3i_ratAll Y.left
    rw [a1p_pushforward_add]
    exact add_mem hc hd

section projection
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

omit [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom] in
/-- The fibre of `q_*` over `x` for a cycle supported on `σ₀(X) ∪ σ₁(X)`. -/
theorem a3o_pushforward_apply (c : AlgebraicCycle (a3n_T X).left ℚ)
    (hc : ∀ d, c d ≠ 0 → d ∈ Set.range (a3n_σ X 0) ∪ Set.range (a3n_σ X 1)) (x : X.left) :
    a1p_pushforward (a3n_q X).left c x = c (a3n_σ X 0 x) + c (a3n_σ X 1 x) := by
  classical
  rw [a1p_pushforward_apply_eq_sum (a3n_q X).left c x {a3n_σ X 0 x, a3n_σ X 1 x}]
  · rw [Finset.sum_pair (a3n_σ0_ne_σ1 X x x), a3n_degree_q_σ, a3n_degree_q_σ]
    push_cast
    ring
  · rintro d ⟨hd, hcd⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hd
    rcases hc d hcd with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · rw [a3n_q_σ_apply] at hd
      subst hd
      simp
    · rw [a3n_q_σ_apply] at hd
      subst hd
      simp
  · intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact a3n_q_σ_apply X 0 x
    · exact a3n_q_σ_apply X 1 x

open Classical in
/-- A projection formula along the sections: for a cycle `c` on `X × ℙ¹` supported on
`σ₀(X) ∪ σ₁(X)`, `q_*(c · [V × ℙ¹]) = (q_* c) · [V]`.
Source: Fulton, *Intersection Theory*, second edition, Proposition 8.1.1 (c) and Example 20.4.3;
Serre, *Algèbre locale, multiplicités*, Chapitre V, C. -/
theorem a3o_push_intersect (c : AlgebraicCycle (a3n_T X).left ℚ)
    (hc : ∀ d, c d ≠ 0 → d ∈ Set.range (a3n_σ X 0) ∪ Set.range (a3n_σ X 1)) (v : X.left) :
    a1p_pushforward (a3n_q X).left (a3i_intersect (a3n_T X).left c
        (Function.locallyFinsuppWithin.single (a3n_b X v) 1)) =
      a3i_intersect X.left (a1p_pushforward (a3n_q X).left c)
        (Function.locallyFinsuppWithin.single v 1) := by
  classical
  have hNX : IsNoetherian X.left := by
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : CompactSpace X.left := by
      have h := QuasiCompact.isCompact_preimage (f := X.hom) _ isOpen_univ isCompact_univ
      rw [Set.preimage_univ] at h
      exact isCompact_univ_iff.mp h
    exact ⟨⟩
  set s := (a3c_support_finite c).toFinset
  have hs : ∀ d ∉ s, c d = 0 := fun d hd => by simpa [s] using hd
  have hsσ : ∀ d ∈ s, d ∈ Set.range (a3n_σ X 0) ∪ Set.range (a3n_σ X 1) := fun d hd =>
    hc d (by simpa [s] using hd)
  set E := s.image (a3n_q X).left
  set W := a3i_intersect (a3n_T X).left c (Function.locallyFinsuppWithin.single (a3n_b X v) 1)
  have hW : ∀ τ, W τ = ∑ d ∈ s, c d * a3i_intersectPrime (a3n_T X).left d (a3n_b X v) τ :=
    fun τ => a3z_intersect_single_apply _ c _ s hs τ
  -- `W` lives on `σ₀(X) ∪ σ₁(X)`
  have hWsupp : ∀ τ, W τ ≠ 0 → τ ∈ Set.range (a3n_σ X 0) ∪ Set.range (a3n_σ X 1) := by
    intro τ hτ
    rw [hW] at hτ
    obtain ⟨d, hd, hd0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    have hi : a3i_intersectPrime (a3n_T X).left d (a3n_b X v) τ ≠ 0 := fun h0 =>
      hd0 (by rw [h0, mul_zero])
    have hdτ := (a3y_comps_spec _ _ (a3z_intersectPrime_ne_zero _ _ _ τ hi)).1
    rcases hsσ d hd with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact Or.inl (a3n_mem_range_σ_of_specializes X 0 hdτ)
    · exact Or.inr (a3n_mem_range_σ_of_specializes X 1 hdτ)
  -- the coefficients along the sections
  have hcross : ∀ (c₁ c₂ : ℂ), (c₁ = 0 ∧ c₂ = 1) ∨ (c₁ = 1 ∧ c₂ = 0) → ∀ (e x : X.left),
      a3i_intersectPrime (a3n_T X).left (a3n_σ X c₁ e) (a3n_b X v) (a3n_σ X c₂ x) = 0 := by
    intro c₁ c₂ hc e x
    refine a3n_intersectPrime_σ_of_not_mem X c₁ e v _ ?_
    rintro ⟨x', hx'⟩
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact a3n_σ0_ne_σ1 X x' x hx'
    · exact a3n_σ0_ne_σ1 X x x' hx'.symm
  have hWσ : ∀ (c₁ c₂ : ℂ), (c₁ = 0 ∧ c₂ = 1) ∨ (c₁ = 1 ∧ c₂ = 0) → ∀ x : X.left,
      W (a3n_σ X c₁ x) = ∑ d ∈ s.filter (· ∈ Set.range (a3n_σ X c₁)),
        c d * a3i_intersectPrime X.left ((a3n_q X).left d) v x := by
    intro c₁ c₂ hc x
    rw [hW, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    split_ifs with hd'
    · obtain ⟨e, rfl⟩ := hd'
      rw [a3n_intersectPrime_σ, a3n_q_σ_apply]
    · have hd2 : d ∈ Set.range (a3n_σ X c₂) := by
        rcases hsσ d hd with h | h
        · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd h hd'
          · exact h
        · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h
          · exact absurd h hd'
      obtain ⟨e, rfl⟩ := hd2
      rw [hcross c₂ c₁ (by rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp) e x, mul_zero]
  -- reindexing along `q`
  have hkey : ∀ (c₁ : ℂ) (g : X.left → ℚ),
      ∑ d ∈ s.filter (· ∈ Set.range (a3n_σ X c₁)), c d * g ((a3n_q X).left d) =
        ∑ e ∈ E, c (a3n_σ X c₁ e) * g e := by
    intro c₁ g
    have hinj : Set.InjOn (a3n_q X).left (s.filter (· ∈ Set.range (a3n_σ X c₁))) := by
      intro d hd d' hd' he
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hd hd'
      obtain ⟨e, rfl⟩ := hd.2
      obtain ⟨e', rfl⟩ := hd'.2
      rw [a3n_q_σ_apply, a3n_q_σ_apply] at he
      rw [he]
    rw [← Finset.sum_subset (s₁ := (s.filter (· ∈ Set.range (a3n_σ X c₁))).image (a3n_q X).left)
      (Finset.image_subset_image (Finset.filter_subset _ _)), Finset.sum_image hinj]
    · refine Finset.sum_congr rfl fun d hd => ?_
      simp only [Finset.mem_filter] at hd
      obtain ⟨e, rfl⟩ := hd.2
      rw [a3n_q_σ_apply]
    · intro e _ he
      have : a3n_σ X c₁ e ∉ s := fun hs' => he (Finset.mem_image.2
        ⟨a3n_σ X c₁ e, Finset.mem_filter.2 ⟨hs', ⟨e, rfl⟩⟩, a3n_q_σ_apply X c₁ e⟩)
      rw [hs _ this, zero_mul]
  -- `(q_* c)` vanishes off `E`
  have hpush := a3o_pushforward_apply X c hc
  have hE : ∀ e ∉ E, a1p_pushforward (a3n_q X).left c e = 0 := by
    intro e he
    rw [hpush]
    have h0 : a3n_σ X 0 e ∉ s := fun hs' => he (Finset.mem_image.2 ⟨_, hs', a3n_q_σ_apply X 0 e⟩)
    have h1 : a3n_σ X 1 e ∉ s := fun hs' => he (Finset.mem_image.2 ⟨_, hs', a3n_q_σ_apply X 1 e⟩)
    rw [hs _ h0, hs _ h1, add_zero]
  ext x
  rw [a3o_pushforward_apply X W hWsupp x, a3z_intersect_single_apply X.left _ v E hE x,
    hWσ 0 1 (Or.inl ⟨rfl, rfl⟩) x, hWσ 1 0 (Or.inr ⟨rfl, rfl⟩) x,
    hkey 0 (fun e => a3i_intersectPrime X.left e v x),
    hkey 1 (fun e => a3i_intersectPrime X.left e v x), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hpush]
  ring

end projection

section fibrePoints
variable (X : Over (Spec ↧ℂ))

theorem a3n_h_σ (c : ℂ) (n : ℤ) (hn : (n : ℂ) = c) (x : X.left) :
    ∃ q : Spec (.of a3m_Away1), g3c_chartι 1 0 q = a3n_h X (a3n_σ X c x) ∧
      a3m_t₁ - n ∈ q.asIdeal := by
  refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ)
    (B := a3n_A 0)).toRingHom) (Spec.map (CommRingCat.ofHom (a3n_evc c)) a3n_o), ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (a3n_σ X c), a3n_σ_p, Scheme.Hom.comp_apply,
      show X.hom x = a3n_o from Subsingleton.elim _ _, a3n_pt, Scheme.Hom.comp_apply, a3n_π_κ]
  · change Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ) (B := a3n_A 0) (a3m_t₁ - n) ∈
      (⊥ : Ideal ℂ).comap (a3n_evc c)
    rw [Ideal.mem_comap, Ideal.mem_bot, map_sub, map_intCast, ← a3n_chartEquiv_X]
    simp [a3n_evc, hn]

theorem a3n_h_σ0 (x : X.left) : a3n_h X (a3n_σ X 0 x) ∈ a3m_Z0 := by
  obtain ⟨q, hq, ht⟩ := a3n_h_σ X 0 0 (by simp) x
  exact ⟨q, hq, by simpa using ht⟩

theorem a3n_h_σ1 (x : X.left) : a3n_h X (a3n_σ X 1 x) ∈ a3m_Zinf := by
  obtain ⟨q, hq, ht⟩ := a3n_h_σ X 1 1 (by simp) x
  exact ⟨q, hq, by simpa using ht⟩

/-- Points over `t₁ ∈ {0, 1}` lie in the chart `t₁ ≠ ∞`. -/
theorem a3n_p_mem_chart (τ : (a3n_T X).left) (h : a3n_h X τ ∈ a3m_Z0 ∨ a3n_h X τ ∈ a3m_Zinf) :
    a3n_p X τ ∈ Set.range (a3m_Pnκ 1 0) := by
  rcases h with h | h
  · rw [a3n_eq_σ0 X τ h, ← Scheme.Hom.comp_apply, a3n_σ_p, Scheme.Hom.comp_apply, a3n_pt,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · rw [a3n_eq_σ1 X τ h, ← Scheme.Hom.comp_apply, a3n_σ_p, Scheme.Hom.comp_apply, a3n_pt,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

end fibrePoints

section family
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
  (y : (a3n_T X).left) (hy : a3n_h X y = genericPoint (g3c_P 1))

omit [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom] in
include hy in
theorem a3o_hgen : (cycleComponentι (a3n_T X).left y ≫ a3n_h X)
    (genericPoint (cycleComponent (a3n_T X).left y)) = genericPoint (g3c_P 1) := by
  rw [Scheme.Hom.comp_apply, a3m_cycleComponentι_genericPoint, hy]

/-- The coordinate `t` of `a3m_P1curve` restricted to `Y = closure {y}`.
Source: Fulton, *Intersection Theory*, second edition, §1.6 (the rational function `t` on a
subvariety of `X × ℙ¹` dominating `ℙ¹`). -/
def a3o_φ : (cycleComponent (a3n_T X).left y).functionField :=
  a3m_pullbackFF (cycleComponentι (a3n_T X).left y ≫ a3n_h X) (a3o_hgen X y hy) a3m_P1curve.t

example : (cycleComponent (a3n_T X).left y).functionField := a3o_φ X y hy

omit [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom] in
theorem a3o_φ_ne_zero : a3o_φ X y hy ≠ 0 :=
  a3m_pullbackFF_ne_zero _ _ _ a3m_P1curve.t_ne_zero

/-- `[div (t|_Y)]` on `X × ℙ¹`; its push-forward to `X` is `[Y(0)] − [Y(1)]`.
Source: Fulton, *Intersection Theory*, second edition, §1.6. -/
def a3o_cyc : AlgebraicCycle (a3n_T X).left ℚ :=
  a2_principalCycle (a3n_T X).left ℚ y (a3o_φ X y hy)

example : AlgebraicCycle (a3n_T X).left ℚ := a3o_cyc X y hy

omit [IsIntegral X.left] [Smooth X.hom] in
/-- `[div (t|_Y)]` lives on the fibres over `t₁ = 0` and `t₁ = 1`. -/
theorem a3o_cyc_supp (d : (a3n_T X).left) (hd : a3o_cyc X y hy d ≠ 0) :
    d ∈ Set.range (a3n_σ X 0) ∪ Set.range (a3n_σ X 1) := by
  obtain ⟨D, rfl, hD1, heq⟩ := a3z_principalCycle_ne_zero (a3n_T X).left y (a3o_φ X y hy)
    (a3o_φ_ne_zero X y hy) d hd
  have hord : (cycleComponent (a3n_T X).left y).ord (a3o_φ X y hy) D ≠ 0 := by
    intro h0
    apply hd
    change a2_principalCycle (a3n_T X).left ℚ y (a3o_φ X y hy) _ = 0
    rw [heq, h0]
    simp
  by_cases h0 : a3n_h X (cycleComponentι (a3n_T X).left y D) ∈ a3m_Z0
  · exact Or.inl ⟨_, (a3n_eq_σ0 X _ h0).symm⟩
  by_cases hinf : a3n_h X (cycleComponentι (a3n_T X).left y D) ∈ a3m_Zinf
  · exact Or.inr ⟨_, (a3n_eq_σ1 X _ hinf).symm⟩
  exfalso
  obtain ⟨a, ha, hat⟩ := a3m_P1curve.unit _ h0 hinf
  exact hord (a3m_ord_pullbackFF_eq_zero (cycleComponentι (a3n_T X).left y ≫ a3n_h X)
    (a3o_hgen X y hy) a3m_P1curve.t D a ha hat)

omit [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom] in
/-- The restriction to `Y` of the pull-back of a germ representing `t` is `t|_Y`. -/
theorem a3o_germ_pullback (τ : (a3n_T X).left) (TY : cycleComponent (a3n_T X).left y)
    (hTY : cycleComponentι (a3n_T X).left y TY = τ)
    (a₀ : a3m_P1curve.C.presheaf.stalk (a3n_h X τ))
    (hat : a3m_P1curve.C.presheaf.stalkSpecializes (genericPoint_specializes _) a₀ =
      a3m_P1curve.t) :
    a3y_germ y TY hTY ((a3n_h X).stalkMap τ a₀) = a3o_φ X y hy := by
  subst hTY
  rw [a3y_germ_self]
  have h := a3m_pullbackFF_eq (cycleComponentι (a3n_T X).left y ≫ a3n_h X)
    (a3o_hgen X y hy) a3m_P1curve.t TY a₀ hat
  rw [a3o_φ, h, Scheme.Hom.stalkMap_comp (cycleComponentι (a3n_T X).left y) (a3n_h X) TY]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom] in
/-- Away from `t₁ ∈ {0, 1}` the function `t|_Y` is a unit. -/
theorem a3o_unitAt (z : (a3n_T X).left) (hz : y ⤳ z) (h0 : a3n_h X z ∉ a3m_Z0)
    (hinf : a3n_h X z ∉ a3m_Zinf) : a3z_UnitAt y (a3o_φ X y hy) z := by
  obtain ⟨zY, hzY⟩ := a3z_exists_pt y hz
  obtain ⟨a₀, ha₀, hat⟩ := a3m_P1curve.unit _ h0 hinf
  refine ⟨zY, hzY, (a3n_h X).stalkMap z a₀, 1, ?_, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact ha₀.map _
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact isUnit_one
  · rw [map_one, mul_one]
    exact a3o_germ_pullback X y hy z zY hzY a₀ hat

end family

section localIdentity
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
  (y : (a3n_T X).left) (hy : a3n_h X y = genericPoint (g3c_P 1))

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Away from `t₁ ∈ {0, 1}`, the divisor of the restriction of `t|_Y` to a component vanishes. -/
theorem a3o_restriction_ord_zero (b : (a3n_T X).left) (z : (a3n_T X).left)
    (hz : z ∈ a3y_comps y b) (ψ : (cycleComponent (a3n_T X).left z).functionField)
    (hψ : a3z_IsRestriction y (a3o_φ X y hy) z ψ) (hψ0 : ψ ≠ 0) (τ : (a3n_T X).left)
    (h0 : a3n_h X τ ∉ a3m_Z0) (hinf : a3n_h X τ ∉ a3m_Zinf) :
    a2_principalCycle (a3n_T X).left ℚ z ψ τ = 0 := by
  by_contra hne
  obtain ⟨TZ, hTZ, hTZ1, heq⟩ := a3z_principalCycle_ne_zero (a3n_T X).left z ψ hψ0 τ hne
  have hzτ : z ⤳ τ := hTZ ▸ a3z_specializes_pt z TZ
  have hyτ : y ⤳ τ := (a3y_comps_spec _ _ hz).1.trans hzτ
  obtain ⟨TY, hTY⟩ := a3z_exists_pt y hyτ
  obtain ⟨a₀, ha₀, hat⟩ := a3m_P1curve.unit _ h0 hinf
  have hab : a3y_germ y TY hTY ((a3n_h X).stalkMap τ a₀) =
      a3o_φ X y hy * a3y_germ y TY hTY 1 := by
    rw [map_one, mul_one]
    exact a3o_germ_pullback X y hy τ TY hTY a₀ hat
  have hres := a3z_restriction_at y hψ hzτ TY hTY TZ hTZ _ 1 hab
  rw [map_one, mul_one] at hres
  subst hTZ
  rw [a3y_germ_self] at hres
  have hord : (cycleComponent (a3n_T X).left z).ord ψ TZ = 0 := by
    rw [← hres]
    exact a3m_ord_algebraMap_of_isUnit TZ _ ((ha₀.map _).map _)
  rw [heq, hord] at hne
  exact hne (by simp)

open Classical in
/-- The cycle form of Fulton, Theorem 2.4, on `X × ℙ¹` for `t|_Y`, when the components of
`Y ∩ (V × ℙ¹)` over `ℙ¹ ∖ {∞}` meet properly: `[div t|_Y] · [V × ℙ¹] = Σ_Z i(Z) [div (t|_Z)]`. -/
theorem a3o_identity (v : X.left)
    (hi : ∀ z ∈ a3y_comps y (a3n_b X v), a3n_p X z ∈ Set.range (a3m_Pnκ 1 0) →
      coheight z = coheight y + coheight (a3n_b X v))
    (hii : ∀ d, a3o_cyc X y hy d ≠ 0 → a3i_MeetProperly (a3n_T X).left d (a3n_b X v))
    (ψ : (z : (a3n_T X).left) → (cycleComponent (a3n_T X).left z).functionField)
    (hψ : ∀ z ∈ a3y_comps y (a3n_b X v), ψ z ≠ 0 ∧ a3z_IsRestriction y (a3o_φ X y hy) z (ψ z)) :
    a3i_intersect (a3n_T X).left (a3o_cyc X y hy)
        (Function.locallyFinsuppWithin.single (a3n_b X v) 1) =
      ∑ z ∈ (a3y_comps_finite y (a3n_b X v)).toFinset,
        (a2_principalCycle (a3n_T X).left ℚ z (ψ z)).mapRange
          ((a3i_serreMult (a3n_T X).left z y (a3n_b X v) : ℚ) * ·) (mul_zero _) := by
  classical
  set b := a3n_b X v
  set c := a3o_cyc X y hy with hc
  set s := (a3c_support_finite c).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by simpa [s] using hu
  ext τ
  rw [a3z_intersect_single_apply _ c b s hs τ, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply]
  simp only [Function.locallyFinsuppWithin.mapRange_apply]
  by_cases hτ : a3n_h X τ ∈ a3m_Z0 ∨ a3n_h X τ ∈ a3m_Zinf
  · -- over `t₁ ∈ {0, 1}`: the components through `τ` meet properly
    have hloc : ∀ z ∈ a3y_comps y b, z ⤳ τ → coheight z = coheight y + coheight b := by
      intro z hz hzτ
      refine hi z hz ?_
      have hopen : IsOpen (Set.range (a3m_Pnκ 1 0)) := (a3m_Pnκ 1 0).isOpenEmbedding.isOpen_range
      exact (hzτ.map (a3n_p X).continuous).mem_open hopen (a3n_p_mem_chart X τ hτ)
    by_cases hP : y ⤳ τ ∧ b ⤳ τ ∧ coheight τ = coheight y + coheight b + 1
    · obtain ⟨hyτ, hbτ, hT⟩ := hP
      rw [show (∑ u ∈ s, c u * a3i_intersectPrime (a3n_T X).left u b τ) =
          ∑ u ∈ s, a2_principalCycle (a3n_T X).left ℚ y (a3o_φ X y hy) u *
            a3i_intersectPrime (a3n_T X).left u b τ from rfl,
        a3z_principal_point (a3n_T X) y b τ hyτ hbτ hloc hT (a3o_φ X y hy)
        (a3o_φ_ne_zero X y hy) hii ψ (fun z hz => (hψ z hz).2) s hs]
      simp only [a3y_compsAt]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs with hzT
      · rfl
      · rw [a3y_principalCycle_apply_of_not_mem (a3n_T X).left z (ψ z) τ, mul_zero]
        rintro ⟨TZ, rfl⟩
        exact hzT (a3z_specializes_pt z TZ)
    · have hL : ∀ u ∈ s, c u * a3i_intersectPrime (a3n_T X).left u b τ = 0 := by
        intro u _
        by_cases hcu : c u = 0
        · rw [hcu, zero_mul]
        by_cases hip : a3i_intersectPrime (a3n_T X).left u b τ = 0
        · rw [hip, mul_zero]
        exfalso
        obtain ⟨D, hD', hD1, -⟩ := a3z_principalCycle_ne_zero (a3n_T X).left y (a3o_φ X y hy)
          (a3o_φ_ne_zero X y hy) u hcu
        have hcohu : coheight u = coheight y + 1 := by
          rw [← hD']
          exact (a3y_coheight_eq_one_iff (a3n_T X) y D).1 hD1
        have hyu : y ⤳ u := hD' ▸ a3z_specializes_pt y D
        have hTc := a3z_intersectPrime_ne_zero (a3n_T X).left u b τ hip
        obtain ⟨huT, hbT, -⟩ := a3y_comps_spec u b hTc
        refine hP ⟨hyu.trans huT, hbT, ?_⟩
        rw [a3y_coheight_comps u b (hii u hcu) hTc, hcohu, add_right_comm]
      have hR : ∀ z ∈ (a3y_comps_finite y b).toFinset,
          (a3i_serreMult (a3n_T X).left z y b : ℚ) *
            a2_principalCycle (a3n_T X).left ℚ z (ψ z) τ = 0 := by
        intro z hz
        rw [Set.Finite.mem_toFinset] at hz
        by_cases h0 : a2_principalCycle (a3n_T X).left ℚ z (ψ z) τ = 0
        · rw [h0, mul_zero]
        exfalso
        obtain ⟨TZ, hTZ, hTZ1, -⟩ := a3z_principalCycle_ne_zero (a3n_T X).left z (ψ z)
          (hψ z hz).1 τ h0
        have hzT : z ⤳ τ := hTZ ▸ a3z_specializes_pt z TZ
        obtain ⟨hwz, hvz, -⟩ := a3y_comps_spec y b hz
        refine hP ⟨hwz.trans hzT, hvz.trans hzT, ?_⟩
        rw [← hTZ, (a3y_coheight_eq_one_iff (a3n_T X) z TZ).1 hTZ1, hloc z hz hzT]
      rw [Finset.sum_eq_zero hL, Finset.sum_eq_zero hR]
  · -- elsewhere both sides vanish
    have hτ0 : a3n_h X τ ∉ a3m_Z0 := fun h => hτ (Or.inl h)
    have hτ1 : a3n_h X τ ∉ a3m_Zinf := fun h => hτ (Or.inr h)
    have hL : ∀ u ∈ s, c u * a3i_intersectPrime (a3n_T X).left u b τ = 0 := by
      intro u _
      by_cases hcu : c u = 0
      · rw [hcu, zero_mul]
      by_cases hip : a3i_intersectPrime (a3n_T X).left u b τ = 0
      · rw [hip, mul_zero]
      exfalso
      have huτ := (a3y_comps_spec u b (a3z_intersectPrime_ne_zero _ u b τ hip)).1
      rcases a3o_cyc_supp X y hy u hcu with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · obtain ⟨x, rfl⟩ := a3n_mem_range_σ_of_specializes X 0 huτ
        exact hτ0 (a3n_h_σ0 X x)
      · obtain ⟨x, rfl⟩ := a3n_mem_range_σ_of_specializes X 1 huτ
        exact hτ1 (a3n_h_σ1 X x)
    have hR : ∀ z ∈ (a3y_comps_finite y b).toFinset,
        (a3i_serreMult (a3n_T X).left z y b : ℚ) *
          a2_principalCycle (a3n_T X).left ℚ z (ψ z) τ = 0 := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      rw [a3o_restriction_ord_zero X y hy b z hz (ψ z) (hψ z hz).2 (hψ z hz).1 τ hτ0 hτ1,
        mul_zero]
    rw [Finset.sum_eq_zero hL, Finset.sum_eq_zero hR]

end localIdentity

section specialize
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
  (y : (a3n_T X).left) (hy : a3n_h X y = genericPoint (g3c_P 1))

open Classical in
/-- **Specialization.** For `Y = closure {y} ⊆ X × ℙ¹` dominating `ℙ¹`, such that the components of
`Y ∩ (V × ℙ¹)` over `ℙ¹ ∖ {∞}` meet properly, the components of `div (t|_Y)` meet `V × ℙ¹`
properly and no component of `Y ∩ (V × ℙ¹)` lies over `t₁ ∈ {0, 1}`, the cycle
`([Y(0)] − [Y(1)]) · [V] = (q_*[div t|_Y]) · [V]` is rationally equivalent to zero on `X`.
Source: Fulton, *Intersection Theory*, second edition, Theorem 1.4, Theorem 2.4 and §10.1;
S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §1 (the
boundary map on `z^p(X, 1)`). -/
theorem a3o_specialize (v : X.left)
    (hi : ∀ z ∈ a3y_comps y (a3n_b X v), a3n_p X z ∈ Set.range (a3m_Pnκ 1 0) →
      coheight z = coheight y + coheight (a3n_b X v))
    (hii : ∀ d, a3o_cyc X y hy d ≠ 0 → a3i_MeetProperly (a3n_T X).left d (a3n_b X v))
    (hiii : ∀ z ∈ a3y_comps y (a3n_b X v), a3n_h X z ∉ a3m_Z0 ∧ a3n_h X z ∉ a3m_Zinf) :
    a3i_intersect X.left (a1p_pushforward (a3n_q X).left (a3o_cyc X y hy))
      (Function.locallyFinsuppWithin.single v 1) ∈ a3i_ratAll X.left := by
  classical
  have hex : ∀ z, ∃ ψ : (cycleComponent (a3n_T X).left z).functionField,
      z ∈ a3y_comps y (a3n_b X v) → ψ ≠ 0 ∧ a3z_IsRestriction y (a3o_φ X y hy) z ψ := by
    intro z
    by_cases hz : z ∈ a3y_comps y (a3n_b X v)
    · obtain ⟨ψ, h1, h2⟩ := a3z_exists_restriction y (a3o_unitAt X y hy z
        (a3y_comps_spec _ _ hz).1 (hiii z hz).1 (hiii z hz).2)
      exact ⟨ψ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose ψ hψ using hex
  rw [← a3o_push_intersect X _ (a3o_cyc_supp X y hy) v, a3o_identity X y hy v hi hii ψ hψ]
  exact a3o_pushforward_ratAll (a3n_q X) _ (a3z_sum_principal_mem (a3n_T X) _ _ ψ
    fun z hz => (hψ z (by simpa using hz)).1)

end specialize

end HodgeLean.Adapters
