import HodgeLean.Adapters.IntersectionProductBlochCharts

/-! # Roberts' main lemma over the line, on the points of `X × 𝔸¹`

Stage A3.3. Through the dictionary of `IntersectionProductBlochCharts`, Roberts' main lemma over
the line (`a3h_roberts_rel_X`) becomes a statement about points of `X × 𝔸¹ ⊂ X × ℙ¹` and the
excess bound `a3k_ExcessLE` of the Bloch files: if a point `y` of `X × 𝔸¹`, lying over neither
`t = 0` nor `t = 1`, has excess at most `k + 1` against the faces of `β`, then for a generic
projection `ℓ × id` every other point `y'` of `X × 𝔸¹` with the same image has excess at most `k`
(`a3h_roberts_points`). The cone dimensions of the dictionary are turned into coheights by
`a3h_dim_P`.

Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma; S. Bloch, *The moving lemma for
higher Chow groups*, J. Algebraic Geom. 3 (1994), §2. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

section dims

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

/-- The cone of a point `y` of `X × 𝔸¹` has dimension `n + 2 - codim y`. -/
theorem a3h_dim_P (n : ℕ) (hn : height (genericPoint X.left) = n) (y : (a3n_T X).left)
    (hy : y ∈ a3h_U X) :
    ∃ c : ℕ, coheight y = c ∧ c ≤ n + 1 ∧
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y hy) =
        (n + 2 - c : ℕ) := by
  have h1 := a3n_height_add_coheight_T X n hn y
  have h2 := a3h_height_add_one X y hy
  have hh : height y ≠ ⊤ := fun hh => by rw [hh, top_add] at h1; exact ENat.top_ne_natCast _ h1
  have hc : coheight y ≠ ⊤ := fun hc => by rw [hc, add_top] at h1; exact ENat.top_ne_natCast _ h1
  obtain ⟨h, hh'⟩ := ENat.ne_top_iff_exists.mp hh
  obtain ⟨c, hc'⟩ := ENat.ne_top_iff_exists.mp hc
  rw [← hh', ← hc'] at h1
  have e : h + c = n + 1 := by exact_mod_cast h1
  refine ⟨c, hc'.symm, by omega, ?_⟩
  rw [← h2, ← hh', show n + 2 - c = h + 1 by omega]
  norm_cast

/-- The relative cone `I_X[t]` has dimension `n + 2`. -/
theorem a3h_dim_IXr (n : ℕ) (hn : height (genericPoint X.left) = n) :
    ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_IXr (a3s_IX X)) =
      (n + 2 : ℕ) := by
  have hd : ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) = (n + 1 : ℕ) := by
    rw [← a3s_height_add_one X (genericPoint X.left), hn]
    rfl
  rw [(a3h_IXr_isPrime_dim (a3s_IX X)).2, hd]
  norm_cast

theorem a3h_IXr_le_P (y : (a3n_T X).left) (hy : y ∈ a3h_U X) :
    a3h_IXr (a3s_IX X) ≤ a3h_P X y hy := by
  rw [a3h_IXr, Ideal.map_le_iff_le_comap]
  intro F hF
  rw [Ideal.mem_comap, ← a3h_fst_prime X y hy]
  exact a3s_IX_le X _ hF

omit [IsIntegral X.left] in
/-- The prime of a point of `X × 𝔸¹` is relevant. -/
theorem a3h_P_relevant (y : (a3n_T X).left) (hy : y ∈ a3h_U X) :
    ∃ j, MvPolynomial.X (Sum.inl j) ∉ a3h_P X y hy := by
  obtain ⟨j, hj⟩ := a3s_relevant X ((a3n_q X).left y)
  exact ⟨j, fun h => hj ((a3h_fst_prime X y hy _).2 (by rw [rename_X]; exact h))⟩

theorem a3h_withBot_le {a b : ℕ} (h : ((a : WithBot ℕ∞)) ≤ b) : a ≤ b := by
  exact_mod_cast h

/-- Coheight bounds are cone dimension bounds. -/
theorem a3h_dims_iff (n : ℕ) (hn : height (genericPoint X.left) = n)
    (y w z : (a3n_T X).left) (hy : y ∈ a3h_U X) (hw : w ∈ a3h_U X) (hz : z ∈ a3h_U X)
    (k : ℕ) :
    coheight y + coheight w ≤ coheight z + k ↔
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X z hz) +
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_IXr (a3s_IX X)) ≤
        ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y hy) +
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X w hw) + k := by
  obtain ⟨cy, hcy, hly, hdy⟩ := a3h_dim_P X n hn y hy
  obtain ⟨cw, hcw, hlw, hdw⟩ := a3h_dim_P X n hn w hw
  obtain ⟨cz, hcz, hlz, hdz⟩ := a3h_dim_P X n hn z hz
  rw [hcy, hcw, hcz, hdy, hdw, hdz, a3h_dim_IXr X n hn]
  constructor
  · intro h
    have h' : cy + cw ≤ cz + k := by exact_mod_cast h
    have : n + 2 - cz + (n + 2) ≤ n + 2 - cy + (n + 2 - cw) + k := by omega
    exact_mod_cast this
  · intro h
    have h' : n + 2 - cz + (n + 2) ≤ n + 2 - cy + (n + 2 - cw) + k :=
      a3h_withBot_le (by exact_mod_cast h)
    have : cy + cw ≤ cz + k := by omega
    exact_mod_cast this

end dims

section fibres

variable {σ' : Type}

/-- `t - c` lies in `P[t] + (t - a)` only for `c = a`. -/
theorem a3h_X_sub_C_mem (P : Ideal (MvPolynomial σ' ℂ)) [P.IsPrime] (a c : ℂ)
    (h : MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∈ Ideal.map (rename Sum.inl) P ⊔
      Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C a}) : c = a := by
  by_contra hca
  rw [← a3h_ker_evt, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at h
  have he : (a3h_evt (σ' := σ') a).toRingHom (MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c) =
      MvPolynomial.C (a - c) := by
    simp [a3h_evt]
  rw [he] at h
  have hu : IsUnit (MvPolynomial.C (σ := σ') (a - c)) :=
    (isUnit_iff_ne_zero.2 (sub_ne_zero.2 (Ne.symm hca))).map _
  exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _ h hu)

/-- `t - c` never lies in `P[t]`. -/
theorem a3h_X_sub_C_not_mem (P : Ideal (MvPolynomial σ' ℂ)) [P.IsPrime] (c : ℂ) :
    MvPolynomial.X (Sum.inr ()) - MvPolynomial.C c ∉ Ideal.map (rename Sum.inl) P := by
  intro h
  have := a3h_X_sub_C_mem P (c + 1) c (Ideal.mem_sup_left h)
  exact one_ne_zero (by linear_combination -this)

end fibres

section points

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The primes of the faces `V × ℙ¹`, `V × {0}`, `V × {1}` of the components `V` of `β`. -/
def a3h_SW (β : AlgebraicCycle X.left ℚ) :
    Finset (Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ)) := by
  classical
  exact (a3c_support_finite β).toFinset.biUnion fun v =>
    {a3h_P X (a3n_b X v) (a3h_b_mem_U X v), a3h_P X (a3n_σ X 0 v) (a3h_σ0_mem_U X v),
      a3h_P X (a3n_σ X 1 v) (a3h_σ1_mem_U X v)}

theorem a3h_mem_SW (β : AlgebraicCycle X.left ℚ)
    (W : Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ)) :
    W ∈ a3h_SW X β ↔ ∃ v, β v ≠ 0 ∧ (W = a3h_P X (a3n_b X v) (a3h_b_mem_U X v) ∨
      W = a3h_P X (a3n_σ X 0 v) (a3h_σ0_mem_U X v) ∨
      W = a3h_P X (a3n_σ X 1 v) (a3h_σ1_mem_U X v)) := by
  classical
  simp [a3h_SW]

/-- **Roberts' main lemma over the line, on points.** Let `y` be a point of `X × 𝔸¹`, over
neither `t = 0` nor `t = 1`, with excess at most `k + 1` against the faces of `β`. For a generic
`ℓ`, the projection `ℓ × id` of the relative cone is finite, and every other point `y'` of
`X × 𝔸¹` whose prime has the same image as that of `y` has excess at most `k`.
Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma; S. Bloch, *The moving lemma for
higher Chow groups*, J. Algebraic Geom. 3 (1994), §2. -/
theorem a3h_roberts_points (n : ℕ) (hn : height (genericPoint X.left) = n)
    (β : AlgebraicCycle X.left ℚ) (y : (a3n_T X).left) (hy : y ∈ a3h_U X)
    (h0 : a3n_h X y ∉ a3m_Z0) (h1 : a3n_h X y ∉ a3m_Zinf) (k : ℕ)
    (hexc : a3k_ExcessLE X β y (k + 1)) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ((Ideal.Quotient.mk (a3h_IXr (a3s_IX X))).comp (a3r_lin (a3h_block a)).toRingHom).Finite ∧
      ∀ y' (hy' : y' ∈ a3h_U X), (a3h_P X y' hy').comap (a3r_lin (a3h_block a)) =
        (a3h_P X y hy).comap (a3r_lin (a3h_block a)) → y' ≠ y → a3k_ExcessLE X β y' k} := by
  classical
  refine (a3h_roberts_rel_X X n hn (a3h_P X y hy) (a3h_IXr_le_P X y hy) (a3h_SW X β) ?_ ?_ k
    ?_).mono ?_
  · intro W hW
    obtain ⟨v, -, h | h | h⟩ := (a3h_mem_SW X β W).1 hW <;> rw [h] <;> infer_instance
  · intro W hW c
    obtain ⟨v, -, h | h | h⟩ := (a3h_mem_SW X β W).1 hW
    · right
      rw [h, a3h_P_b]
      exact a3h_X_sub_C_not_mem _ c
    · by_cases hc : c = 0
      · left
        rw [hc, map_zero, sub_zero, ← a3h_mem_Z0]
        exact h0
      · right
        rw [h, a3h_P_σ0]
        exact fun hm => hc (a3h_X_sub_C_mem _ 0 c hm)
    · by_cases hc : c = 1
      · left
        rw [hc, map_one, ← a3h_mem_Zinf]
        exact h1
      · right
        rw [h, a3h_P_σ1]
        exact fun hm => hc (a3h_X_sub_C_mem _ 1 c hm)
  · intro W hW 𝔶 h𝔶 hrel
    have key : ∀ w (hw : w ∈ a3h_U X), W = a3h_P X w hw →
        (∀ z ∈ a3y_comps y w, z ∈ a3h_U X →
          coheight y + coheight w ≤ coheight z + (k + 1 : ℕ)) →
        ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ 𝔶) +
            ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_IXr (a3s_IX X)) ≤
          ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y hy) +
            ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ W) + (k + 1 : ℕ) := by
      intro w hw hW' hcomps
      subst hW'
      obtain ⟨z, hz, hzc, rfl⟩ := a3h_comp_of_minimal X y w hy hw 𝔶 h𝔶 hrel
      exact (a3h_dims_iff X n hn y w z hy hw hz (k + 1)).1 (hcomps z hzc hz)
    obtain ⟨v, hv, h | h | h⟩ := (a3h_mem_SW X β W).1 hW
    · exact key _ _ h fun z hzc hz => (hexc v hv).1 z hzc hz
    · exact key _ _ h fun z hzc _ => (hexc v hv).2.1 z hzc
    · exact key _ _ h fun z hzc _ => (hexc v hv).2.2 z hzc
  · rintro a ⟨hfin, hR⟩
    refine ⟨hfin, fun y' hy' hcomap hne => ?_⟩
    have hdim : ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y' hy') =
        ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y hy) := by
      rw [a3r_dim_eq_of_finite _ _ hfin _ (a3h_IXr_le_P X y' hy'),
        a3r_dim_eq_of_finite _ _ hfin _ (a3h_IXr_le_P X y hy), hcomap]
    have key : ∀ w (hw : w ∈ a3h_U X), a3h_P X w hw ∈ a3h_SW X β →
        ∀ z ∈ a3y_comps y' w, ∀ hz : z ∈ a3h_U X, coheight y' + coheight w ≤ coheight z + k := by
      intro w hw hW z hzc hz
      obtain ⟨hyz, hwz, -⟩ := a3y_comps_spec _ _ hzc
      rw [a3h_dims_iff X n hn y' w z hy' hw hz k, hdim]
      refine hR (a3h_P X y' hy') inferInstance (a3h_IXr_le_P X y' hy') hcomap
        (fun h => hne (a3h_P_injective X y' y hy' hy h)) _ hW (a3h_P X z hz) inferInstance
        (sup_le ((a3h_P_le_iff X y' z hy' hz).2 hyz) ((a3h_P_le_iff X w z hw hz).2 hwz))
        (a3h_P_relevant X z hz)
    intro v hv
    refine ⟨fun z hzc hz => key _ _ ((a3h_mem_SW X β _).2 ⟨v, hv, Or.inl rfl⟩) z hzc hz,
      fun z hzc => ?_, fun z hzc => ?_⟩
    · obtain ⟨x, rfl⟩ := a3n_mem_range_σ_of_specializes X 0 (a3y_comps_spec _ _ hzc).2.1
      exact key _ _ ((a3h_mem_SW X β _).2 ⟨v, hv, Or.inr (Or.inl rfl)⟩) _ hzc
        (a3h_σ0_mem_U X x)
    · obtain ⟨x, rfl⟩ := a3n_mem_range_σ_of_specializes X 1 (a3y_comps_spec _ _ hzc).2.1
      exact key _ _ ((a3h_mem_SW X β _).2 ⟨v, hv, Or.inr (Or.inr rfl)⟩) _ hzc
        (a3h_σ1_mem_U X x)

end points

end HodgeLean.Adapters
