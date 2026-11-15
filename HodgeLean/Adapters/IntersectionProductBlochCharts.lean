import HodgeLean.Adapters.IntersectionProductBlochRobertsRel
import HodgeLean.Adapters.IntersectionProductBlochSquare

/-! # Points of `X × 𝔸¹` as homogeneous primes of `ℂ[x, t]`

Stage A3.3, the dictionary between the points of `X × ℙ¹` over `𝔸¹` and the primes of the
relative cone, in the coordinates of Roberts' main lemma over the line (`a3h_roberts_rel_X`).
The product `a3n_T X = X ×_ℂ ℙ¹_ℂ` of the Bloch files is canonically `X ×_ℤ ℙ¹_ℤ = a3m_T X.left`
(`a3h_e`), whose part over `𝔸¹` carries the line charts `a3s_LC` of the Chow lane. Transporting
them, a point `y` of `X × 𝔸¹` has the prime `a3h_P y` of `ℂ[x, t] = MvPolynomial (σ ⊕ Unit) ℂ`,
homogeneous in `x` and containing `I_X[t]`; specialization is inclusion (`a3h_P_le_iff`), heights
are cone dimensions (`a3h_height_add_one`), the point of `X` below `y` has the prime
`{F | F ∈ a3h_P y}` (`a3h_fst_prime`), and the fibres `t = 0`, `t = 1` are cut out by `t` and
`t - 1` (`a3h_mem_Z0`, `a3h_mem_Zinf`).

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5, Theorem 3.3 and Exercise 3.20;
Mathlib, `pullbackRightPullbackFstIso`. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

/-! ## The two models of `X × ℙ¹` -/

section iso

variable (X : Over (Spec ↧ℂ))

/-- `X ×_ℂ ℙ¹_ℂ ≅ X ×_ℤ ℙ¹_ℤ`, first step: pasting of pullbacks. -/
def a3h_e₁ : (a3n_T X).left ≅
    pullback (X.hom ≫ terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P 1)) :=
  pullbackRightPullbackFstIso (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P 1)) X.hom

/-- `X ×_ℂ ℙ¹_ℂ ≅ X ×_ℤ ℙ¹_ℤ`, second step: the structure maps to the terminal scheme. -/
def a3h_e₂ : pullback (X.hom ≫ terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P 1)) ≅
    a3m_T X.left :=
  pullback.congrHom (terminal.hom_ext _ _) rfl

theorem a3h_e₁_fst : (a3h_e₁ X).hom ≫ pullback.fst _ _ = (a3n_q X).left :=
  pullbackRightPullbackFstIso_hom_fst _ _ _

theorem a3h_e₁_snd : (a3h_e₁ X).hom ≫ pullback.snd _ _ = a3n_h X :=
  pullbackRightPullbackFstIso_hom_snd _ _ _

theorem a3h_e₂_fst : (a3h_e₂ X).hom ≫ pullback.fst (terminal.from X.left) (terminal.from (g3c_P 1)) =
    pullback.fst _ _ := by
  simp [a3h_e₂]

theorem a3h_e₂_snd : (a3h_e₂ X).hom ≫ pullback.snd (terminal.from X.left) (terminal.from (g3c_P 1)) =
    pullback.snd _ _ := by
  simp [a3h_e₂]

/-- `X ×_ℂ ℙ¹_ℂ ≅ X ×_ℤ ℙ¹_ℤ`, `(x, p) ↦ (x, π(p))`.
Source: Mathlib, `pullbackRightPullbackFstIso` (pasting of pullbacks). -/
def a3h_e : (a3n_T X).left ≅ a3m_T X.left := a3h_e₁ X ≪≫ a3h_e₂ X

theorem a3h_e_fst : (a3h_e X).hom ≫ pullback.fst (terminal.from X.left) (terminal.from (g3c_P 1)) =
    (a3n_q X).left := by
  rw [a3h_e, Iso.trans_hom, Category.assoc, a3h_e₂_fst, a3h_e₁_fst]

theorem a3h_e_snd : (a3h_e X).hom ≫ pullback.snd (terminal.from X.left) (terminal.from (g3c_P 1)) =
    a3n_h X := by
  rw [a3h_e, Iso.trans_hom, Category.assoc, a3h_e₂_snd, a3h_e₁_snd]

theorem a3h_e_fst_apply (y : (a3n_T X).left) :
    pullback.fst (terminal.from X.left) (terminal.from (g3c_P 1)) ((a3h_e X).hom y) =
      (a3n_q X).left y := by
  rw [← Scheme.Hom.comp_apply, a3h_e_fst]

theorem a3h_e_snd_apply (y : (a3n_T X).left) :
    pullback.snd (terminal.from X.left) (terminal.from (g3c_P 1)) ((a3h_e X).hom y) =
      a3n_h X y := by
  rw [← Scheme.Hom.comp_apply, a3h_e_snd]

/-- `X × 𝔸¹ ⊆ X × ℙ¹`, the part over the chart `t₀ ≠ 0` of `ℙ¹`. -/
def a3h_U : (a3n_T X).left.Opens := (a3n_p X) ⁻¹ᵁ (a3m_Pnκ 1 0).opensRange

theorem a3h_mem_U_iff (y : (a3n_T X).left) :
    y ∈ a3h_U X ↔ (a3h_e X).hom y ∈ a3m_U X.left := by
  change a3n_p X y ∈ Set.range (a3m_Pnκ 1 0) ↔
    pullback.snd (terminal.from X.left) (terminal.from (g3c_P 1)) ((a3h_e X).hom y) ∈
      Set.range (g3c_chartι 1 0)
  rw [a3h_e_snd_apply, a3m_Pnκ, a3m_range_prodChart]
  simp [a3n_h]

end iso

/-! ## The coordinates `ℂ[x, t]` -/

section coords

variable (σ : Type)

/-- `ℂ[x, t] = MvPolynomial (σ ⊕ Unit) ℂ ≅ ℂ[x][t]`. -/
def a3h_eqT : MvPolynomial (σ ⊕ Unit) ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial σ ℂ) :=
  (renameEquiv ℂ (Equiv.optionEquivSumPUnit.{0, 0} σ).symm).trans (optionEquivLeft ℂ σ)

variable {σ}

theorem a3h_eqT_inl (k : σ) : a3h_eqT σ (X (Sum.inl k)) = Polynomial.C (X k) := by
  simp [a3h_eqT, Equiv.optionEquivSumPUnit, optionEquivLeft_X_some]

theorem a3h_eqT_inr (u : Unit) : a3h_eqT σ (X (Sum.inr u)) = Polynomial.X := by
  simp [a3h_eqT, Equiv.optionEquivSumPUnit, optionEquivLeft_X_none]

theorem a3h_eqT_rename (F : MvPolynomial σ ℂ) :
    a3h_eqT σ (rename Sum.inl F) = Polynomial.C F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [a3h_eqT, optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p k hp => rw [map_mul, map_mul, hp, rename_X, a3h_eqT_inl, Polynomial.C_mul]

end coords

/-! ## The prime of a point of `X × 𝔸¹` -/

section prime

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

/-- The point of `a3m_U X.left` of a point of `X × 𝔸¹`. -/
def a3h_pt (y : (a3n_T X).left) (hy : y ∈ a3h_U X) : (a3m_U X.left).toScheme :=
  ⟨(a3h_e X).hom y, (a3h_mem_U_iff X y).1 hy⟩

/-- **The prime of a point `y` of `X × 𝔸¹`** in `ℂ[x, t]`. -/
def a3h_P (y : (a3n_T X).left) (hy : y ∈ a3h_U X) :
    Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ) :=
  (a3s_Q X (a3h_pt X y hy)).comap (a3h_eqT (Fin (a3s_N X + 1)))

instance (y : (a3n_T X).left) (hy : y ∈ a3h_U X) : (a3h_P X y hy).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsIntegral X.left] in
theorem a3h_mem_P (y : (a3n_T X).left) (hy : y ∈ a3h_U X)
    (F : MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ) :
    F ∈ a3h_P X y hy ↔ a3h_eqT _ F ∈ a3s_Q X (a3h_pt X y hy) := Iff.rfl

omit [IsIntegral X.left] in
/-- Specialization is inclusion of primes. -/
theorem a3h_P_le_iff (y y' : (a3n_T X).left) (hy : y ∈ a3h_U X) (hy' : y' ∈ a3h_U X) :
    a3h_P X y hy ≤ a3h_P X y' hy' ↔ y ⤳ y' := by
  have h1 : a3h_P X y hy ≤ a3h_P X y' hy' ↔ a3s_Q X (a3h_pt X y hy) ≤ a3s_Q X (a3h_pt X y' hy') := by
    constructor
    · intro h G hG
      obtain ⟨F, rfl⟩ := (a3h_eqT (Fin (a3s_N X + 1))).surjective G
      exact h hG
    · intro h F hF
      exact h hF
  rw [h1, a3s_Q_le_iff]
  exact Topology.IsInducing.subtypeVal.specializes_iff.symm.trans
    (a3h_e X).hom.homeomorph.isInducing.specializes_iff

omit [IsIntegral X.left] in
/-- The point of `X` below `y` has the prime `{F | F ∈ a3h_P y}`. -/
theorem a3h_fst_prime (y : (a3n_T X).left) (hy : y ∈ a3h_U X)
    (F : MvPolynomial (Fin (a3s_N X + 1)) ℂ) :
    F ∈ (a3s_CX X).prime ((a3n_q X).left y) ↔ rename Sum.inl F ∈ a3h_P X y hy := by
  rw [a3h_mem_P, a3h_eqT_rename, ← a3s_fst_prime]
  change _ ↔ F ∈ (a3s_CX X).prime (a3s_fst X ((a3h_e X).hom y))
  rw [a3h_e_fst_apply]

omit [IsIntegral X.left] in
theorem a3h_mem_Z0 (y : (a3n_T X).left) (hy : y ∈ a3h_U X) :
    a3n_h X y ∈ a3m_Z0 ↔ MvPolynomial.X (Sum.inr ()) ∈ a3h_P X y hy := by
  rw [a3h_mem_P, a3h_eqT_inr, ← a3s_mem_Z0]
  change _ ↔ a3s_snd X ((a3h_e X).hom y) ∈ a3m_Z0
  rw [a3h_e_snd_apply]

omit [IsIntegral X.left] in
theorem a3h_mem_Zinf (y : (a3n_T X).left) (hy : y ∈ a3h_U X) :
    a3n_h X y ∈ a3m_Zinf ↔ MvPolynomial.X (Sum.inr ()) - 1 ∈ a3h_P X y hy := by
  rw [a3h_mem_P, map_sub, map_one, a3h_eqT_inr, ← a3s_mem_Zinf]
  change _ ↔ a3s_snd X ((a3h_e X).hom y) ∈ a3m_Zinf
  rw [a3h_e_snd_apply]

omit [IsIntegral X.left] in
/-- Heights of points of `X × 𝔸¹` are dimensions of their cones, minus one. -/
theorem a3h_height_add_one (y : (a3n_T X).left) (hy : y ∈ a3h_U X) :
    (Order.height y : WithBot ℕ∞) + 1 =
      ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸ a3h_P X y hy) := by
  let e : (a3n_T X).left ≃o a3m_T X.left :=
    { (a3h_e X).hom.homeomorph.toEquiv with
      map_rel_iff' := fun {a b} => by
        change (a3h_e X).hom a ≤ (a3h_e X).hom b ↔ a ≤ b
        rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
        exact (a3h_e X).hom.homeomorph.isInducing.specializes_iff }
  have h1 := a3s_height_add_one_U X (a3h_pt X y hy)
  rw [← a3s_height_U X] at h1
  have h2 : Order.height ((a3m_U X.left).ι (a3h_pt X y hy)) = Order.height y :=
    Order.height_orderIso e y
  rw [h2, ← a3s_dim_Q] at h1
  rw [h1]
  refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _
    (a3h_eqT (Fin (a3s_N X + 1))).toRingEquiv ?_).symm
  rw [a3h_P]
  exact (Ideal.map_comap_of_surjective _ (a3h_eqT _).toRingEquiv.surjective _).symm

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- A prime of `ℂ[x, t]`, homogeneous in `x`, relevant and containing `I_X[t]`, is the prime of a
point of `X × 𝔸¹`. -/
theorem a3h_exists_point (P : Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ)) [P.IsPrime]
    (hhom : ((P.map (a3h_eqT (Fin (a3s_N X + 1)))).map (a3m_eq (Fin (a3s_N X + 1)))).IsHomogeneous
      (homogeneousSubmodule (Fin (a3s_N X + 1)) (Polynomial ℂ)))
    (j : Fin (a3s_N X + 1)) (hj : MvPolynomial.X (Sum.inl j) ∉ P)
    (hjX : MvPolynomial.X j ∉ a3s_IX X) (hXP : a3h_IXr (a3s_IX X) ≤ P) :
    ∃ y, ∃ hy : y ∈ a3h_U X, a3h_P X y hy = P := by
  set e := a3h_eqT (Fin (a3s_N X + 1))
  have hP : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have hcomap : (P.map e).comap e = P := Ideal.comap_map_of_bijective _ e.bijective
  obtain ⟨y, hy⟩ := a3s_exists_point_U X (P.map e) hhom j (by
      rw [← a3h_eqT_inl]
      intro h
      apply hj
      rw [← hcomap, Ideal.mem_comap]
      exact h) hjX (by
      rw [Ideal.map_le_iff_le_comap]
      intro F hF
      rw [Ideal.mem_comap, ← a3h_eqT_rename, ← Ideal.mem_comap, hcomap]
      exact hXP (Ideal.mem_map_of_mem _ hF))
  refine ⟨(a3h_e X).inv y.1, (a3h_mem_U_iff X _).2 (by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; exact y.2), ?_⟩
  have : a3h_pt X ((a3h_e X).inv y.1) ((a3h_mem_U_iff X _).2 (by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; exact y.2)) = y := by
    apply Subtype.ext
    change (a3h_e X).hom ((a3h_e X).inv y.1) = y.1
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [a3h_P, this, hy, hcomap]

end prime

/-! ## The primes of `V × ℙ¹`, `V × {0}` and `V × {1}` -/

section faces

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3h_mem_U_iff' (y : (a3n_T X).left) :
    y ∈ a3h_U X ↔ a3n_h X y ∈ Set.range (g3c_chartι 1 0) := by
  rw [a3h_mem_U_iff]
  change pullback.snd (terminal.from X.left) (terminal.from (g3c_P 1)) ((a3h_e X).hom y) ∈
    Set.range (g3c_chartι 1 0) ↔ _
  rw [a3h_e_snd_apply]

attribute [local instance] MvPolynomial.gradedAlgebra in
omit [IsProjective X.hom] in
theorem a3h_b_mem_U (v : X.left) : a3n_b X v ∈ a3h_U X := by
  rw [a3h_mem_U_iff', a3k_h_b]
  have h := a3k_generic_mem_basicOpen
  rw [← Proj.opensRange_awayι _ _ (isHomogeneous_X _ (0 : Fin 2)) zero_lt_one] at h
  exact h

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3h_σ0_mem_U (x : X.left) : a3n_σ X 0 x ∈ a3h_U X := by
  rw [a3h_mem_U_iff']
  obtain ⟨q, hq, -⟩ := a3n_h_σ0 X x
  exact ⟨q, hq⟩

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3h_σ1_mem_U (x : X.left) : a3n_σ X 1 x ∈ a3h_U X := by
  rw [a3h_mem_U_iff']
  obtain ⟨q, hq, -⟩ := a3n_h_σ1 X x
  exact ⟨q, hq⟩

/-- Primes contained in primes with the same finite dimension of the quotient are equal. -/
theorem a3h_eq_of_le_of_dim {σ' : Type} [Fintype σ'] (P Q : Ideal (MvPolynomial σ' ℂ)) [P.IsPrime]
    [Q.IsPrime] (hPQ : P ≤ Q) (m : ℕ) (hP : ringKrullDim (MvPolynomial σ' ℂ ⧸ P) = m)
    (hQ : ringKrullDim (MvPolynomial σ' ℂ ⧸ Q) = m) : P = Q := by
  by_contra hne
  have h := a3r_dim_add_one_le P Q (lt_of_le_of_ne hPQ hne)
  rw [hP, hQ] at h
  have : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (m : ℕ) := by exact_mod_cast h
  have : m + 1 ≤ m := by exact_mod_cast this
  omega

/-- Cancellation in `ℕ∞` for the dimension formula. -/
theorem a3h_enat_cancel {m n : ℕ} {c h : ℕ∞} (h1 : (m : ℕ∞) + c = n) (h2 : h + c = (n + 1 : ℕ)) :
    h = (m + 1 : ℕ) := by
  have hc : c ≠ ⊤ := fun hc => by simp [hc] at h1
  obtain ⟨c', rfl⟩ := ENat.ne_top_iff_exists.mp hc
  have hh : h ≠ ⊤ := fun hh => by
    rw [hh, top_add] at h2
    exact ENat.top_ne_coe _ h2
  obtain ⟨h', rfl⟩ := ENat.ne_top_iff_exists.mp hh
  have e1 : m + c' = n := by exact_mod_cast h1
  have e2 : h' + c' = n + 1 := by exact_mod_cast h2
  have : h' = m + 1 := by omega
  rw [this]

/-- **The prime of `V × ℙ¹`** is `P_V[t]`. -/
theorem a3h_P_b (v : X.left) :
    a3h_P X (a3n_b X v) (a3h_b_mem_U X v) = Ideal.map (rename Sum.inl) ((a3s_CX X).prime v) := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  obtain ⟨-, m, hm, -⟩ := a1d_height_eq_trdeg (X := X) v
  obtain ⟨hpr, hdim⟩ := a3h_IXr_isPrime_dim ((a3s_CX X).prime v)
  haveI := hpr
  have hb : Order.height (a3n_b X v) = (m + 1 : ℕ) := by
    have h1 := a3m_height_add_coheight X v
    rw [hm, hn] at h1
    have h2 := a3n_height_add_coheight_T X n hn (a3n_b X v)
    rw [a3k_coheight_b] at h2
    exact a3h_enat_cancel h1 h2
  symm
  refine a3h_eq_of_le_of_dim _ _ ?_ (m + 2) ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, ← a3h_fst_prime X _ (a3h_b_mem_U X v), a3n_q_b]
    exact hF
  · rw [hdim, ← a3s_height_add_one X v, hm]
    norm_cast
  · rw [← a3h_height_add_one X _ (a3h_b_mem_U X v), hb]
    norm_cast

/-- Evaluation at `t = a`, `ℂ[x, t] → ℂ[x]`. -/
def a3h_evt {σ' : Type} (a : ℂ) : MvPolynomial (σ' ⊕ Unit) ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
  aeval (Sum.elim MvPolynomial.X fun _ => MvPolynomial.C a)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3h_evt_rename {σ' : Type} (a : ℂ) (F : MvPolynomial σ' ℂ) :
    a3h_evt a (rename Sum.inl F) = F := by
  rw [a3h_evt, aeval_rename]
  simp

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- `F - F(x, a)` is a multiple of `t - a`. -/
theorem a3h_sub_evt_mem {σ' : Type} (a : ℂ) (F : MvPolynomial (σ' ⊕ Unit) ℂ) :
    F - rename Sum.inl (a3h_evt a F) ∈
      Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C a} := by
  rw [Ideal.mem_span_singleton]
  set e := a3h_eqT σ'
  have hev : ∀ G : MvPolynomial (σ' ⊕ Unit) ℂ,
      e (rename Sum.inl (a3h_evt a G)) = Polynomial.C ((e G).eval (MvPolynomial.C a)) := by
    intro G
    rw [a3h_eqT_rename]
    congr 1
    induction G using MvPolynomial.induction_on with
    | C c => simp [a3h_evt, e, a3h_eqT, optionEquivLeft_C]
    | add p q hp hq => rw [map_add, hp, hq, map_add, Polynomial.eval_add]
    | mul_X p i hp =>
      rw [map_mul, hp, map_mul, Polynomial.eval_mul]
      rcases i with k | u
      · simp [a3h_evt, e, a3h_eqT_inl]
      · simp [a3h_evt, e, a3h_eqT_inr]
  obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := MvPolynomial.C a) (p := e F)
  refine ⟨e.symm q, e.injective ?_⟩
  rw [map_mul, AlgEquiv.apply_symm_apply, map_sub, hev, map_sub, a3h_eqT_inr]
  have : e (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
    simp [e, a3h_eqT, optionEquivLeft_C]
  rw [this, hq]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- `P[t] + (t - a)` is the kernel of `ℂ[x, t] → ℂ[x]/P`, `t ↦ a`. -/
theorem a3h_ker_evt {σ' : Type} (P : Ideal (MvPolynomial σ' ℂ)) (a : ℂ) :
    RingHom.ker ((Ideal.Quotient.mk P).comp (a3h_evt a).toRingHom) =
      Ideal.map (rename Sum.inl) P ⊔
        Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C a} := by
  apply le_antisymm
  · intro F hF
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hF
    have h := a3h_sub_evt_mem a F
    have : F = (F - rename Sum.inl (a3h_evt a F)) + rename Sum.inl (a3h_evt a F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right h) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hF))
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro F hF
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
      change Ideal.Quotient.mk P (a3h_evt a (rename Sum.inl F)) = 0
      rw [a3h_evt_rename, Ideal.Quotient.eq_zero_iff_mem]
      exact hF
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change Ideal.Quotient.mk P (a3h_evt a _) = 0
      simp [a3h_evt]

/-- **The prime of `V × {a}`**, for `t = a` cutting out `σ_a(X)` at the point: `P_V[t] + (t - a)`. -/
theorem a3h_P_σ (a : ℂ) (v : X.left) (hU : a3n_σ X a v ∈ a3h_U X)
    (ha : MvPolynomial.X (Sum.inr ()) - MvPolynomial.C a ∈ a3h_P X (a3n_σ X a v) hU) :
    a3h_P X (a3n_σ X a v) hU = Ideal.map (rename Sum.inl) ((a3s_CX X).prime v) ⊔
      Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C a} := by
  obtain ⟨-, m, hm, -⟩ := a1d_height_eq_trdeg (X := X) v
  set φ := (Ideal.Quotient.mk ((a3s_CX X).prime v)).comp (a3h_evt a).toRingHom
  have hsurj : Function.Surjective φ := fun z => by
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨rename Sum.inl F, by simp [φ, a3h_evt_rename]⟩
  have hker := a3h_ker_evt ((a3s_CX X).prime v) a
  have hJ : (Ideal.map (rename Sum.inl) ((a3s_CX X).prime v) ⊔
      Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C a}).IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime φ
  have hdim : ringKrullDim (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ ⧸
      (Ideal.map (rename Sum.inl) ((a3s_CX X).prime v) ⊔
        Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C a})) = (m + 1 : ℕ) := by
    rw [← hker, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj),
      ← a3s_height_add_one X v, hm]
    norm_cast
  symm
  refine a3h_eq_of_le_of_dim _ _ (sup_le ?_ ?_) (m + 1) hdim ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, ← a3h_fst_prime X _ hU, a3n_q_σ_apply]
    exact hF
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ha
  · rw [← a3h_height_add_one X _ hU, a3n_height_σ, hm]
    norm_cast

theorem a3h_P_σ0 (v : X.left) :
    a3h_P X (a3n_σ X 0 v) (a3h_σ0_mem_U X v) = Ideal.map (rename Sum.inl) ((a3s_CX X).prime v) ⊔
      Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C 0} :=
  a3h_P_σ X 0 v _ (by
    rw [map_zero, sub_zero, ← a3h_mem_Z0]
    exact a3n_h_σ0 X v)

theorem a3h_P_σ1 (v : X.left) :
    a3h_P X (a3n_σ X 1 v) (a3h_σ1_mem_U X v) = Ideal.map (rename Sum.inl) ((a3s_CX X).prime v) ⊔
      Ideal.span {MvPolynomial.X (Sum.inr ()) - MvPolynomial.C 1} :=
  a3h_P_σ X 1 v _ (by
    rw [map_one, ← a3h_mem_Zinf]
    exact a3n_h_σ1 X v)

end faces

/-! ## Homogeneity in `x` and the components of intersections -/

section comps

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Minimal primes are carried by ring isomorphisms. -/
theorem a3h_map_minimalPrimes {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {J 𝔶 : Ideal R} (h𝔶 : 𝔶 ∈ J.minimalPrimes) : 𝔶.map e ∈ (J.map e).minimalPrimes := by
  have h𝔶p := h𝔶.1.1
  refine ⟨⟨Ideal.map_isPrime_of_equiv e, Ideal.map_mono h𝔶.1.2⟩, fun q ⟨hq, hJq⟩ hq𝔶 => ?_⟩
  have hq' : q.comap e ∈ {p | p.IsPrime ∧ J ≤ p} :=
    ⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.1 hJq⟩
  have hle : q.comap e ≤ 𝔶 := by
    have := Ideal.comap_mono (f := e) hq𝔶
    rwa [Ideal.comap_map_of_bijective _ e.bijective] at this
  have h := h𝔶.2 hq' hle
  have := Ideal.map_mono (f := e) h
  rwa [Ideal.map_comap_of_surjective _ e.surjective] at this

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- An ideal of `ℂ[x, t]` homogeneous in `x`. -/
def a3h_XHom (I : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)) : Prop :=
  ((I.map (a3h_eqT σ)).map (a3m_eq σ)).IsHomogeneous (homogeneousSubmodule σ (Polynomial ℂ))

theorem a3h_XHom_sup {I J : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)} (hI : a3h_XHom I)
    (hJ : a3h_XHom J) : a3h_XHom (I ⊔ J) := by
  unfold a3h_XHom at *
  rw [Ideal.map_sup, Ideal.map_sup]
  exact hI.sup hJ

theorem a3h_XHom_minimal {J 𝔶 : Ideal (MvPolynomial (σ ⊕ Unit) ℂ)} (hJ : a3h_XHom J)
    (h𝔶 : 𝔶 ∈ J.minimalPrimes) : a3h_XHom 𝔶 :=
  a3m_isHomogeneous_of_mem_minimalPrimes hJ
    (a3h_map_minimalPrimes (a3m_eq σ).toRingEquiv
      (a3h_map_minimalPrimes (a3h_eqT σ).toRingEquiv h𝔶))

end comps

section compsX

attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

omit [IsIntegral X.left] in
theorem a3h_XHom_P (y : (a3n_T X).left) (hy : y ∈ a3h_U X) : a3h_XHom (a3h_P X y hy) := by
  unfold a3h_XHom
  rw [a3h_P, a3s_Q, Ideal.map_comap_of_surjective _ (a3h_eqT _).surjective,
    Ideal.map_comap_of_surjective _ (a3m_eq _).surjective]
  exact (a3s_LC X).isHomogeneous_prime _

omit [IsIntegral X.left] in
/-- Points of `X × 𝔸¹` with the same prime are equal. -/
theorem a3h_P_injective (y y' : (a3n_T X).left) (hy : y ∈ a3h_U X) (hy' : y' ∈ a3h_U X)
    (h : a3h_P X y hy = a3h_P X y' hy') : y = y' :=
  (((a3h_P_le_iff X y y' hy hy').1 h.le).antisymm ((a3h_P_le_iff X y' y hy' hy).1 h.ge)).eq

/-- **A relevant minimal prime over `P_y + P_w` is the prime of a component** of
`closure {y} ∩ closure {w}` over `𝔸¹`. -/
theorem a3h_comp_of_minimal (y w : (a3n_T X).left) (hy : y ∈ a3h_U X) (hw : w ∈ a3h_U X)
    (𝔶 : Ideal (MvPolynomial (Fin (a3s_N X + 1) ⊕ Unit) ℂ))
    (h𝔶 : 𝔶 ∈ (a3h_P X y hy ⊔ a3h_P X w hw).minimalPrimes)
    (hrel : ∃ j, MvPolynomial.X (Sum.inl j) ∉ 𝔶) :
    ∃ z, ∃ hz : z ∈ a3h_U X, z ∈ a3y_comps y w ∧ a3h_P X z hz = 𝔶 := by
  have h𝔶p : 𝔶.IsPrime := h𝔶.1.1
  have hhom : a3h_XHom 𝔶 :=
    a3h_XHom_minimal (a3h_XHom_sup (a3h_XHom_P X y hy) (a3h_XHom_P X w hw)) h𝔶
  have hIX : a3h_IXr (a3s_IX X) ≤ 𝔶 := by
    refine le_trans ?_ (le_sup_left.trans h𝔶.1.2)
    rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, ← a3h_fst_prime X y hy]
    exact a3s_IX_le X _ hF
  obtain ⟨j, hj⟩ := hrel
  have hjX : MvPolynomial.X j ∉ a3s_IX X := fun h =>
    hj (hIX (by rw [← rename_X]; exact Ideal.mem_map_of_mem _ h))
  obtain ⟨z, hz, hzP⟩ := a3h_exists_point X 𝔶 (by
    exact hhom) j hj hjX hIX
  have hyz : y ⤳ z := (a3h_P_le_iff X y z hy hz).1 (hzP ▸ le_sup_left.trans h𝔶.1.2)
  have hwz : w ⤳ z := (a3h_P_le_iff X w z hw hz).1 (hzP ▸ le_sup_right.trans h𝔶.1.2)
  refine ⟨z, hz, ?_, hzP⟩
  obtain ⟨z₀, hz₀, hcomp⟩ := a3s_component_of_maximal y w z hyz hwz (fun z' hyz' hwz' hz'z => by
    have hz' : z' ∈ a3h_U X := hz'z.mem_open (a3h_U X).isOpen hz
    have hle : a3h_P X z' hz' ≤ 𝔶 := hzP ▸ (a3h_P_le_iff X z' z hz' hz).2 hz'z
    have hge : a3h_P X y hy ⊔ a3h_P X w hw ≤ a3h_P X z' hz' :=
      sup_le ((a3h_P_le_iff X y z' hy hz').2 hyz') ((a3h_P_le_iff X w z' hw hz').2 hwz')
    have heq := le_antisymm (h𝔶.2 ⟨inferInstance, hge⟩ hle) hle
    exact a3h_P_injective X z' z hz' hz (heq.symm.trans hzP.symm))
  exact ⟨z₀, hcomp, hz₀⟩

end compsX

end HodgeLean.Adapters
