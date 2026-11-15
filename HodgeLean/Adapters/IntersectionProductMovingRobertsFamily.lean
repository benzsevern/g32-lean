import HodgeLean.Adapters.IntersectionProductMovingRobertsExcess

/-! # Roberts' moving family

`a3s_movingFamily_of_rank` builds `a3m_MovingFamily` for a subvariety `Z = closure {u}` of
positive codimension of an integral projective `X ⊂ ℙᴺ` whose affine cone has differentials of
rank at most `dim X + 1` at its relevant points: from the cone `C = C_L(Z)` and the general
translate `M⁻¹ C` of `a3r_exists_cone_translate`, the family `t ↦ h_t⁻¹(C)`, `h_t = (1 - t) + t M`,
met with `X × ℙ¹` has a component through `Z × {0}` (`a3m_family_components`) dominating `ℙ¹`; its
points over `t = 0` lie in `C ∩ X` and those over `t = 1` in `M⁻¹(C) ∩ X`.

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970* (1972), 89–96;
Fulton, *Intersection Theory*, second edition, §1.6 and Example 11.4.1.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations TensorProduct

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

section Helpers

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem a3s_eq_map_algebraMap (f : Polynomial ℂ) :
    a3m_eq σ (f.map (algebraMap ℂ (MvPolynomial σ ℂ))) = MvPolynomial.C f := by
  have : ((a3m_eq σ).toRingHom.comp (Polynomial.mapRingHom (algebraMap ℂ (MvPolynomial σ ℂ)))) =
      (MvPolynomial.C : Polynomial ℂ →+* MvPolynomial σ (Polynomial ℂ)) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
      change a3m_eq σ (Polynomial.C (MvPolynomial.C c)) = _
      rw [a3m_eq_C, MvPolynomial.map_C]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      exact a3m_eq_X σ
  exact congrArg (fun φ : Polynomial ℂ →+* MvPolynomial σ (Polynomial ℂ) => φ f) this

omit [Fintype σ] [DecidableEq σ] in
theorem a3s_dim_zeroFibre (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime] :
    ringKrullDim (Polynomial (MvPolynomial σ ℂ) ⧸ a3m_zeroFibre P) =
      ringKrullDim (MvPolynomial σ ℂ ⧸ P) := by
  refine ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective ?_)
  intro z
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨Polynomial.C F, by simp⟩

theorem a3s_zeroFibre_isHomogeneous (P : Ideal (MvPolynomial σ ℂ))
    (hP : P.IsHomogeneous (homogeneousSubmodule σ ℂ)) :
    ((a3m_zeroFibre P).map (a3m_eq σ)).IsHomogeneous (homogeneousSubmodule σ (Polynomial ℂ)) := by
  refine a3m_isHomogeneous_of_scale _ fun c _ G hG => ?_
  obtain ⟨H, hH, rfl⟩ := (Ideal.mem_map_of_equiv (a3m_eq σ) G).1 hG
  rw [← a3m_eq_scale]
  refine Ideal.mem_map_of_mem _ ?_
  rw [a3m_mem_zeroFibre] at hH ⊢
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
  exact a3m_scale_mem_of_isHomogeneous hP c hH

/-- `F(h_t x) ≡ F (mod t)`. -/
theorem a3s_subst_mod_X (M : Matrix σ σ ℂ) (F : MvPolynomial σ ℂ)
    (Qp : Ideal (Polynomial (MvPolynomial σ ℂ))) (hX : Polynomial.X ∈ Qp)
    (hF : a3m_subst M F ∈ Qp) : Polynomial.C F ∈ Qp := by
  obtain ⟨g, hg⟩ := Polynomial.X_dvd_sub_C (p := a3m_subst M F)
  rw [Polynomial.coeff_zero_eq_eval_zero, a3m_eval_zero_subst] at hg
  have : Polynomial.C F = a3m_subst M F - Polynomial.X * g := by rw [← hg]; ring
  rw [this]
  exact sub_mem hF (Qp.mul_mem_right _ hX)

/-- `F(h_t x) ≡ F(M x) (mod t - 1)`. -/
theorem a3s_subst_mod_X_sub_one (M : Matrix σ σ ℂ) (F : MvPolynomial σ ℂ)
    (Qp : Ideal (Polynomial (MvPolynomial σ ℂ))) (hX : Polynomial.X - 1 ∈ Qp)
    (hF : a3m_subst M F ∈ Qp) : Polynomial.C (a3r_lin M F) ∈ Qp := by
  obtain ⟨g, hg⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := a3m_subst M F) (a := 1)
  rw [a3m_eval_one_subst, map_one] at hg
  have : Polynomial.C (a3r_lin M F) = a3m_subst M F - (Polynomial.X - 1) * g := by
    rw [← hg, show a3r_lin M F = a3m_substM M F from rfl]; ring
  rw [this]
  exact sub_mem hF (Qp.mul_mem_right _ hX)

theorem a3s_height_eq {α : Type} [Preorder α] (y : α) (m : ℕ)
    (h : (Order.height y : WithBot ℕ∞) + 1 = (m + 1 : ℕ)) : Order.height y = m := by
  generalize Order.height y = x at h
  induction x using ENat.recTopCoe with
  | top =>
    exfalso
    have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast h
    rw [top_add] at h'
    exact ENat.top_ne_natCast _ (WithBot.coe_injective h')
  | coe x =>
    have : x + 1 = m + 1 := by exact_mod_cast h
    rw [show x = m by omega]

end Helpers

section Family

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

omit [IsIntegral X.left] [IsProjective X.hom] in
theorem a3s_mem_U_of_Z0 (r : (a3s_T X).left) (h : a3s_snd X r ∈ a3m_Z0) : r ∈ a3m_U X.left := by
  obtain ⟨q, hq, -⟩ := h
  exact ⟨q, hq⟩

omit [IsIntegral X.left] [IsProjective X.hom] in
theorem a3s_mem_U_of_Zinf (r : (a3s_T X).left) (h : a3s_snd X r ∈ a3m_Zinf) : r ∈ a3m_U X.left := by
  obtain ⟨q, hq, -⟩ := h
  exact ⟨q, hq⟩

/-- Roberts' moving family, from the rank condition on the differentials of the affine cone over
`X` (which holds when `X` is smooth): `T = X × ℙ¹`, the member `closure {y₀}` is the component
through `Z × {0}` of the family `t ↦ h_t⁻¹(C)` of translates of the cone `C = C_L(Z)`, met with
`X × ℙ¹`; its fibre over `t = 0` lies in `C ∩ X`, whose components other than `Z` have smaller
excess, and its fibre over `t = 1` lies in `M⁻¹(C) ∩ X`, which meets `Z` and every `W` properly.
Source: J. Roberts, *Chow's moving lemma* (1972), Main Lemma and §2; Fulton, *Intersection
Theory*, second edition, §1.6 and Example 11.4.1. -/
theorem a3s_movingFamily_of_rank (n : ℕ) (hn : Order.height (genericPoint X.left) = n)
    (hsm : ∀ (𝔶 : Ideal (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X)) [𝔶.IsPrime],
      (∃ j, Ideal.Quotient.mk (a3s_IX X) (MvPolynomial.X j) ∉ 𝔶) →
      Module.finrank 𝔶.ResidueField
        (𝔶.ResidueField ⊗[MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X]
          Ω[MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X⁄ℂ]) ≤ n + 1)
    (S : Set X.left) (hS : S.Finite) (p k d : ℕ) (hp : 0 < p) (u : X.left)
    (hu : Order.coheight u = p) (hd : Order.height u = d)
    (he : a3m_ExcessLE X.left S u (k + 1)) :
    Nonempty (a3m_MovingFamily X S p k d u) := by
  classical
  set N := a3s_N X
  set CX := a3s_CX X
  set IX := a3s_IX X
  -- dimensions
  obtain ⟨mu, cu, hmu, hcu, hsumu, hdu⟩ := a3s_nums X n hn u
  have hmu' : mu = d := by rw [hd] at hmu; exact_mod_cast hmu.symm
  have hcu' : cu = p := by rw [hu] at hcu; exact_mod_cast hcu.symm
  obtain ⟨mη, -, hmη, -, -, hdη⟩ := a3s_nums X n hn (genericPoint X.left)
  have hmη' : mη = n := by rw [hn] at hmη; exact_mod_cast hmη.symm
  have hdimX : ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IX) = (n + 1 : ℕ) := by
    change ringKrullDim (_ ⧸ CX.prime (genericPoint X.left)) = _
    rw [hdη, hmη']
  set PZ := CX.prime u
  have hdimZ : ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ PZ) = (d + 1 : ℕ) := by
    rw [hdu, hmu']
  have hdn : d < n := by omega
  set SW := hS.toFinset.image CX.prime
  have hSW : ∀ W ∈ SW, W.IsPrime := by
    intro W hW
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hW
    infer_instance
  have hexc : ∀ W ∈ SW, ∀ 𝔶 ∈ (PZ ⊔ W).minimalPrimes, (∃ j, MvPolynomial.X j ∉ 𝔶) →
      ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ 𝔶) +
          ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IX) ≤
        ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ PZ) +
          ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ W) + (k + 1 : ℕ) := by
    intro W hW 𝔶 h𝔶 hrel
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hW
    exact a3s_dim_of_excessLE X S u (k + 1) he v (hS.mem_toFinset.1 hv) 𝔶 h𝔶 hrel
  obtain ⟨IC, M, hICp, hIChom, hICZ, hC, hfib, hres, htr⟩ :=
    a3r_exists_cone_translate IX PZ (CX.isHomogeneous_prime u) (a3s_IX_isHomogeneous X)
      (a3s_IX_le X u) hdimX d hdimZ SW hSW k hexc hsm
  -- the component of the family through `Z × {0}`
  have hle0 : a3m_famInter IX IC M ≤ a3m_zeroFibre PZ :=
    a3m_famInter_le_zeroFibre IX IC M PZ (sup_le (a3s_IX_le X u) hICZ)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle0
  have hQp : Q.IsPrime := hQ.1.1
  obtain ⟨hdimQ, -, hdomQ⟩ :=
    a3m_family_components IX IC M n d hdimX hC.le hfib PZ Q hQ hQP
  obtain ⟨j, hj⟩ := a3s_relevant X u
  have hjX : MvPolynomial.X j ∉ IX := fun h => hj (a3s_IX_le X u h)
  have hj0 : Polynomial.C (MvPolynomial.X j) ∉ a3m_zeroFibre PZ := by
    rw [a3m_mem_zeroFibre, Polynomial.eval_C]; exact hj
  have hjQ : Polynomial.C (MvPolynomial.X j) ∉ Q := fun h => hj0 (hQP h)
  have hXQ : Ideal.map Polynomial.C IX ≤ Q := le_sup_left.trans hQ.1.2
  have hhomQ : (Q.map (a3m_eq (Fin (N + 1)))).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) (Polynomial ℂ)) :=
    a3m_isHomogeneous_of_mem_minimalPrimes
      (a3m_famInter_isHomogeneous IX IC (a3s_IX_isHomogeneous X) hIChom M)
      (a3m_map_mem_minimalPrimes (a3m_eq (Fin (N + 1))).toRingEquiv hQ)
  obtain ⟨y₀, hy₀⟩ := a3s_exists_point_U X Q hhomQ j hjQ hjX hXQ
  have hX0 : Ideal.map Polynomial.C IX ≤ a3m_zeroFibre PZ := by
    refine Ideal.map_le_iff_le_comap.2 fun F hF => ?_
    rw [Ideal.mem_comap, a3m_mem_zeroFibre, Polynomial.eval_C]
    exact a3s_IX_le X u hF
  obtain ⟨r₀, hr₀⟩ := a3s_exists_point_U X (a3m_zeroFibre PZ)
    (a3s_zeroFibre_isHomogeneous PZ (CX.isHomogeneous_prime u)) j hj0 hjX hX0
  set yT := (a3m_U X.left).ι y₀
  set rT := (a3m_U X.left).ι r₀
  have hemb := (a3m_U X.left).ι.isOpenEmbedding
  have hyr : y₀ ⤳ r₀ := (a3s_Q_le_iff X y₀ r₀).1 (by rw [hy₀, hr₀]; exact hQP)
  -- heights
  have hy₀h : Order.height yT = (d + 1 : ℕ) := by
    rw [a3s_height_U]
    refine a3s_height_eq y₀ (d + 1) ?_
    rw [a3s_height_add_one_U, ← a3s_dim_Q, hy₀, hdimQ]
  have hr₀h : Order.height rT = d := by
    rw [a3s_height_U]
    refine a3s_height_eq r₀ d ?_
    rw [a3s_height_add_one_U, ← a3s_dim_Q, hr₀, a3s_dim_zeroFibre, hdimZ]
  -- the dimension of the cone
  have hC' : (((n : ℕ) : ℕ∞) : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ IC) =
      ((d + Fintype.card (Fin (N + 1)) : ℕ) : WithBot ℕ∞) := by
    rw [hC, add_comm]; rfl
  obtain ⟨a, b, ha, hb, hab⟩ := a3m_withBot_add_eq_nat hC'
  have ha' : a = n := by exact_mod_cast ha.symm
  -- points over the special fibres
  have hover : ∀ r : (a3s_T X).left, yT ⤳ r →
      (a3s_snd X r ∈ a3m_Z0 ∨ a3s_snd X r ∈ a3m_Zinf) →
      ∃ r' : (a3m_U X.left).toScheme, (a3m_U X.left).ι r' = r ∧ Q ≤ a3s_Q X r' := by
    intro r hr hZ
    have hrU : r ∈ a3m_U X.left := hZ.elim (a3s_mem_U_of_Z0 X r) (a3s_mem_U_of_Zinf X r)
    refine ⟨⟨r, hrU⟩, Scheme.Opens.ι_apply _ _, ?_⟩
    rw [← hy₀]
    refine (a3s_Q_le_iff X y₀ ⟨r, hrU⟩).2 (hemb.isInducing.specializes_iff.1 ?_)
    rw [Scheme.Opens.ι_apply]
    exact hr
  have hsubst : ∀ r' : (a3m_U X.left).toScheme, Q ≤ a3s_Q X r' → ∀ F ∈ IC,
      a3m_subst M F ∈ a3s_Q X r' := fun r' hQr F hF =>
    hQr (hQ.1.2 (Ideal.mem_sup_right (a3m_subst_mem_famIdeal IC M hF)))
  refine ⟨{
    T := a3s_T X
    q := a3s_q X
    L := a3m_P1curve
    h₀ := a3s_snd X
    Y := ({yT} : Finset (a3s_T X).left)
    dom := ?_
    dim := ?_
    start := ?_
    avoid := ?_
    good := ?_ }⟩
  · intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    change a3s_snd X ((a3m_U X.left).ι y₀) = genericPoint (g3c_P 1)
    rw [a3m_genericPoint_P1]
    refine a3m_line_snd_bot (a3s_CX X) (a3s_hov X) y₀ fun f hf hfQ => hdomQ f hf ?_
    rw [← hy₀, a3s_Q, Ideal.mem_comap, a3s_eq_map_algebraMap]
    exact hfQ
  · intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact hy₀h
  · refine ⟨yT, Finset.mem_singleton_self _, rT, hyr.map (a3m_U X.left).ι.continuous, hr₀h, ?_, ?_⟩
    · change a3s_snd X ((a3m_U X.left).ι r₀) ∈ a3m_Z0
      rw [a3s_mem_Z0, hr₀, a3m_mem_zeroFibre, Polynomial.eval_X]
      exact zero_mem _
    · change a3s_fst X rT = u
      apply CX.prime_injective
      ext F
      rw [a3s_fst_prime, hr₀, a3m_mem_zeroFibre, Polynomial.eval_C]
  · intro y hy r hr hinf hqr
    rw [Finset.mem_singleton] at hy
    subst hy
    obtain ⟨r', rfl, hQr⟩ := hover r hr (Or.inr hinf)
    have hinf : a3s_snd X ((a3m_U X.left).ι r') ∈ a3m_Zinf := hinf
    rw [a3s_mem_Zinf] at hinf
    have hlin : ∀ F ∈ IC, a3r_lin M F ∈ PZ := by
      intro F hF
      have h1 := (a3s_fst_prime X r' _).2
        (a3s_subst_mod_X_sub_one M F (a3s_Q X r') hinf (hsubst r' hQr F hF))
      change a3s_fst X _ = u at hqr
      rwa [hqr] at h1
    have hb' := htr PZ (Finset.mem_insert_self _ _) PZ inferInstance le_rfl hlin ⟨j, hj⟩
    rw [hdimZ, hb] at hb'
    have : d + 1 + (N + 1) ≤ b + (d + 1) := by
      simp only [Fintype.card_fin] at hb'
      exact_mod_cast hb'
    simp only [Fintype.card_fin] at hab
    omega
  · intro y hy r hr hZ hdq hne
    rw [Finset.mem_singleton] at hy
    subst hy
    obtain ⟨r', rfl, hQr⟩ := hover r hr hZ
    set x := a3s_fst X ((a3m_U X.left).ι r')
    change Order.height x = d at hdq
    change x ≠ u at hne
    change a3m_ExcessLE X.left S x k ∧ Order.coheight x = p
    obtain ⟨mx, cx, hmx, hcx, hsumx, hdx⟩ := a3s_nums X n hn x
    have hmx' : mx = d := by rw [hdq] at hmx; exact_mod_cast hmx.symm
    have hdimx : ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ CX.prime x) = (d + 1 : ℕ) := by
      rw [hdx, hmx']
    refine ⟨?_, by rw [hcx]; exact_mod_cast (show cx = p by omega)⟩
    have hXx : IX ≤ CX.prime x := a3s_IX_le X x
    have hnePZ : CX.prime x ≠ PZ := fun h => hne (CX.prime_injective h)
    have hvSW : ∀ v ∈ S, CX.prime v ∈ SW := fun v hv =>
      Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hv)
    rcases hZ with hZ0 | hZinf
    · have hZ0 : a3s_snd X ((a3m_U X.left).ι r') ∈ a3m_Z0 := hZ0
      rw [a3s_mem_Z0] at hZ0
      have hICx : IC ≤ CX.prime x := fun F hF =>
        (a3s_fst_prime X r' F).2 (a3s_subst_mod_X M F _ hZ0 (hsubst r' hQr F hF))
      refine a3s_excessLE_of_dim X S x k fun v hv Y hY hle hrel => ?_
      exact hres (CX.prime x) inferInstance (sup_le hXx hICx) hdimx hnePZ (CX.prime v)
        (hvSW v hv) Y hY hle hrel
    · have hZinf : a3s_snd X ((a3m_U X.left).ι r') ∈ a3m_Zinf := hZinf
      rw [a3s_mem_Zinf] at hZinf
      have hlin : ∀ F ∈ IC, a3r_lin M F ∈ CX.prime x := fun F hF =>
        (a3s_fst_prime X r' _).2 (a3s_subst_mod_X_sub_one M F _ hZinf (hsubst r' hQr F hF))
      refine a3s_excessLE_of_dim X S x k fun v hv Y hY hle hrel => ?_
      have hb' := htr (CX.prime v) (Finset.mem_insert_of_mem (hvSW v hv)) Y hY
        (le_sup_right.trans hle) (fun F hF => (le_sup_left.trans hle) (hlin F hF)) hrel
      obtain ⟨mv, cv, -, -, -, hdv⟩ := a3s_nums X n hn v
      rw [hb, hdv] at hb'
      rw [hdimX, hdimx, hdv]
      simp only [Fintype.card_fin] at hb' hab
      refine a3r_withBot_le_of_add_le_add N ?_
      calc ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ Y) + ((n + 1 : ℕ) : WithBot ℕ∞) + (N : ℕ)
          = ringKrullDim (MvPolynomial (Fin (N + 1)) ℂ ⧸ Y) + ((N + 1 : ℕ) : WithBot ℕ∞) +
              (n : ℕ) := by push_cast; abel
        _ ≤ ((b : ℕ) : WithBot ℕ∞) + ((mv + 1 : ℕ) : WithBot ℕ∞) + (n : ℕ) := by gcongr
        _ = ((b + (mv + 1) + n : ℕ) : WithBot ℕ∞) := by push_cast; rfl
        _ ≤ ((d + 1 + (mv + 1) + k + N : ℕ) : WithBot ℕ∞) := by
            exact_mod_cast (show b + (mv + 1) + n ≤ d + 1 + (mv + 1) + k + N by omega)
        _ = _ := by push_cast; rfl

end Family

end HodgeLean.Adapters
