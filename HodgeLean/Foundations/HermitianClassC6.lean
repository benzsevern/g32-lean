import HodgeLean.Foundations.HermitianClassC5

noncomputable section
namespace HodgeLean.Foundations.HermitianClass

/-- A normalized orthogonal pair splits off two Hermitian lines and leaves a regular complement.
Source: Scharlau, *Quadratic and Hermitian Forms*, Chapter 7, §1. -/
theorem hermClass_pair_decomposition (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (a b : W) (haa : h a a = 1) (hbb : h b b = -1) (hab : h a b = 0) :
    ∃ V₁ : Submodule (QuadraticAlgebra ℚ (-3) 0) W,
      ∃ V₂ : Submodule (QuadraticAlgebra ℚ (-3) 0) V₁,
      ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0 × V₂),
        ((h.domRestrict₁₂ V₁ V₁).domRestrict₁₂ V₂ V₂).Nondegenerate ∧
          e a = (1, 0, 0) ∧ e b = (0, 1, 0) ∧
          ∀ x y, h x y = star (e x).1 * (e y).1 -
            star (e x).2.1 * (e y).2.1 + h (e x).2.2 (e y).2.2 := by
  let K := QuadraticAlgebra ℚ (-3) 0
  have haa0 : h a a ≠ 0 := by rw [haa]; norm_num
  obtain ⟨V₁, e₁, hn₁, hea, he₁⟩ := hermClass_line_decomposition W h hh hn a haa0
  have heb₁ : (e₁ b).1 = 0 := by
    have := he₁ a b
    rw [hea, hab, haa] at this
    simpa using this.symm
  let b₁ : V₁ := (e₁ b).2
  let h₁ := h.domRestrict₁₂ V₁ V₁
  have hh₁ : h₁.IsSymm := hh.domRestrict V₁
  have hb₁ : h₁ b₁ b₁ = -1 := by
    have := he₁ b b
    rw [hbb, heb₁] at this
    change h (e₁ b).2 (e₁ b).2 = -1
    simpa [b₁] using this.symm
  have hb₁0 : h₁ b₁ b₁ ≠ 0 := by rw [hb₁]; norm_num
  obtain ⟨V, e₂, hnV, heb₂, he₂⟩ :=
    hermClass_line_decomposition V₁ h₁ hh₁ hn₁ b₁ hb₁0
  let ep := LinearEquiv.prodCongr (LinearEquiv.refl K K) e₂
  let e := e₁.trans ep
  refine ⟨V₁, V, e, hnV, ?_, ?_, fun x y ↦ ?_⟩
  · change ep (e₁ a) = (1, 0, 0)
    rw [hea]
    simp [ep]
    rfl
  · change ep (e₁ b) = (0, 1, 0)
    rw [show e₁ b = (0, b₁) by exact Prod.ext heb₁ rfl]
    simp [ep, heb₂]
  · rw [he₁ x y]
    have hrest := he₂ (e₁ x).2 (e₁ y).2
    change h (e₁ x).2 (e₁ y).2 = _ at hrest
    rw [hrest, haa, hb₁]
    change _ = star (ep (e₁ x)).1 * (ep (e₁ y)).1 -
      star (ep (e₁ x)).2.1 * (ep (e₁ y)).2.1 +
        h (ep (e₁ x)).2.2 (ep (e₁ y)).2.2
    simp [ep, h₁]
    change _ + (-_ + h _ _) = _ - _ + h _ _
    abel

#print axioms hermClass_pair_decomposition

/-- A form-preserving linear equivalence preserves Hermitian inertia.
Source: Sylvester's law of inertia. -/
theorem hermSignature_eq_of_equiv (W W' : Type*) [AddCommGroup W] [AddCommGroup W']
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W']
    [Module ℚ W] [Module ℚ W']
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W']
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (h' : W' →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W' →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0] W')
    (he : ∀ x y, h' (e x) (e y) = h x y) :
    HermitianForm.hermSignature h = HermitianForm.hermSignature h' := by
  let q := (HermitianForm.hermQuadForm h).baseChange ℝ
  let q' := (HermitianForm.hermQuadForm h').baseChange ℝ
  let er := (e.restrictScalars ℚ).baseChange ℚ ℝ _ _
  have heq : QuadraticMap.Equivalent q q' := by
    refine ⟨{ toLinearEquiv := er, map_app' := fun z ↦ ?_ }⟩
    have hforms : q'.comp er.toLinearMap = q := by
      apply baseChange_ext
      intro x
      simp [q, q', er, HermitianForm.hermQuadForm_apply, he]
    exact DFunLike.congr_fun hforms z
  simp only [HermitianForm.hermSignature, Prod.mk.injEq]
  exact ⟨congrArg (fun n ↦ n / 2) heq.sigPos_eq,
    congrArg (fun n ↦ n / 2) heq.sigNeg_eq⟩

#print axioms hermSignature_eq_of_equiv

set_option maxHeartbeats 400000 in
/-- A form-preserving linear equivalence preserves the Hermitian determinant class.
Source: change of basis for Hermitian Gram determinants. -/
theorem detClass_eq_of_equiv (W W' : Type*) [AddCommGroup W] [AddCommGroup W']
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W']
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W']
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (h' : W' →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W' →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (hh : h.IsSymm) (hn : h.Nondegenerate) (hh' : h'.IsSymm) (hn' : h'.Nondegenerate)
    (e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0] W')
    (he : ∀ x y, h' (e x) (e y) = h x y) :
    HermitianForm.detClass h hh hn = HermitianForm.detClass h' hh' hn' := by
  let b := Module.finBasis (QuadraticAlgebra ℚ (-3) 0) W
  let b' := b.map e
  have hmat : LinearMap.toMatrix₂ b' b' h' = LinearMap.toMatrix₂ b b h := by
    apply Matrix.ext
    intro i j
    simp [b', LinearMap.toMatrix₂_apply, he]
  have hgram : HermitianForm.gramDetℚ h b = HermitianForm.gramDetℚ h' b' := by
    apply (algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0)).injective
    rw [HermitianForm.algebraMap_gramDetℚ hh b, HermitianForm.algebraMap_gramDetℚ hh' b']
    simp only [HermitianForm.gramDet, hmat]
  rw [HermitianForm.detClass_eq hh hn b, HermitianForm.detClass_eq hh' hn' b']
  apply congrArg (fun u : ℚˣ ↦
    (u : ℚˣ ⧸ HermitianForm.normSubgroup (QuadraticAlgebra ℚ (-3) 0)))
  apply Units.ext
  exact hgram

#print axioms detClass_eq_of_equiv

private theorem ncard_sum_pred {A B : Type*} [Fintype A] [Fintype B]
    (p : A → Prop) (q : B → Prop) [DecidablePred p] [DecidablePred q] :
    {z : A ⊕ B | Sum.elim p q z}.ncard =
      {a : A | p a}.ncard + {b : B | q b}.ncard := by
  let es : {z : A ⊕ B // Sum.elim p q z} ≃
      ({a : A // p a} ⊕ {b : B // q b}) :=
    { toFun := fun z ↦ match z.1, z.2 with
        | Sum.inl a, ha => Sum.inl ⟨a, ha⟩
        | Sum.inr b, hb => Sum.inr ⟨b, hb⟩
      invFun := fun z ↦ match z with
        | Sum.inl a => ⟨Sum.inl a.1, a.2⟩
        | Sum.inr b => ⟨Sum.inr b.1, b.2⟩
      left_inv := by rintro ⟨a | b, h⟩ <;> rfl
      right_inv := by rintro (a | b) <;> rfl }
  simp_rw [← _root_.Nat.card_coe_set_eq]
  exact (Nat.card_congr es).trans Nat.card_sum

/-- Splitting a normalized positive and negative line removes one from each inertia index.
Source: Sylvester's law of inertia. -/
theorem hermSignature_pair_coordinates (W V : Type*) [AddCommGroup W] [AddCommGroup V]
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    [Module (QuadraticAlgebra ℚ (-3) 0) V]
    [Module ℚ W] [Module ℚ V]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) V]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) V]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (hV : V →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] V →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (hhV : hV.IsSymm) (hnV : hV.Nondegenerate)
    (e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
      (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0 × V))
    (he : ∀ x y, h x y = star (e x).1 * (e y).1 -
      star (e x).2.1 * (e y).2.1 + hV (e x).2.2 (e y).2.2) :
    HermitianForm.hermSignature h =
      ((HermitianForm.hermSignature hV).1 + 1,
        (HermitianForm.hermSignature hV).2 + 1) := by
  let K := QuadraticAlgebra ℚ (-3) 0
  obtain ⟨d, hd, eV, heV⟩ := hermClass_diagonalize V hV hhV hnV
  let D : Fin 2 ⊕ Fin (Module.finrank K V) → ℚ :=
    Sum.elim ![1, -1] d
  let ep₁ := (LinearEquiv.refl K K).prodCongr ((LinearEquiv.refl K K).prodCongr eV)
  let ep₂ := (LinearEquiv.prodAssoc K K K
    (Fin (Module.finrank K V) → K)).symm
  let ep₃ := (LinearEquiv.finTwoArrow K K).symm.prodCongr
    (LinearEquiv.refl K (Fin (Module.finrank K V) → K))
  let ep₄ := (LinearEquiv.sumArrowLequivProdArrow (Fin 2)
    (Fin (Module.finrank K V)) K K).symm
  let E := e.trans (ep₁.trans (ep₂.trans (ep₃.trans ep₄)))
  have hE : ∀ x y, HermitianForm.diagForm D (E x) (E y) = h x y := by
    intro x y
    rw [he x y]
    have hEx : E x = ep₄ ((LinearEquiv.finTwoArrow K K).symm
        ((e x).1, (e x).2.1), eV (e x).2.2) := rfl
    have hEy : E y = ep₄ ((LinearEquiv.finTwoArrow K K).symm
        ((e y).1, (e y).2.1), eV (e y).2.2) := rfl
    rw [hEx, hEy, HermitianForm.diagForm_apply, Fintype.sum_sum_type]
    simp only [D, ep₄, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, Sum.elim_inl, Sum.elim_inr]
    rw [show ∑ i : Fin 2, star (((LinearEquiv.finTwoArrow K K).symm
          ((e x).1, (e x).2.1)) i) * algebraMap ℚ K (![1, -1] i) *
            (((LinearEquiv.finTwoArrow K K).symm ((e y).1, (e y).2.1)) i) =
          star (e x).1 * (e y).1 - star (e x).2.1 * (e y).2.1 by
        simp [LinearEquiv.finTwoArrow]; ring]
    rw [← HermitianForm.diagForm_apply d, heV (e x).2.2 (e y).2.2]
  have hsig := hermSignature_eq_of_equiv W _ h
    (HermitianForm.diagForm D) E hE
  have hsigV := hermSignature_eq_of_equiv V _ hV
    (HermitianForm.diagForm d) eV heV
  rw [hsig, HermitianForm.hermSignature_diagForm (by norm_num), hsigV,
    HermitianForm.hermSignature_diagForm (by norm_num)]
  apply Prod.ext
  · simp only [Prod.fst, D]
    have hset : {z : Fin 2 ⊕ Fin (Module.finrank K V) |
        0 < Sum.elim ![1, -1] d z} =
        {z | Sum.elim (fun i ↦ 0 < (![1, -1] : Fin 2 → ℚ) i) (fun i ↦ 0 < d i) z} := by
      ext z
      cases z <;> rfl
    rw [hset]
    rw [ncard_sum_pred (fun i : Fin 2 ↦ 0 < (![1, -1] : Fin 2 → ℚ) i)
      (fun i ↦ 0 < d i)]
    have hp : {i : Fin 2 | 0 < (![1, -1] : Fin 2 → ℚ) i} =
        ↑({0} : Finset (Fin 2)) := by
      ext i
      fin_cases i <;> norm_num
    rw [hp, Set.ncard_coe_finset]
    simp [Nat.add_comm]
  · simp only [Prod.snd, D]
    have hset : {z : Fin 2 ⊕ Fin (Module.finrank K V) |
        Sum.elim ![1, -1] d z < 0} =
        {z | Sum.elim (fun i ↦ (![1, -1] : Fin 2 → ℚ) i < 0) (fun i ↦ d i < 0) z} := by
      ext z
      cases z <;> rfl
    rw [hset]
    rw [ncard_sum_pred (fun i : Fin 2 ↦ (![1, -1] : Fin 2 → ℚ) i < 0)
      (fun i ↦ d i < 0)]
    have hn : {i : Fin 2 | (![1, -1] : Fin 2 → ℚ) i < 0} =
        ↑({1} : Finset (Fin 2)) := by
      ext i
      fin_cases i <;> norm_num
    rw [hn, Set.ncard_coe_finset]
    simp [Nat.add_comm]

#print axioms hermSignature_pair_coordinates

/-- A nonzero Hermitian inertia index supplies a rational trace vector of the corresponding sign.
Source: Hermitian diagonalization and the trace normalization. -/
theorem hermSignature_trace_signs (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (hp : 0 < (HermitianForm.hermSignature h).1)
    (hm : 0 < (HermitianForm.hermSignature h).2) :
    (∃ x, 0 < traceQuad W h x) ∧ (∃ x, traceQuad W h x < 0) := by
  let K := QuadraticAlgebra ℚ (-3) 0
  obtain ⟨d, hd, e, he⟩ := hermClass_diagonalize W h hh hn
  have hsig := hermSignature_eq_of_equiv W _ h (HermitianForm.diagForm d) e he
  have hdiag := HermitianForm.hermSignature_diagForm (a := (-3 : ℚ)) (by norm_num) d
  have hpcard : 0 < {i | 0 < d i}.ncard := by
    rw [hsig, hdiag] at hp
    exact hp
  have hmcard : 0 < {i | d i < 0}.ncard := by
    rw [hsig, hdiag] at hm
    exact hm
  obtain ⟨ip, hip⟩ := (Set.ncard_pos (s := {i | 0 < d i})).mp hpcard
  obtain ⟨im, him⟩ := (Set.ncard_pos (s := {i | d i < 0})).mp hmcard
  let vp : Fin (Module.finrank K W) → K := Pi.single ip 1
  let vm : Fin (Module.finrank K W) → K := Pi.single im 1
  refine ⟨⟨e.symm vp, ?_⟩, ⟨e.symm vm, ?_⟩⟩
  · have hev := he (e.symm vp) (e.symm vp)
    simp only [e.apply_symm_apply] at hev
    change 0 < 2 * (h (e.symm vp) (e.symm vp)).re
    rw [← hev]
    have hvp : HermitianForm.diagForm d vp vp = algebraMap ℚ K (d ip) := by
      rw [HermitianForm.diagForm_apply, Finset.sum_eq_single ip]
      · simp [vp]
      · intro j _ hji
        simp [vp, hji]
      · simp
    rw [hvp]
    have hip' : 0 < d ip := hip
    change 0 < 2 * d ip
    linarith
  · have hev := he (e.symm vm) (e.symm vm)
    simp only [e.apply_symm_apply] at hev
    change 2 * (h (e.symm vm) (e.symm vm)).re < 0
    rw [← hev]
    have hvm : HermitianForm.diagForm d vm vm = algebraMap ℚ K (d im) := by
      rw [HermitianForm.diagForm_apply, Finset.sum_eq_single im]
      · simp [vm]
      · intro j _ hji
        simp [vm, hji]
      · simp
    rw [hvm]
    have him' : d im < 0 := him
    change 2 * d im < 0
    linarith

#print axioms hermSignature_trace_signs

/-- A regular indefinite Hermitian space of rank at least three splits a normalized
positive-negative pair, with rank and inertia recorded for the complement.
Source: Meyer isotropy and orthogonal Hermitian splitting. -/
theorem hermClass_split_indefinite_pair (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [FiniteDimensional ℚ W] [FiniteDimensional (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (hrank : 3 ≤ Module.finrank (QuadraticAlgebra ℚ (-3) 0) W)
    (hp : 0 < (HermitianForm.hermSignature h).1)
    (hm : 0 < (HermitianForm.hermSignature h).2) :
    ∃ V₁ : Submodule (QuadraticAlgebra ℚ (-3) 0) W,
      ∃ V : Submodule (QuadraticAlgebra ℚ (-3) 0) V₁,
      ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (QuadraticAlgebra ℚ (-3) 0 × QuadraticAlgebra ℚ (-3) 0 × V),
        ((h.domRestrict₁₂ V₁ V₁).domRestrict₁₂ V V).Nondegenerate ∧
        Module.finrank (QuadraticAlgebra ℚ (-3) 0) W =
          Module.finrank (QuadraticAlgebra ℚ (-3) 0) V + 2 ∧
        HermitianForm.hermSignature h =
          ((HermitianForm.hermSignature
            ((h.domRestrict₁₂ V₁ V₁).domRestrict₁₂ V V)).1 + 1,
            (HermitianForm.hermSignature
              ((h.domRestrict₁₂ V₁ V₁).domRestrict₁₂ V V)).2 + 1) ∧
        ∀ x y, h x y = star (e x).1 * (e y).1 -
          star (e x).2.1 * (e y).2.1 + h (e x).2.2 (e y).2.2 := by
  obtain ⟨hp', hm'⟩ := hermSignature_trace_signs W h hh hn hp hm
  obtain ⟨x, hx, hxx⟩ := hermClass_isotropic W h hh hn hrank hp' hm'
  obtain ⟨a, b, haa, hbb, hab⟩ := hermClass_hyperbolic_pair W h hh hn x hx hxx
  obtain ⟨V₁, V, e, hnV, hea, heb, he⟩ :=
    hermClass_pair_decomposition W h hh hn a b haa hbb hab
  refine ⟨V₁, V, e, hnV, ?_, ?_, he⟩
  · have hd := LinearEquiv.finrank_eq e
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self] at hd
    omega
  · exact hermSignature_pair_coordinates W V h
      ((h.domRestrict₁₂ V₁ V₁).domRestrict₁₂ V V)
      ((hh.domRestrict V₁).domRestrict V) hnV e he

#print axioms hermClass_split_indefinite_pair

end HodgeLean.Foundations.HermitianClass
