import HodgeLean.Foundations.Program.HalfTwistAction

/-! # Words of half-twists and the certificate word
Composition of elementary ambient isotopies in list order, negative letters by the inverse
isotopy, and the specialization to the 86-letter certificate word.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Complex Set Topology
namespace HodgeLean.Foundations.Program

/-- The finite-word conclusion, as in `b66h_word_realization`. -/
def b66h_WordRealized (w : List b65s_Move) : Prop :=
  ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
    Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
    H 0 = Homeomorph.refl _ ∧
    (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
    (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
    (∃ σ : Equiv.Perm (Fin 12), ∀ k,
      H 1 (mr_marks k : OnePoint ℂ) = (mr_marks (σ k) : OnePoint ℂ)) ∧
    ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
      (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
      ∃ hb : h b63gP_basePoint = b63gP_basePoint,
        ∀ ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group, ∀ k,
          ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
          (MulOpposite.unop (b66h_loop k)))) =
            b65s_word w (fun i ↦ ρ (b66h_loop i)) k

/-! ## Induced maps -/

theorem b66h_mapOfEq_comp (f g h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base)
    (hf : f b63gP_basePoint = b63gP_basePoint) (hg : g b63gP_basePoint = b63gP_basePoint)
    (hh : h b63gP_basePoint = b63gP_basePoint) (hfg : ∀ z, h z = g (f z))
    (x : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint) :
    FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hh x =
      FundamentalGroup.mapOfEq ⟨g, g.continuous⟩ hg
        (FundamentalGroup.mapOfEq ⟨f, f.continuous⟩ hf x) := by
  change FundamentalGroup.mapOfEq _ hh (FundamentalGroup.fromPath x.toPath) =
    FundamentalGroup.mapOfEq _ hg (FundamentalGroup.mapOfEq _ hf
      (FundamentalGroup.fromPath x.toPath))
  induction x.toPath using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [b66h_mapOfEq_fromPath, b66h_mapOfEq_fromPath, b66h_mapOfEq_fromPath]
      congr 1
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      simp [hfg]

theorem b66h_mapOfEq_id (h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base)
    (hh : h b63gP_basePoint = b63gP_basePoint) (hid : ∀ z, h z = z)
    (x : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint) :
    FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hh x = x := by
  change FundamentalGroup.mapOfEq _ hh (FundamentalGroup.fromPath x.toPath) =
    FundamentalGroup.fromPath x.toPath
  induction x.toPath using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [b66h_mapOfEq_fromPath]
      congr 1
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      simp [hid]

/-! ## Moves -/

/-- The inverse Hurwitz move in any group. -/
def b66h_negStep {G : Type*} [Group G] (i : Fin 12) (t : Fin 13 → G) : Fin 13 → G :=
  Function.update (t ∘ Equiv.swap i.castSucc i.succ) i.succ
    ((t i.succ)⁻¹ * t i.castSucc * t i.succ)

theorem b66h_step_negative (i : Fin 12) (t : Fin 13 → b4b_Group) :
    b65s_step (.negative i) t = b66h_negStep i t := rfl

theorem b66h_braid_map {G G' : Type*} [Group G] [Group G'] (ψ : G →* G') (i : Fin 12)
    (T : Fin 13 → G) (k : Fin 13) :
    ψ (b4_braid i.castSucc i.succ T k) = b4_braid i.castSucc i.succ (fun m ↦ ψ (T m)) k := by
  unfold b4_braid
  by_cases hk : k = i.castSucc
  · subst hk; simp
  · simp [Function.update_of_ne hk]

theorem b66h_negStep_map {G G' : Type*} [Group G] [Group G'] (ψ : G →* G') (i : Fin 12)
    (T : Fin 13 → G) (k : Fin 13) :
    ψ (b66h_negStep i T k) = b66h_negStep i (fun m ↦ ψ (T m)) k := by
  unfold b66h_negStep
  by_cases hk : k = i.succ
  · subst hk; simp
  · simp [Function.update_of_ne hk]

theorem b66h_negStep_braid {G : Type*} [Group G] (i : Fin 12) (T : Fin 13 → G) :
    b66h_negStep i (b4_braid i.castSucc i.succ T) = T := by
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  funext k
  unfold b66h_negStep b4_braid
  by_cases hk : k = i.succ
  · subst hk
    simp [Function.update_of_ne hne.symm, Function.update_self, Equiv.swap_apply_right]
    group
  · rw [Function.update_of_ne hk, Function.comp_apply]
    by_cases hk' : k = i.castSucc
    · subst hk'
      simp [Equiv.swap_apply_left, Function.update_of_ne hne.symm]
    · rw [Equiv.swap_apply_of_ne_of_ne hk' hk, Function.update_of_ne hk']
      simp [Equiv.swap_apply_of_ne_of_ne hk' hk]

/-- The opposite of an induced map. -/
def b66h_opMap (h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base)
    (hb : h b63gP_basePoint = b63gP_basePoint) :
    (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →*
      (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ :=
  MonoidHom.op (FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)

theorem b66h_opMap_apply (h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base)
    (hb : h b63gP_basePoint = b63gP_basePoint) (x) :
    b66h_opMap h hb x = MulOpposite.op (FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb
      (MulOpposite.unop x)) := rfl

/-! ## Letters -/

theorem b66h_nil : b66h_WordRealized [] := by
  refine ⟨fun _ ↦ Homeomorph.refl _, continuous_snd, rfl, fun _ ↦ rfl, fun _ ↦ rfl,
    ⟨1, fun k ↦ rfl⟩, Homeomorph.refl _, fun z ↦ rfl, rfl, fun ρ k ↦ ?_⟩
  exact congrArg (fun x ↦ ρ (MulOpposite.op x))
    (b66h_mapOfEq_id (Homeomorph.refl _) rfl (fun _ ↦ rfl) (MulOpposite.unop (b66h_loop k)))

theorem b66h_positive (i : Fin 12) (hi : i ≠ 0) : b66h_WordRealized [.positive i] := by
  obtain ⟨ε, hε, H, hHc, hH0, hHI, hHB, hHQ, h, hh, hb, hact⟩ := b66h_half_twist_body i hi
  refine ⟨H, hHc, hH0, hHI, hHB, ⟨Equiv.swap (⟨11 - i.val, by omega⟩ : Fin 11).castSucc
    (⟨11 - i.val, by omega⟩ : Fin 11).succ, fun k ↦ ?_⟩, h, hh, hb, fun ρ k ↦ ?_⟩
  · rw [hHQ 1 k, Set.Icc.coe_one, (b66h_track_endpoints_body _ ε hε).2]
    rfl
  · rw [hact k, b66h_braid_map ρ i]
    rfl

theorem b66h_negative (i : Fin 12) (hi : i ≠ 0) : b66h_WordRealized [.negative i] := by
  obtain ⟨ε, hε, H, hHc, hH0, hHI, hHB, hHQ, h, hh, hb, hact⟩ := b66h_half_twist_body i hi
  set j : Fin 11 := ⟨11 - i.val, by omega⟩
  -- the inverse isotopy
  let F : unitInterval × OnePoint ℂ → unitInterval × OnePoint ℂ := fun q ↦ (q.1, H q.1 q.2)
  have hFc : Continuous F := continuous_fst.prodMk hHc
  have hFb : Function.Bijective F := by
    constructor
    · rintro ⟨t, a⟩ ⟨t', b⟩ hab
      simp only [F, Prod.mk.injEq] at hab
      obtain ⟨rfl, h2⟩ := hab
      rw [(H t).injective h2]
    · rintro ⟨t, b⟩
      exact ⟨(t, (H t).symm b), by simp [F]⟩
  let E : unitInterval × OnePoint ℂ ≃ₜ unitInterval × OnePoint ℂ :=
    hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hFb)
  have hEs : ∀ t w, E.symm (t, w) = (t, (H t).symm w) := by
    intro t w
    apply E.injective
    rw [E.apply_symm_apply]
    change (t, w) = F (t, (H t).symm w)
    simp [F]
  have hHs : (fun q : unitInterval × OnePoint ℂ ↦ (H q.1).symm q.2) = fun q ↦ (E.symm q).2 := by
    funext q; rw [hEs]
  have hsw : ∀ k, H 1 (mr_marks k : OnePoint ℂ) =
      (mr_marks (Equiv.swap j.castSucc j.succ k) : OnePoint ℂ) := by
    intro k
    rw [hHQ 1 k, Set.Icc.coe_one, (b66h_track_endpoints_body _ ε hε).2]
    rfl
  have hbs : h.symm b63gP_basePoint = b63gP_basePoint := by
    rw [Homeomorph.symm_apply_eq, hb]
  refine ⟨fun t ↦ (H t).symm, ?_, ?_, fun t ↦ ?_, fun t ↦ ?_,
    ⟨Equiv.swap j.castSucc j.succ, fun k ↦ ?_⟩, h.symm, fun z ↦ ?_, hbs, fun ρ k ↦ ?_⟩
  · rw [hHs]; exact continuous_snd.comp E.symm.continuous
  · show (H 0).symm = _
    rw [hH0]; rfl
  · rw [Homeomorph.symm_apply_eq, hHI]
  · rw [Homeomorph.symm_apply_eq, hHB]
  · rw [Homeomorph.symm_apply_eq, hsw, Equiv.swap_apply_self]
  · show _ = (H 1).symm _
    rw [Homeomorph.eq_symm_apply, ← hh, Homeomorph.apply_symm_apply]
  · -- the inverse move
    set L := b66h_loop
    have hΨ : ∀ m, b66h_opMap h hb (L m) = b4_braid i.castSucc i.succ L m := hact
    have hinj : Function.Injective (b66h_opMap h hb) := by
      intro x y hxy
      have hl : ∀ x, b66h_opMap h.symm hbs (b66h_opMap h hb x) = x := by
        intro x
        rw [b66h_opMap_apply, b66h_opMap_apply, MulOpposite.unop_op,
          ← b66h_mapOfEq_comp h h.symm (Homeomorph.refl _) hb hbs rfl
            (fun z ↦ (h.symm_apply_apply z).symm)]
        exact (congrArg MulOpposite.op (b66h_mapOfEq_id (Homeomorph.refl _) rfl (fun _ ↦ rfl)
          (MulOpposite.unop x))).trans (MulOpposite.op_unop x)
      rw [← hl x, hxy, hl y]
    have hr : ∀ x, b66h_opMap h hb (b66h_opMap h.symm hbs x) = x := by
      intro x
      rw [b66h_opMap_apply, b66h_opMap_apply, MulOpposite.unop_op,
        ← b66h_mapOfEq_comp h.symm h (Homeomorph.refl _) hbs hb rfl
          (fun z ↦ (h.apply_symm_apply z).symm)]
      exact (congrArg MulOpposite.op (b66h_mapOfEq_id (Homeomorph.refl _) rfl (fun _ ↦ rfl)
        (MulOpposite.unop x))).trans (MulOpposite.op_unop x)
    have hN : b66h_opMap h.symm hbs (L k) = b66h_negStep i L k := by
      apply hinj
      rw [hr, b66h_negStep_map, show (fun m ↦ b66h_opMap h hb (L m)) =
        b4_braid i.castSucc i.succ L from funext hΨ, b66h_negStep_braid]
    change ρ (b66h_opMap h.symm hbs (L k)) = _
    rw [hN, b66h_negStep_map]
    rfl

/-! ## Words -/

theorem b66h_cons (m : b65s_Move) (w : List b65s_Move) (hm : b66h_WordRealized [m])
    (hw : b66h_WordRealized w) : b66h_WordRealized (m :: w) := by
  obtain ⟨H1, hHc1, hH01, hHI1, hHB1, ⟨σ1, hσ1⟩, h1, hh1, hb1, hact1⟩ := hm
  obtain ⟨H2, hHc2, hH02, hHI2, hHB2, ⟨σ2, hσ2⟩, h2, hh2, hb2, hact2⟩ := hw
  have hb : (h2.trans h1) b63gP_basePoint = b63gP_basePoint := by
    rw [Homeomorph.trans_apply, hb2, hb1]
  refine ⟨fun t ↦ (H2 t).trans (H1 t), hHc1.comp (continuous_fst.prodMk hHc2), ?_,
    fun t ↦ ?_, fun t ↦ ?_, ⟨σ2.trans σ1, fun k ↦ ?_⟩, h2.trans h1, fun z ↦ ?_, hb,
    fun ρ k ↦ ?_⟩
  · show (H2 0).trans (H1 0) = _
    rw [hH01, hH02]; rfl
  · simp [hHI1, hHI2]
  · simp [hHB1, hHB2]
  · simp [hσ1, hσ2]
  · simp [hh1, hh2]
  · rw [b66h_mapOfEq_comp h2 h1 _ hb2 hb1 hb (fun z ↦ rfl)]
    have := hact2 (ρ.comp (b66h_opMap h1 hb1)) k
    simp only [MonoidHom.comp_apply, b66h_opMap_apply, MulOpposite.unop_op] at this
    rw [this]
    have hT : (fun i ↦ ρ (MulOpposite.op (FundamentalGroup.mapOfEq ⟨h1, h1.continuous⟩ hb1
        (MulOpposite.unop (b66h_loop i))))) = b65s_step m (fun i ↦ ρ (b66h_loop i)) := by
      funext i; exact hact1 ρ i
    rw [hT]
    rfl

theorem b66h_word_body (w : List b65s_Move)
    (hw : ∀ m ∈ w, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i)) :
    b66h_WordRealized w := by
  induction w with
  | nil => exact b66h_nil
  | cons m w ih =>
    apply b66h_cons m w _ (ih fun m' hm' ↦ hw m' (List.mem_cons_of_mem _ hm'))
    obtain ⟨i, hi, rfl | rfl⟩ := hw m List.mem_cons_self
    · exact b66h_positive i hi
    · exact b66h_negative i hi

/-! ## The certificate word -/

/-- Letters that are elementary half-twists away from the outer puncture. -/
def b66h_letterOK : b65s_Move → Bool
  | .positive i => i ≠ 0
  | .negative i => i ≠ 0
  | .conjugate _ => false

theorem b66h_word_ok : b65b_word.all b66h_letterOK = true := by
  decide

theorem b66h_word_letters :
    ∀ m ∈ b65b_word, ∃ i : Fin 12, i ≠ 0 ∧ (m = .positive i ∨ m = .negative i) := by
  intro m hm
  have h := List.all_eq_true.mp b66h_word_ok m hm
  cases m with
  | positive i => exact ⟨i, by simpa [b66h_letterOK] using h, Or.inl rfl⟩
  | negative i => exact ⟨i, by simpa [b66h_letterOK] using h, Or.inr rfl⟩
  | conjugate g => simp [b66h_letterOK] at h

theorem b66h_certificate_body
    (ρ : (FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint)ᵐᵒᵖ →* b4b_Group)
    (hρ : ∀ i, ρ (b66h_loop i) = b65s_columnRoot i) :
    ∃ H : unitInterval → OnePoint ℂ ≃ₜ OnePoint ℂ,
      Continuous (fun q : unitInterval × OnePoint ℂ ↦ H q.1 q.2) ∧
      H 0 = Homeomorph.refl _ ∧
      (∀ t, H t OnePoint.infty = OnePoint.infty) ∧
      (∀ t, H t (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) ∧
      (∃ σ : Equiv.Perm (Fin 12), ∀ k,
        H 1 (mr_marks k : OnePoint ℂ) = (mr_marks (σ k) : OnePoint ℂ)) ∧
      ∃ h : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
        (∀ z, (h z : OnePoint ℂ) = H 1 z) ∧
        ∃ hb : h b63gP_basePoint = b63gP_basePoint,
          ∀ i, ρ (MulOpposite.op ((FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hb)
            (MulOpposite.unop (b66h_loop i)))) =
            b4_conjTuple (b4b_generators 1)⁻¹ b65b_final i := by
  obtain ⟨H, hHc, hH0, hHI, hHB, hσ, h, hh, hb, hact⟩ := b66h_word_body b65b_word b66h_word_letters
  refine ⟨H, hHc, hH0, hHI, hHB, hσ, h, hh, hb, fun i ↦ ?_⟩
  rw [hact ρ i, show (fun i ↦ ρ (b66h_loop i)) = b65s_columnRoot from funext hρ,
    b65b_replay.1]

end HodgeLean.Foundations.Program
