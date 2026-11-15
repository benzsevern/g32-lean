import HodgeLean.Foundations.Program.ComponentTransportNormalized

/-! # The punctured-sphere word calculation for normalized transport -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- Based maps compose with their specified endpoint equalities.
Source: Mathlib `FundamentalGroup.mapOfEq_apply`. -/
theorem rtc_mapOfEq_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (h : C(X, Z))
    {x : X} {y : Y} {z : Z} (hf : f x = y) (hg : g y = z) (hh : h x = z)
    (heq : ∀ a, h a = g (f a)) (η : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq h hh η =
      FundamentalGroup.mapOfEq g hg (FundamentalGroup.mapOfEq f hf η) := by
  change FundamentalGroup.mapOfEq _ hh (FundamentalGroup.fromPath η.toPath) =
    FundamentalGroup.mapOfEq _ hg (FundamentalGroup.mapOfEq _ hf
      (FundamentalGroup.fromPath η.toPath))
  induction η.toPath using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [b66h_mapOfEq_fromPath, b66h_mapOfEq_fromPath, b66h_mapOfEq_fromPath]
    congr 1
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact heq (p t)

/-- A based identity map acts identically on loop classes.
Source: Mathlib `FundamentalGroup.mapOfEq_apply`. -/
theorem rtc_mapOfEq_id {X : Type*} [TopologicalSpace X]
    (f : C(X, X)) {x : X} (hf : f x = x) (hid : ∀ a, f a = a)
    (η : FundamentalGroup X x) : FundamentalGroup.mapOfEq f hf η = η := by
  change FundamentalGroup.mapOfEq _ hf (FundamentalGroup.fromPath η.toPath) =
    FundamentalGroup.fromPath η.toPath
  induction η.toPath using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [b66h_mapOfEq_fromPath]
    congr 1
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact hid (p t)

/-- Unbased induced maps respect composition with the literal image base point.
Source: Mathlib `FundamentalGroup.map`. -/
theorem rtc_map_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) (η : FundamentalGroup X x) :
    FundamentalGroup.map (g.comp f) x η =
      FundamentalGroup.map g (f x) (FundamentalGroup.map f x η) := by
  change FundamentalGroup.map (g.comp f) x (FundamentalGroup.fromPath η.toPath) =
    FundamentalGroup.map g (f x) (FundamentalGroup.map f x
      (FundamentalGroup.fromPath η.toPath))
  induction η.toPath using Path.Homotopic.Quotient.ind with
  | mk p =>
    change FundamentalGroup.fromPath ⟦p.map (g.comp f).continuous⟧ =
      FundamentalGroup.fromPath ⟦(p.map f.continuous).map g.continuous⟧
    rfl

set_option maxHeartbeats 400000 in
/-- The inverse word endpoint followed by certified transport has the required loop-word action.
This statement retains the two punctured-sphere factors and their literal composite.
Source: `b65b_path_lasso_transport`; `b65v_word_endpoint`; B65-BRAIDCERT REPORT §1.5. -/
theorem rtc_punctured_word_stage (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) :
    ∃ h : b65s_sphere ≃ₜ b6t_punctured mr_base,
    ∃ w : b6t_punctured mr_base ≃ₜ b6t_punctured mr_base,
    ∃ Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, Ψ z = e (h.symm (w.symm z))) ∧
      ∃ hb : Ψ b63gP_basePoint = e (b65s_inclusion x),
        ∀ ρ : (FundamentalGroup (b6t_punctured (b65z_centre p))
            (e (b65s_inclusion x)))ᵐᵒᵖ →* b4b_Group,
          b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
            (FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb
              (MulOpposite.unop (b66h_loop k))))) =
          b65s_word b65b_pathWord (fun j ↦ (ρ (MulOpposite.op
            (FundamentalGroup.map ((⟨e, e.continuous⟩ :
              C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x
              (FundamentalGroup.fromPath ⟦δ j⟧))))⁻¹) := by
  obtain ⟨_, h, γ, _, _, _, htrace, _, hmove⟩ :=
    b65b_path_lasso_transport x δ hδ p hp
  obtain ⟨_, _, _, _, _, _, w, _, hw, hact⟩ :=
    b65v_word_endpoint b65b_word b66h_word_letters
  have hbase : h (b65s_inclusion x) = b63gP_basePoint := by
    apply Subtype.ext
    change (h (b65s_inclusion x) : OnePoint ℂ) = ((mr_basePoint : ℂ) : OnePoint ℂ)
    have hh := htrace 0 0
    simpa [mr_curve_zero] using hh
  have hbase' : h.symm b63gP_basePoint = b65s_inclusion x :=
    h.symm_apply_eq.mpr hbase.symm
  have hw' : w.symm b63gP_basePoint = b63gP_basePoint :=
    w.symm_apply_eq.mpr hw.symm
  let Θ := h.symm.trans e
  have hΘ : Θ b63gP_basePoint = e (b65s_inclusion x) := congrArg e hbase'
  let Ψ := w.symm.trans Θ
  have hb : Ψ b63gP_basePoint = e (b65s_inclusion x) := by
    change Θ (w.symm b63gP_basePoint) = _
    rw [hw', hΘ]
  refine ⟨h, w, Ψ, fun _ ↦ rfl, hb, fun ρ ↦ ?_⟩
  let ν := ρ.comp (MonoidHom.op (FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb))
  have hcancel (η : FundamentalGroup (b6t_punctured mr_base) b63gP_basePoint) :
      FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb
        (FundamentalGroup.mapOfEq ⟨w, w.continuous⟩ hw η) =
      FundamentalGroup.mapOfEq ⟨Θ, Θ.continuous⟩ hΘ η := by
    symm
    apply rtc_mapOfEq_comp _ _ _ hw hb hΘ _ η
    intro z
    change Θ z = Θ (w.symm (w z))
    rw [w.symm_apply_apply]
  have hword : b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
        (FundamentalGroup.mapOfEq ⟨Ψ, Ψ.continuous⟩ hb
          (MulOpposite.unop (b66h_loop k))))) =
      fun k ↦ ρ (MulOpposite.op (FundamentalGroup.mapOfEq ⟨Θ, Θ.continuous⟩ hΘ
        (MulOpposite.unop (b66h_loop k)))) := by
    funext k
    exact (hact ν k).symm.trans (congrArg (fun η ↦ ρ (MulOpposite.op η))
      (hcancel (MulOpposite.unop (b66h_loop k))))
  rw [hword]
  let f : C(b65s_sphere, b6t_punctured (b65z_centre p)) := ⟨e, e.continuous⟩
  let μ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group :=
    { toFun := fun η ↦ ρ (MulOpposite.op ((FundamentalGroup.map f _ η)⁻¹))
      map_one' := by simp
      map_mul' := by intros; simp [mul_inv_rev] }
  have hloops (i : Fin 13) :
      FundamentalGroup.mapOfEq ⟨Θ, Θ.continuous⟩ hΘ (b63gP_loops i) =
        FundamentalGroup.map f _
          (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦γ i⟧)) := by
    let M : Path b63gP_basePoint b63gP_basePoint :=
      (((γ i).map b65s_inclusion.continuous).map h.continuous).cast hbase.symm hbase.symm
    have hM : FundamentalGroup.fromPath ⟦M⟧ = b63gP_loops i :=
      b65x_loops_eq i M (htrace i)
    rw [← hM]
    change FundamentalGroup.mapOfEq _ hΘ
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk M)) = _
    rw [b66h_mapOfEq_fromPath]
    change FundamentalGroup.fromPath ⟦(M.map Θ.continuous).cast hΘ.symm hΘ.symm⟧ =
      FundamentalGroup.fromPath ⟦((γ i).map b65s_inclusion.continuous).map f.continuous⟧
    congr 1
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    change e (h.symm (h (b65s_inclusion (γ i t)))) = _
    rw [h.symm_apply_apply]
    rfl
  have hright := funext (hmove μ)
  simp only [b66h_loop, MulOpposite.unop_op, map_inv, hloops]
  simpa only [μ, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.op_inv, map_inv,
    rtc_map_comp, f, b65b_pathWord] using hright

end HodgeLean.Foundations.Program
