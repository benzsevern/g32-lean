import HodgeLean.Foundations.Program.PullbackMonodromyFoundationsAnnulus

/-! # Descent of the pullback representation to the sphere

The plane chart identifies `b65s_regular` with `b65s_sphere` minus `3`, `1`, `−2` and `∞`. Lassos
about these points have trivial transport, so a representation tied to transport kills the
peripheral classes and descends through the puncture filling.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- The statement of `b65t_puncture_fill`, as a proposition. -/
def b65t_FillProp : Prop :=
  ∀ (X : Set (OnePoint ℂ)) (_ : IsOpen X) (F : Finset (OnePoint ℂ))
    (x : ↥(X \ (F : Set (OnePoint ℂ)))),
    Function.Surjective (FundamentalGroup.map (b65t_fill X F) x) ∧
      (FundamentalGroup.map (b65t_fill X F) x).ker =
        Subgroup.normalClosure (b65t_peripheral X F x) ∧
      ∀ (G : Type) [Group G] (ρ : FundamentalGroup ↥(X \ (F : Set (OnePoint ℂ))) x →* G),
        (∀ c ∈ b65t_peripheral X F x, ρ c = 1) →
          ∃! σ : FundamentalGroup ↥X (b65t_fill X F x) →* G,
            σ.comp (FundamentalGroup.map (b65t_fill X F) x) = ρ

open Classical in
/-- The apparent poles and infinity, the points filled to pass from `b65s_regular` to the sphere. -/
def b65t_F : Finset (OnePoint ℂ) :=
  {((3 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ((-2 : ℂ) : OnePoint ℂ), OnePoint.infty}

theorem b65t_sphere_open : IsOpen b65s_sphere := by
  unfold b65s_sphere
  rw [isOpen_compl_iff, b65s_branch_eq]
  exact (b65s_branchFinset.finite_toSet.image _).isClosed

theorem b65t_coe_mem_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ b65s_sphere \ (b65t_F : Set (OnePoint ℂ)) ↔ z ∈ b65s_regular := by
  have hb : (z : OnePoint ℂ) ∈ b65s_branch ↔ (z = 0 ∨ b65r_P 5 z = 0 ∨ b65r_P (-7) z = 0) := by
    constructor
    · rintro ⟨w, hw, h⟩
      rwa [OnePoint.coe_injective hw]
    · intro h; exact ⟨z, rfl, h⟩
  have hF : (z : OnePoint ℂ) ∈ (b65t_F : Set (OnePoint ℂ)) ↔ (z = 3 ∨ z = 1 ∨ z = -2) := by
    simp only [b65t_F, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
      mem_singleton_iff, OnePoint.coe_eq_coe, OnePoint.coe_ne_infty, or_false]
  simp only [Set.mem_sdiff, b65s_sphere, mem_compl_iff, hb, hF, b65s_regular, mem_ofPred_eq]
  tauto

/-- The plane chart identifies the regular domain with the sphere minus the filled points. -/
def b65t_chart : C(b65s_regular, ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ)))) :=
  ⟨fun z ↦ ⟨(z.val : OnePoint ℂ), (b65t_coe_mem_iff z.val).mpr z.property⟩, by
    apply Continuous.subtype_mk
    exact OnePoint.continuous_coe.comp continuous_subtype_val⟩

theorem b65t_ne_infty (q : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ)))) :
    (q : OnePoint ℂ) ≠ OnePoint.infty := by
  intro h
  apply q.property.2
  rw [h]
  simp [b65t_F]

theorem b65t_elim_mem (q : ↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ)))) :
    (q : OnePoint ℂ).elim 0 id ∈ b65s_regular ∧
      (((q : OnePoint ℂ).elim 0 id : ℂ) : OnePoint ℂ) = q := by
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp (b65t_ne_infty q)
  have h1 : (q : OnePoint ℂ).elim 0 id = w := by rw [← hw]; rfl
  rw [h1]
  refine ⟨(b65t_coe_mem_iff w).mp ?_, hw⟩
  rw [hw]; exact q.property

theorem b65t_chart_embedding : Topology.IsEmbedding b65t_chart :=
  (Topology.IsEmbedding.subtypeVal.of_comp_iff (f := b65t_chart)).mp
    ((OnePoint.isOpenEmbedding_coe.isEmbedding).comp Topology.IsEmbedding.subtypeVal)

theorem b65t_chart_surjective : Function.Surjective b65t_chart := fun q ↦
  ⟨⟨_, (b65t_elim_mem q).1⟩, Subtype.ext (b65t_elim_mem q).2⟩

/-- The inverse chart, written so that `b65t_unchart (b65t_chart x)` is `x` by definition. -/
def b65t_unchart : C(↥(b65s_sphere \ (b65t_F : Set (OnePoint ℂ))), b65s_regular) :=
  ⟨fun q ↦ ⟨(q : OnePoint ℂ).elim 0 id, (b65t_elim_mem q).1⟩, by
    let h := b65t_chart_embedding.toHomeomorphOfSurjective b65t_chart_surjective
    refine h.symm.continuous.congr fun q ↦ ?_
    apply b65t_chart_embedding.injective
    change h (h.symm q) = _
    rw [h.apply_symm_apply]
    exact Subtype.ext (b65t_elim_mem q).2.symm⟩

example (x : b65s_regular) : b65t_unchart (b65t_chart x) = x := rfl


/-- A lasso about a loop with trivial transport is in the kernel of a representation tied to
transport. -/
theorem b65t_lasso_trivial (x : b65s_regular)
    (ρ : FundamentalGroup b65s_regular x →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hρ : ∀ γ : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹))
    {y : b65s_regular} (δ : Path x y) (γ : Path y y)
    (hγ : b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) = 1) :
    ρ (FundamentalGroup.fromPath ⟦(δ.trans γ).trans δ.symm⟧) = 1 := by
  have hcomp : ∀ {p q s : b65s_regular} (α : Path p q) (β : Path q s),
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ ((α.trans β).extend t).val) =
        b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (β.extend t).val) *
          b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (α.extend t).val) := fun α β ↦
    b65f_path_composition _ _ b65t_regular_open _ b65t_pullback_analytic _ _ _ α β
  have hT : b65f_transport (Fin 4 → ℂ) b65r_pullback
      (fun t ↦ (((δ.trans γ).trans δ.symm).extend t).val) = 1 := by
    rw [hcomp, hcomp, hγ, one_mul]
    exact b65t_symm_transport b65t_regular_open b65t_pullback_analytic δ
  rw [hρ] at hT
  set g := ρ (FundamentalGroup.fromPath ⟦(δ.trans γ).trans δ.symm⟧)
  have hop : b65r_operator (b4b_toMatrix g) = b65r_operator (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    have e : b65r_operator (b4b_toMatrix g) =
        ↑(C⁻¹) * ((C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) * b65r_operator (b4b_toMatrix g) *
          ↑(C⁻¹)) * (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) := by
      simp only [mul_assoc, Units.inv_mul, mul_one]
      simp only [← mul_assoc, Units.inv_mul, one_mul]
    rw [e, hT, mul_one, Units.inv_mul]
    ext v i; simp [b65r_operator]
  have hm := b65t_operator_injective hop
  exact Subtype.val_injective (hm.trans (map_one b4b_toMatrix).symm)

theorem b65t_map_lasso {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x y : X} (δ : Path x y) (γ : Path y y) :
    FundamentalGroup.map f x (FundamentalGroup.fromPath ⟦(δ.trans γ).trans δ.symm⟧) =
      FundamentalGroup.fromPath ⟦((δ.map f.continuous).trans (γ.map f.continuous)).trans
        (δ.map f.continuous).symm⟧ := by
  change FundamentalGroup.fromPath ⟦((δ.trans γ).trans δ.symm).map f.continuous⟧ = _
  rw [Path.map_trans, Path.map_trans, Path.map_symm]

/-- The peripheral classes of the sphere minus the filled points act trivially. -/
theorem b65t_peripheral_trivial (x : b65s_regular)
    (ρ : FundamentalGroup b65s_regular x →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hρ : ∀ γ : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹)) :
    ∀ c ∈ b65t_peripheral b65s_sphere b65t_F (b65t_chart x),
      (ρ.comp (FundamentalGroup.map b65t_unchart (b65t_chart x))) c = 1 := by
  rintro c ⟨p, hpF, r, hr, hdisc, honly, y, δ, γ, hγ, rfl⟩
  change ρ (FundamentalGroup.map b65t_unchart (b65t_chart x)
    (FundamentalGroup.fromPath ⟦(δ.trans γ).trans δ.symm⟧)) = 1
  rw [b65t_map_lasso]
  apply b65t_lasso_trivial x ρ C hρ
  have hval : ∀ t, ((γ.map b65t_unchart.continuous) t : ℂ) = ((γ t : OnePoint ℂ)).elim 0 id :=
    fun t ↦ rfl
  have hnotF : ∀ t, (γ t : OnePoint ℂ) ∉ (b65t_F : Set (OnePoint ℂ)) := fun t ↦ (γ t).property.2
  have hpF' : p = ((3 : ℂ) : OnePoint ℂ) ∨ p = ((1 : ℂ) : OnePoint ℂ) ∨
      p = ((-2 : ℂ) : OnePoint ℂ) ∨ p = OnePoint.infty := by
    simpa [b65t_F] using hpF
  have hreg : ∀ z : ℂ, (z : OnePoint ℂ) ∈ b65t_disc p r → (z : OnePoint ℂ) ≠ p →
      z ∈ b65s_regular := by
    intro z hz hzp
    rw [← b65t_coe_mem_iff]
    refine ⟨hdisc hz, fun hF ↦ hzp (honly _ hF hz)⟩
  rcases hpF' with h3 | h1 | h2 | rfl
  rotate_right
  · -- infinity
    apply b65t_loop_near_infty r⁻¹ (inv_pos.mpr hr)
    · intro z hz
      exact hreg z (mem_insert_of_mem _ ⟨z, hz, rfl⟩) (OnePoint.coe_ne_infty z)
    · intro t
      rw [hval]
      have h := hγ t
      have hne : (γ t : OnePoint ℂ) ≠ OnePoint.infty := fun h' ↦ hnotF t (by rw [h']; simp [b65t_F])
      rcases h with h | ⟨w, hw, hwe⟩
      · exact absurd h hne
      · rw [← hwe]; exact hw
  all_goals
    obtain ⟨a, ha, rfl⟩ : ∃ a : ℂ, (a = 3 ∨ a = 1 ∨ a = -2) ∧ p = (a : OnePoint ℂ) := by
      first
        | exact ⟨3, by norm_num, by assumption⟩
        | exact ⟨1, by norm_num, by assumption⟩
        | exact ⟨-2, by norm_num, by assumption⟩
    apply b65t_loop_near_apparent a ha r hr
    · intro z hz hza
      apply hreg z ⟨z, by rwa [mem_ball, dist_eq_norm], rfl⟩
      intro h; exact hza (OnePoint.coe_injective h)
    · intro t
      rw [hval]
      obtain ⟨w, hw, hwe⟩ := hγ t
      have hF := hnotF t
      rw [← hwe] at hF ⊢
      refine ⟨by rwa [mem_ball, dist_eq_norm] at hw, fun hwa ↦ hF ?_⟩
      have hwa' : w = a := hwa
      rw [hwa']
      rcases ha with rfl | rfl | rfl <;> simp [b65t_F]


theorem b65t_unchart_chart_map (x : b65s_regular) (c : FundamentalGroup b65s_regular x) :
    FundamentalGroup.map b65t_unchart (b65t_chart x) (FundamentalGroup.map b65t_chart x c) = c := by
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep c.asHom
  have hc : c = FundamentalGroup.fromPath ⟦γ⟧ := by
    rw [show (⟦γ⟧ : Path.Homotopic.Quotient x x) = c.asHom from hγ]
  rw [hc]
  rfl

theorem b65t_inclusion_map (x : b65s_regular) (c : FundamentalGroup b65s_regular x) :
    FundamentalGroup.map b65s_inclusion x c =
      FundamentalGroup.map (b65t_fill b65s_sphere b65t_F) (b65t_chart x)
        (FundamentalGroup.map b65t_chart x c) := by
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep c.asHom
  have hc : c = FundamentalGroup.fromPath ⟦γ⟧ := by
    rw [show (⟦γ⟧ : Path.Homotopic.Quotient x x) = c.asHom from hγ]
  rw [hc]
  rfl

/-- Descent of a representation tied to transport from `b65s_regular` to the sphere. -/
theorem b65t_descent (hfill : b65t_FillProp) (x : b65s_regular)
    (ρ : FundamentalGroup b65s_regular x →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hρ : ∀ γ : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (γ.extend t).val) =
        (C : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) *
          b65r_operator (b4b_toMatrix (ρ (FundamentalGroup.fromPath ⟦γ⟧))) * ↑(C⁻¹)) :
    ∃ σ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group,
      σ.range = ρ.range ∧
      ∀ c : FundamentalGroup b65s_regular x, σ (FundamentalGroup.map b65s_inclusion x c) = ρ c := by
  obtain ⟨hsurj, -, hdesc⟩ := hfill b65s_sphere b65t_sphere_open b65t_F (b65t_chart x)
  obtain ⟨σ, hσ, -⟩ := hdesc b4b_Group (ρ.comp (FundamentalGroup.map b65t_unchart (b65t_chart x)))
    (b65t_peripheral_trivial x ρ C hρ)
  have key : ∀ c : FundamentalGroup b65s_regular x,
      σ (FundamentalGroup.map b65s_inclusion x c) = ρ c := by
    intro c
    rw [b65t_inclusion_map]
    have := congrArg (fun f ↦ f (FundamentalGroup.map b65t_chart x c)) hσ
    simp only [MonoidHom.comp_apply] at this
    rw [this]
    exact congrArg ρ (b65t_unchart_chart_map x c)
  refine ⟨σ, ?_, key⟩
  ext g
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨d', rfl⟩ := hsurj d
    have := congrArg (fun f ↦ f d') hσ
    simp only [MonoidHom.comp_apply] at this
    exact ⟨_, this.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, key c⟩

end HodgeLean.Foundations.Program
