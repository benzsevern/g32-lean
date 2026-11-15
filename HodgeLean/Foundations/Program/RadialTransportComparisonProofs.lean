import HodgeLean.Foundations.Program.RadialTransportAvoidance

/-! # Radial and ambient configuration transport
Implication from explicit arc control and ambient motion to endpoint comparison.
Based-loop conclusions use restrictions of the comparison maps.
Ambient class selection and quantitative reparametrization remain planned in
`docs/specs/spec-rtc.md`; this module freezes the first transport stage.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem rtc_homotopy_action {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (F : ContinuousMap.Homotopy f g) (x : X) :
    ∃ β : Path (f x) (g x), ∀ η : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (FundamentalGroup.map f x η) = FundamentalGroup.map g x η := by
  refine ⟨F.evalAt x, ?_⟩
  intro η
  obtain ⟨p, hp⟩ := Quotient.exists_rep η.asHom
  have he : η = FundamentalGroup.fromPath ⟦p⟧ := by
    exact congrArg FundamentalGroup.fromPath hp.symm
  rw [he]
  change FundamentalGroup.fromPath _ = FundamentalGroup.fromPath _
  apply congrArg FundamentalGroup.fromPath
  exact Quotient.sound (RiemannRochTop_homotopy_loop_conjugacy F x p)

def rtc_restrict_comparison (a b : Fin 10 → ℂ)
    (R A : b6t_punctured a ≃ₜ b6t_punctured b)
    (K : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hbij : ∀ t, Function.Bijective (fun z ↦ K (t, z)))
    (hzero : ∀ z : b6t_punctured a, K (0, z.val) = (R z : OnePoint ℂ))
    (hone : ∀ z : b6t_punctured a, K (1, z.val) = (A z : OnePoint ℂ))
    (hmark : ∀ t j, K (t, b6_branch a j) = b6_branch b j) :
    ContinuousMap.Homotopy (⟨R, R.continuous⟩ : C(_, _)) ⟨A, A.continuous⟩ := by
  have hav (t : unitInterval) (z : b6t_punctured a) : K (t, z.val) ∈ b6t_punctured b := by
    rintro ⟨j, hj⟩
    apply z.property
    exact ⟨j, (hbij t).1 ((hmark t j).trans hj)⟩
  exact
    { toFun := fun q ↦ ⟨K (q.1, q.2.val), hav q.1 q.2⟩
      continuous_toFun := (K.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun z ↦ Subtype.ext (hzero z)
      map_one_left := fun z ↦ Subtype.ext (hone z) }

set_option maxHeartbeats 400000 in
def rtc_radial_motion (a : Fin 10 → ℂ) (ha : a ∈ b6_chart)
    (P : C(unitInterval, b6t_polydisc a)) :
    C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
  (⟨fun q : b6t_polydisc a × OnePoint ℂ ↦ b6t_sphere a q.1.val q.2,
    b6t_continuous a ha⟩ : C(b6t_polydisc a × OnePoint ℂ, OnePoint ℂ)).comp
      (P.prodMap (ContinuousMap.id (OnePoint ℂ)))

set_option maxHeartbeats 400000 in
theorem rtc_segment_comparison_aux (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart)
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (h0 : ∀ z, H (0, z) = z)
    (hmarks : ∀ t j, H (t, b6_branch (γ 0) j) = b6_branch (γ t) j)
    (V : Set (Fin 10 → ℂ)) (hV : Convex ℝ V)
    (hsub : V ⊆ b6t_polydisc (γ 0)) (harc : ∀ t, γ t ∈ V)
    (R A : b6t_punctured (γ 0) ≃ₜ b6t_punctured (γ 1))
    (hR : ∀ z, (R z : OnePoint ℂ) = b6t_sphere (γ 0) (γ 1) z)
    (hA : ∀ z, (A z : OnePoint ℂ) = H (1, z))
    (x : b6t_punctured (γ 0)) :
    (∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = b6t_sphere (γ 0) (γ 1) z) ∧
      (∀ z, K (1, z) = H (1, z)) ∧
      (∀ t j, K (t, b6_branch (γ 0) j) = b6_branch (γ 1) j)) ∧
    ∃ β : Path (R x) (A x), ∀ η : FundamentalGroup (b6t_punctured (γ 0)) x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (FundamentalGroup.map ⟨R, R.continuous⟩ x η) =
        FundamentalGroup.map ⟨A, A.continuous⟩ x η := by
  let pg : C(unitInterval, b6t_polydisc (γ 0)) :=
    ⟨fun t ↦ ⟨γ t, hsub (harc t)⟩, γ.continuous.subtype_mk _⟩
  let F := rtc_radial_motion (γ 0) (hγ 0) pg
  have hF (t : unitInterval) : Function.Bijective (fun z ↦ F (t, z)) := by
    obtain ⟨e, he⟩ := b6t_homeomorph (γ 0) (hγ 0) (γ t) (hsub (harc t))
    exact (show (fun z ↦ F (t, z)) = e from funext fun z ↦ (he z).symm) ▸ e.bijective
  obtain ⟨K, hKb, hK0, hK1, hKm⟩ := rtc_same_tracks F H hF hH
    (fun z ↦ congrFun (b6t_identity (γ 0)) z) h0
    (b6_branch (γ 0)) (fun t ↦ b6_branch (γ t))
    (fun t j ↦ b6t_marks (γ 0) (hγ 0) (γ t) (hsub (harc t)) j) hmarks
  refine ⟨⟨K, hKb, hK0, hK1, hKm⟩, ?_⟩
  exact rtc_homotopy_action
    (rtc_restrict_comparison (γ 0) (γ 1) R A K hKb
      (fun z ↦ (hK0 z).trans (hR z).symm)
      (fun z ↦ (hK1 z).trans (hA z).symm) hKm) x

theorem rtc_arc_to_chord_aux {a b : b6_chart} (α : Path a b)
    (V : Set (Fin 10 → ℂ)) (hV : Convex ℝ V) (hsub : V ⊆ b6_chart)
    (harc : ∀ t, (α t).val ∈ V) :
    ∃ χ : Path a b, (∀ t, (χ t).val =
      (1 - (t : ℝ)) • a.val + (t : ℝ) • b.val) ∧ α.Homotopic χ := by
  have ha : a.val ∈ V := by simpa using harc 0
  have hb : b.val ∈ V := by simpa using harc 1
  have hm (t : unitInterval) : (1 - (t : ℝ)) • a.val + (t : ℝ) • b.val ∈ V :=
    hV ha hb (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel _ _)
  let χ : Path a b :=
    { toFun := fun t ↦ ⟨(1 - (t : ℝ)) • a.val + (t : ℝ) • b.val, hsub (hm t)⟩
      continuous_toFun := (((continuous_const.sub continuous_subtype_val).smul
        continuous_const).add (continuous_subtype_val.smul continuous_const)).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  refine ⟨χ, fun _ ↦ rfl, ?_⟩
  have : ContractibleSpace V := hV.contractibleSpace ⟨a.val, ha⟩
  let inc : C(V, b6_chart) :=
    ⟨fun z ↦ ⟨z.val, hsub z.property⟩, continuous_subtype_val.subtype_mk _⟩
  let lift : (p : Path a b) → (∀ t, (p t).val ∈ V) →
      Path (⟨a.val, ha⟩ : V) ⟨b.val, hb⟩ := fun p hp ↦
    { toFun := fun t ↦ ⟨(p t).val, hp t⟩
      continuous_toFun := (continuous_subtype_val.comp p.continuous).subtype_mk _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simp) }
  have h := (SimplyConnectedSpace.paths_homotopic (lift α harc) (lift χ hm)).map inc
  have h1 : (lift α harc).map inc.continuous = α := by ext t; rfl
  have h2 : (lift χ hm).map inc.continuous = χ := by ext t; rfl
  rwa [h1, h2] at h

set_option maxHeartbeats 400000 in
theorem rtc_convex_comparison (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart)
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (h0 : ∀ z, H (0, z) = z)
    (hmarks : ∀ t j, H (t, b6_branch (γ 0) j) = b6_branch (γ t) j)
    (V : Set (Fin 10 → ℂ)) (hV : Convex ℝ V) (hsub : V ⊆ b6_chart)
    (harc : ∀ t, γ t ∈ V) (hstep : γ 1 ∈ b6t_polydisc (γ 0)) :
    ∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = b6t_sphere (γ 0) (γ 1) z) ∧
      (∀ z, K (1, z) = H (1, z)) ∧
      (∀ t j, K (t, b6_branch (γ 0) j) = b6_branch (γ 1) j) := by
  let α : Path (⟨γ 0, hγ 0⟩ : b6_chart) ⟨γ 1, hγ 1⟩ :=
    { toFun := fun t ↦ ⟨γ t, hγ t⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := rfl
      target' := rfl }
  obtain ⟨χ, hχ, hhom⟩ := rtc_arc_to_chord_aux α V hV hsub harc
  have hpoly : Convex ℝ (b6t_polydisc (γ 0)) := by
    intro x hx y hy a b ha hb hab i
    exact convex_ball (γ 0 i) (b6t_radius (γ 0)) (hx i) (hy i) ha hb hab
  have hp (t : unitInterval) : (χ t).val ∈ b6t_polydisc (γ 0) := by
    rw [hχ]
    exact hpoly (b6t_polydisc_neighbourhood _ (hγ 0)).1 hstep
      (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel _ _)
  let pg : C(unitInterval, b6t_polydisc (γ 0)) :=
    ⟨fun t ↦ ⟨(χ t).val, hp t⟩,
      (continuous_subtype_val.comp χ.continuous).subtype_mk _⟩
  let F := rtc_radial_motion (γ 0) (hγ 0) pg
  have hF (t : unitInterval) : Function.Bijective (fun z ↦ F (t, z)) := by
    obtain ⟨e, he⟩ := b6t_homeomorph (γ 0) (hγ 0) (χ t).val (hp t)
    exact (show (fun z ↦ F (t, z)) = e from funext fun z ↦ (he z).symm) ▸ e.bijective
  obtain ⟨K, hb, hz, ho, hm⟩ := rtc_configuration_comparison χ α hhom.symm
    F H hF hH
    (fun z ↦ by
      change b6t_sphere (γ 0) (χ 0).val z = z
      rw [χ.source]
      exact congrFun (b6t_identity (γ 0)) z)
    h0 (fun t j ↦ b6t_marks _ (hγ 0) _ (hp t) j) hmarks
  refine ⟨K, hb, ?_, ho, hm⟩
  intro z
  have h := hz z
  change K (0, z) = b6t_sphere (γ 0) (χ 1).val z at h
  simpa only [χ.target] using h

theorem rtc_finite_comparison (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart)
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (h0 : ∀ z, H (0, z) = z)
    (hmarks : ∀ t j, H (t, b6_branch (γ 0) j) = b6_branch (γ t) j)
    (N : ℕ) (hN : 0 < N)
    (hsteps : ∀ k < N, b65y_sample γ N (k + 1) ∈
      b6t_polydisc (b65y_sample γ N k))
    (harcs : ∀ k < N, ∃ V : Set (Fin 10 → ℂ), Convex ℝ V ∧ V ⊆ b6_chart ∧
      ∀ t : unitInterval, (k : ℝ) / N ≤ (t : ℝ) →
        (t : ℝ) ≤ ((k : ℝ) + 1) / N → γ t ∈ V) :
    ∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = b65y_radial (b65y_sample γ N) N z) ∧
      (∀ z, K (1, z) = H (1, z)) ∧
      (∀ t j, K (t, b6_branch (γ 0) j) = b6_branch (γ 1) j) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let T : ℕ → unitInterval := fun k ↦ Set.projIcc 0 1 zero_le_one ((k : ℝ) / N)
  have hgrid (k : ℕ) (hk : k ≤ N) : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNr]
    exact_mod_cast hk
  have hTv (k : ℕ) (hk : k ≤ N) : (T k : ℝ) = (k : ℝ) / N := by
    dsimp [T]
    rw [Set.projIcc_of_mem _ (hgrid k hk)]
  have hT0 : T 0 = 0 := by
    apply Subtype.ext
    rw [hTv 0 (by omega)]
    simp
  have hTN : T N = 1 := by
    apply Subtype.ext
    rw [hTv N le_rfl, div_self hNr.ne']
    rfl
  obtain ⟨U, hU⟩ := rtc_family_inverse H hH
  have hUb (t : unitInterval) : Function.Bijective (fun z ↦ U (t, z)) := by
    constructor
    · intro x y h
      simpa only [(hU t x).1, (hU t y).1] using congrArg (fun z ↦ H (t, z)) h
    · intro z
      exact ⟨H (t, z), (hU t z).2⟩
  have hind : ∀ k ≤ N, ∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = b65y_radial (b65y_sample γ N) k z) ∧
      (∀ z, K (1, z) = H (T k, z)) ∧
      (∀ t j, K (t, b6_branch (γ 0) j) = b6_branch (γ (T k)) j) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⟨Prod.snd, continuous_snd⟩, fun _ ↦ Function.bijective_id,
        fun _ ↦ rfl, ?_, ?_⟩
      · intro z
        exact (hT0 ▸ h0 z).symm
      · intro t j
        change b6_branch (γ 0) j = b6_branch (γ (T 0)) j
        rw [hT0]
    | succ k ih =>
      intro hk
      obtain ⟨K, hb, hz, ho, hm⟩ := ih (by omega)
      have hkN : k < N := by omega
      have hτmem (t : unitInterval) : ((k : ℝ) + (t : ℝ)) / N ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg k) t.2.1) hNr.le, ?_⟩
        rw [div_le_one hNr]
        have hkn : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
        linarith [t.2.2]
      let τ : C(unitInterval, unitInterval) :=
        ⟨fun t ↦ ⟨((k : ℝ) + (t : ℝ)) / N, hτmem t⟩,
          ((continuous_const.add continuous_subtype_val).div_const (N : ℝ)).subtype_mk _⟩
      have hτ0 : τ 0 = T k := by
        apply Subtype.ext
        change ((k : ℝ) + (0 : unitInterval).val) / N = (T k).val
        rw [hTv k (by omega)]
        simp
      have hτ1 : τ 1 = T (k + 1) := by
        apply Subtype.ext
        change ((k : ℝ) + (1 : unitInterval).val) / N = (T (k + 1)).val
        rw [hTv (k + 1) hk]
        simp
      let L : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
        ⟨fun w ↦ H (τ w.1, U (T k, w.2)),
          H.continuous.comp ((τ.continuous.comp continuous_fst).prodMk
            (U.continuous.comp (continuous_const.prodMk continuous_snd)))⟩
      have hLb (t : unitInterval) : Function.Bijective (fun z ↦ L (t, z)) :=
        (hH (τ t)).comp (hUb (T k))
      have hL0 (z : OnePoint ℂ) : L (0, z) = z := by
        change H (τ 0, U (T k, z)) = z
        rw [hτ0]
        exact (hU (T k) z).1
      have hLm (t : unitInterval) (j : Fin 13) :
          L (t, b6_branch ((γ.comp τ) 0) j) = b6_branch ((γ.comp τ) t) j := by
        change H (τ t, U (T k, b6_branch (γ (τ 0)) j)) = b6_branch (γ (τ t)) j
        rw [hτ0, ← hmarks (T k) j, (hU (T k) _).2, hmarks]
      obtain ⟨V, hV, hsub, hv⟩ := harcs k hkN
      have harc (t : unitInterval) : (γ.comp τ) t ∈ V := by
        apply hv (τ t)
        · change (k : ℝ) / N ≤ ((k : ℝ) + (t : ℝ)) / N
          exact div_le_div_of_nonneg_right (by linarith [t.2.1]) hNr.le
        · change ((k : ℝ) + (t : ℝ)) / N ≤ ((k : ℝ) + 1) / N
          exact div_le_div_of_nonneg_right (by linarith [t.2.2]) hNr.le
      have hstep : (γ.comp τ) 1 ∈ b6t_polydisc ((γ.comp τ) 0) := by
        change γ (τ 1) ∈ b6t_polydisc (γ (τ 0))
        rw [hτ0, hτ1]
        exact hsteps k hkN
      obtain ⟨J, hjb, hj0, hj1, hjm⟩ := rtc_convex_comparison (γ.comp τ)
        (fun t ↦ hγ (τ t)) L hLb hL0 hLm V hV hsub harc hstep
      let M : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
        ⟨fun w ↦ J (w.1, K w),
          J.continuous.comp (continuous_fst.prodMk K.continuous)⟩
      refine ⟨M, fun t ↦ (hjb t).comp (hb t), ?_, ?_, ?_⟩
      · intro z
        change J (0, K (0, z)) = b6t_sphere _ _ (b65y_radial _ k z)
        rw [hz, hj0]
        change b6t_sphere (γ (τ 0)) (γ (τ 1)) _ = _
        rw [hτ0, hτ1]
        rfl
      · intro z
        change J (1, K (1, z)) = H (T (k + 1), z)
        rw [ho, hj1]
        change H (τ 1, U (T k, H (T k, z))) = _
        rw [hτ1, (hU (T k) z).2]
      · intro t j
        change J (t, K (t, b6_branch (γ 0) j)) = _
        rw [hm]
        have hj := hjm t j
        change J (t, b6_branch (γ (τ 0)) j) = b6_branch (γ (τ 1)) j at hj
        simpa only [hτ0, hτ1] using hj
  obtain ⟨K, hb, hz, ho, hm⟩ := hind N le_rfl
  exact ⟨K, hb, hz, fun z ↦ by simpa only [hTN] using ho z,
    fun t j ↦ by simpa only [hTN] using hm t j⟩

theorem rtc_composition_aux (γ : C(unitInterval, Fin 10 → ℂ))
    (hγ : ∀ t, γ t ∈ b6_chart)
    (H : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (h0 : ∀ z, H (0, z) = z)
    (hmarks : ∀ t j, H (t, b6_branch (γ 0) j) = b6_branch (γ t) j)
    (N : ℕ) (hN : 0 < N)
    (hsteps : ∀ k < N, b65y_sample γ N (k + 1) ∈
      b6t_polydisc (b65y_sample γ N k))
    (harcs : ∀ k < N, ∃ V : Set (Fin 10 → ℂ), Convex ℝ V ∧ V ⊆ b6_chart ∧
      ∀ t : unitInterval, (k : ℝ) / N ≤ (t : ℝ) →
        (t : ℝ) ≤ ((k : ℝ) + 1) / N → γ t ∈ V)
    (R A : b6t_punctured (γ 0) ≃ₜ b6t_punctured (γ 1))
    (hR : ∀ z, (R z : OnePoint ℂ) = b65y_radial (b65y_sample γ N) N z)
    (hA : ∀ z, (A z : OnePoint ℂ) = H (1, z))
    (x : b6t_punctured (γ 0)) :
    (∃ K : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ K (t, z))) ∧
      (∀ z, K (0, z) = b65y_radial (b65y_sample γ N) N z) ∧
      (∀ z, K (1, z) = H (1, z)) ∧
      (∀ t j, K (t, b6_branch (γ 0) j) = b6_branch (γ 1) j)) ∧
    ∃ β : Path (R x) (A x), ∀ η : FundamentalGroup (b6t_punctured (γ 0)) x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (FundamentalGroup.map ⟨R, R.continuous⟩ x η) =
        FundamentalGroup.map ⟨A, A.continuous⟩ x η := by
  obtain ⟨K, hb, hz, ho, hm⟩ := rtc_finite_comparison γ hγ H hH h0 hmarks N hN hsteps harcs
  refine ⟨⟨K, hb, hz, ho, hm⟩, ?_⟩
  exact rtc_homotopy_action
    (rtc_restrict_comparison (γ 0) (γ 1) R A K hb
      (fun z ↦ (hz z).trans (hR z).symm)
      (fun z ↦ (ho z).trans (hA z).symm) hm) x

theorem rtc_avoidance_aux (c : Fin 10 → ℂ) (r : ℝ) (hr : 0 < r)
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (hconv : Convex ℝ V)
    (hchart : V ⊆ b6_chart)
    (hK : {z | ∀ i, dist (z i) (c i) ≤ r} ⊆ V)
    {a b : b6_chart} (α : Path a b)
    (ha : ¬ ∀ i, dist (a.val i) (c i) ≤ r)
    (hb : ¬ ∀ i, dist (b.val i) (c i) ≤ r) :
    ∃ α' : Path a b, α.Homotopic α' ∧
      ∀ t, ¬ ∀ i, dist ((α' t).val i) (c i) ≤ r := by
  have hball : Metric.closedBall c r ⊆ V := by
    intro z hz
    apply hK
    exact (dist_pi_le_iff hr.le).mp hz
  have ha' : r < ‖a.val - c‖ := by
    apply lt_of_not_ge
    intro h
    apply ha
    exact (dist_pi_le_iff hr.le).mp (by simpa only [dist_eq_norm] using h)
  have hb' : r < ‖b.val - c‖ := by
    apply lt_of_not_ge
    intro h
    apply hb
    exact (dist_pi_le_iff hr.le).mp (by simpa only [dist_eq_norm] using h)
  obtain ⟨β, hαβ, hβ⟩ := rtc_buffered_ball_avoidance b6_chart b6_chart_open
    c r hr V hV hchart hball α ha' hb'
  refine ⟨β, hαβ, ?_⟩
  intro t ht
  have h := (dist_pi_le_iff hr.le).mpr ht
  rw [dist_eq_norm] at h
  exact (hβ t).not_ge h

theorem rtc_normalized_tracks_aux (P : C(unitInterval, Fin 12 → ℂ))
    (hinj : ∀ t, Function.Injective (P t))
    (c : Fin 10 → ℂ)
    (hend : ∀ k : Fin 10,
      (P 1 (k.castAdd 2) - P 1 10) / (P 1 11 - P 1 10) = c k) :
    ∃ γ : C(unitInterval, Fin 10 → ℂ),
      (∀ t k, γ t k = (P t (k.castAdd 2) - P t 10) / (P t 11 - P t 10)) ∧
      (∀ t, γ t ∈ b6_chart) ∧ γ 1 = c := by
  have hd (t : unitInterval) : P t 11 - P t 10 ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ (by decide : (11 : Fin 12) ≠ 10) (hinj t h))
  let γ : C(unitInterval, Fin 10 → ℂ) :=
    ⟨fun t k ↦ (P t (k.castAdd 2) - P t 10) / (P t 11 - P t 10),
      continuous_pi fun k ↦
        ((continuous_apply _).comp P.continuous |>.sub
          ((continuous_apply _).comp P.continuous)).div
          (((continuous_apply _).comp P.continuous).sub
            ((continuous_apply _).comp P.continuous)) hd⟩
  refine ⟨γ, fun _ _ ↦ rfl, ?_, ?_⟩
  · intro t
    rw [b6_chart_coordinates]
    refine ⟨?_, ?_⟩
    · intro i j hij
      have h := (div_left_inj' (hd t)).mp hij
      have he := hinj t ((sub_left_inj).mp h)
      exact Fin.ext (congrArg (fun k : Fin 12 ↦ k.val) he)
    · intro k
      constructor
      · intro h
        have he := hinj t (sub_eq_zero.mp ((div_eq_zero_iff).mp h |>.resolve_right (hd t)))
        have hv := congrArg Fin.val he
        simp only [Fin.val_castAdd, Fin.reduceFinMk] at hv
        norm_num at hv
        omega
      · intro h
        have he := hinj t ((sub_left_inj).mp ((div_eq_one_iff_eq (hd t)).mp h))
        have hv := congrArg Fin.val he
        simp only [Fin.val_castAdd, Fin.reduceFinMk] at hv
        norm_num at hv
        omega
  · ext k
    exact hend k

theorem rtc_homotopic_transport_aux {a b : b6_chart} (α α' : Path a b) (hα : α.Homotopic α')
    (H G : C(unitInterval × OnePoint ℂ, OnePoint ℂ))
    (hH : ∀ t, Function.Bijective (fun z ↦ H (t, z)))
    (hG : ∀ t, Function.Bijective (fun z ↦ G (t, z)))
    (hH0 : ∀ z, H (0, z) = z) (hG0 : ∀ z, G (0, z) = z)
    (hHm : ∀ t j, H (t, b6_branch a.val j) = b6_branch (α t).val j)
    (hGm : ∀ t j, G (t, b6_branch a.val j) = b6_branch (α' t).val j)
    (A B : b6t_punctured a.val ≃ₜ b6t_punctured b.val)
    (hA : ∀ z, (A z : OnePoint ℂ) = H (1, z))
    (hB : ∀ z, (B z : OnePoint ℂ) = G (1, z))
    (x : b6t_punctured a.val) :
    ∃ β : Path (A x) (B x), ∀ η : FundamentalGroup (b6t_punctured a.val) x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β
        (FundamentalGroup.map ⟨A, A.continuous⟩ x η) =
        FundamentalGroup.map ⟨B, B.continuous⟩ x η := by
  obtain ⟨K, hKb, hK0, hK1, hKm⟩ := rtc_configuration_comparison α α' hα
    H G hH hG hH0 hG0 hHm hGm
  exact rtc_homotopy_action
    (rtc_restrict_comparison a.val b.val A B K hKb
      (fun z ↦ (hK0 z).trans (hA z).symm)
      (fun z ↦ (hK1 z).trans (hB z).symm) hKm) x

end HodgeLean.Foundations.Program
