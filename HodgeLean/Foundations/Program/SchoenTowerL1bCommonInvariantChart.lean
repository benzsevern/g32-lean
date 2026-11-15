import HodgeLean.Foundations.Program.SchoenTowerL1bCommonBranchContractions
import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedInvariantCharts
import HodgeLean.Foundations.Program.SchoenTowerL1aChartParameterAction

/-! # Invariant sections on the common two-branch chart

The chart uses one separating curve parameter and both actual branch contractions.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Two distinct branch points have simultaneous insertion contractions on one
retained affine quotient neighborhood containing the specified ordered point. -/
theorem s2v_l1b_common_two_branch_invariant_chart
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : Fin 2 → ComplexPoint Z) (hb : b 0 ≠ b 1)
    (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ O : B.left.affineOpens, x.underlying ∈ γ.left ⁻¹ᵁ O.1 ∧
      let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
      letI : IsAffine V.left := O.2.preimage γ.left
      ∃ (z : Fin (h + 1) → Γ(V.left, ⊤)) (c : Fin 2 → Γ(Spec ↧ℂ, ⊤)),
        c 0 ≠ c 1 ∧ (MvPolynomial.eval₂Hom V.hom.appTop.hom z).Etale ∧
        ∃ ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V),
        (∀ τ, ρ τ ≫ ComplexPoint.openInclusion (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) =
          ComplexPoint.openInclusion (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) ≫
            s2_permute Z (h + 1) τ) ∧
        Function.Injective (γ.left ∣_ O.1).appTop.hom ∧
        (∀ s : Γ(V.left, ⊤), s ∈ Set.range (γ.left ∣_ O.1).appTop.hom ↔
          ∀ τ, (ρ τ).left.appTop.hom s = s) ∧
        (∀ τ i, (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i)) ∧
        (∀ k, ((s2c_branchIdeal Z B h γ (b k)).comap O.1.ι).ideal
          ⟨⊤, @isAffineOpen_top _ O.2⟩ =
          (Ideal.span {z 0 - V.hom.appTop.hom (c k)}).comap (γ.left ∣_ O.1).appTop.hom) ∧
        ∀ hx : x.underlying ∈ γ.left ⁻¹ᵁ O.1,
        let p := ComplexPoint.asOpenPoint (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hx
        ∀ i j, Point.map (g3_proj Z (h + 1) i) x ≠ Point.map (g3_proj Z (h + 1) j) x →
          Point.evaluate ⊤ (z i) p ≠ Point.evaluate ⊤ (z j) p := by
  classical
  let t : Fin (h + 3) → ComplexPoint Z :=
    Fin.cases (b 0) (Fin.cases (b 1) (fun i => Point.map (g3_proj Z (h + 1) i) x))
  obtain ⟨A, hA, a, y, zA, ha, hy, hzEt, hzI, hzsep⟩ :=
    s2v_l1b_simultaneous_curve_parameter Z hdim (h + 2) t
  letI : IsAffine A.left := hA
  letI : IsOpenImmersion a.left := ha
  let yp : ComplexPoint (g3_power A (h + 1)) := s2_lift (h + 1) (fun i => y i.succ.succ)
  have hyp : Point.map (s2_powerMap a (h + 1)) yp = x :=
    s2v_l1a_ordered_point_lift a (h + 1) x (fun i => y i.succ.succ)
      (fun i => hy i.succ.succ)
  obtain ⟨O, hx, j, hj, hjfac⟩ :=
    s2v_l1a_compatible_curve_chart A Z B h a γ hγinv hγ x yp hyp
  let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
  letI : IsAffine V.left := O.2.preimage γ.left
  letI : IsAffine (g3_power A (h + 1)).left := s2v_l1a_ordered_power_affine A (h + 1)
  letI : IsOpenImmersion j.left := hj
  let bk (k : Fin 2) : Fin (h + 3) := ⟨k.val, by omega⟩
  have hbk (k : Fin 2) : t (bk k) = b k := by
    fin_cases k <;> rfl
  let c (k : Fin 2) := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    (Point.evaluate ⊤ zA (y (bk k)))
  let z (i : Fin (h + 1)) := (j ≫ g3_proj A (h + 1) i).left.appTop.hom zA
  have hI (k : Fin 2) : ((b k).left.ker.comap a.left).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {zA - A.hom.appTop.hom (c k)} := by
    have H := hzI (bk k)
    rw [hbk] at H
    exact H
  have hbranch := s2v_l1b_common_chart_branch_contractions A Z B h a γ O j hjfac b c zA hI
  have hc : c 0 ≠ c 1 := by
    intro H
    have Hv := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom v) H
    simp only [c, Iso.inv_hom_id_apply] at Hv
    exact hzsep (bk 0) (bk 1) (by rw [hbk, hbk]; exact hb) Hv
  have hjEt : j.left.appTop.hom.Etale :=
    HasRingHomProperty.appTop (P := @Etale) j.left inferInstance
  have heval : MvPolynomial.eval₂Hom V.hom.appTop.hom z =
      j.left.appTop.hom.comp
        (MvPolynomial.eval₂Hom (g3_power A (h + 1)).hom.appTop.hom
          (fun i => (g3_proj A (h + 1) i).left.appTop.hom zA)) := by
    apply MvPolynomial.ringHom_ext
    · intro c'
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      have H := congrArg (fun f : V.left ⟶ Spec ↧ℂ => f.appTop.hom c') (Over.w j)
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using H.symm
    · intro i
      rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change (j ≫ g3_proj A (h + 1) i).left.appTop zA = _
      rw [Over.comp_left, Scheme.Hom.comp_appTop]
      rfl
  have hEt : (MvPolynomial.eval₂Hom V.hom.appTop.hom z).Etale := by
    rw [heval]
    exact s2v_l1a_etale_ringHom_comp _ _
      (s2v_l1a_ordered_parameter_etale A zA hzEt (h + 1)) hjEt
  let X := g3_power Z (h + 1)
  let V₀ := γ.left ⁻¹ᵁ O.1
  let v : V ⟶ X := ComplexPoint.openInclusion X V₀
  have hpre (τ : Equiv.Perm (Fin (h + 1))) :
      V₀ ≤ (s2_permute Z (h + 1) τ).left ⁻¹ᵁ V₀ := by
    change γ.left ⁻¹ᵁ O.1 ≤ (s2_permute Z (h + 1) τ).left ⁻¹ᵁ (γ.left ⁻¹ᵁ O.1)
    rw [← Scheme.Hom.comp_preimage]
    rw [show (s2_permute Z (h + 1) τ).left ≫ γ.left = γ.left from
      congrArg (fun f : X ⟶ B => f.left) (hγinv τ)]
  let r (τ : Equiv.Perm (Fin (h + 1))) :=
    (s2_permute Z (h + 1) τ).left.resLE V₀ V₀ (hpre τ)
  have hr (τ : Equiv.Perm (Fin (h + 1))) :
      r τ ≫ V₀.ι = V₀.ι ≫ (s2_permute Z (h + 1) τ).left :=
    Scheme.Hom.resLE_comp_ι _ _
  let ρ (τ : Equiv.Perm (Fin (h + 1))) : V ⟶ V := Over.homMk (r τ) (by
    change r τ ≫ (V₀.ι ≫ X.hom) = V₀.ι ≫ X.hom
    rw [← Category.assoc, hr, Category.assoc, Over.w])
  have hρv (τ : Equiv.Perm (Fin (h + 1))) :
      ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ := by
    apply Over.OverMorphism.ext
    exact hr τ
  obtain ⟨hinj, himage⟩ := s2v_l1a_retained_affine_invariants Z B h γ hγinv hγ O
  have Hinv := s2v_l1a_restricted_lift_invariant_image γ.left
    (fun τ => (s2_permute Z (h + 1) τ).left)
    (fun τ => congrArg (fun f : X ⟶ B => f.left) (hγinv τ)) O.1 hinj himage r hr
  let ac (i : Fin (h + 1)) := j ≫ g3_proj A (h + 1) i
  have hac (i : Fin (h + 1)) : ac i ≫ a = v ≫ g3_proj Z (h + 1) i := by
    have H : s2_powerMap a (h + 1) ≫ g3_proj Z (h + 1) i =
        g3_proj A (h + 1) i ≫ a := s2_check_lift_proj (h + 1) _ i
    change (j ≫ g3_proj A (h + 1) i) ≫ a = _
    rw [Category.assoc, ← H, ← Category.assoc, hjfac]
  letI : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  letI : Mono v := Over.mono_of_mono_left v
  letI : Mono a := Over.mono_of_mono_left a
  have hcov (τ : Equiv.Perm (Fin (h + 1))) (i : Fin (h + 1)) :
      (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i) := by
    have H := s2v_l1a_chart_parameter_action V A Z (h + 1) a v ρ hρv ac hac zA τ⁻¹ i
    change (ρ ((τ⁻¹)⁻¹)).left.appTop.hom (z i) = z (τ⁻¹ i) at H
    simpa only [inv_inv] using H
  refine ⟨O, hx, z, c, hc, hEt, ρ, hρv, Hinv.1, Hinv.2, hcov, hbranch, ?_⟩
  intro hx'
  let p := ComplexPoint.asOpenPoint X V₀ x hx'
  have hp : Point.map v p = x := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X V₀ x hx'
  have hsep : ∀ i j, Point.map (v ≫ g3_proj Z (h + 1) i) p ≠
      Point.map (v ≫ g3_proj Z (h + 1) j) p →
      Point.evaluate ⊤ (z i) p ≠ Point.evaluate ⊤ (z j) p := by
    have hay (i : Fin (h + 1)) : Point.map (ac i) p = y i.succ.succ := by
      apply (cancel_mono a).mp
      change (p ≫ ac i) ≫ a = y i.succ.succ ≫ a
      rw [Category.assoc, hac, ← Category.assoc]
      change Point.map (g3_proj Z (h + 1) i) (Point.map v p) = Point.map a (y i.succ.succ)
      rw [hp, hy]
      rfl
    have heval (i : Fin (h + 1)) : Point.evaluate ⊤ (z i) p =
        Point.evaluate ⊤ zA (y i.succ.succ) := by
      change Point.evaluate ⊤ ((ac i).left.appTop zA) p = _
      have H := Point.evaluate_map (ac i) ⊤ zA p
      rw [hay] at H
      simpa only [TopologicalSpace.Opens.map_top, Scheme.Hom.appTop] using H.symm
    intro i k hik
    rw [heval, heval]
    apply hzsep i.succ.succ k.succ.succ
    intro H
    apply hik
    change Point.map (g3_proj Z (h + 1) i) x = Point.map (g3_proj Z (h + 1) k) x at H
    change (p ≫ v) ≫ g3_proj Z (h + 1) i = (p ≫ v) ≫ g3_proj Z (h + 1) k
    rw [show p ≫ v = x from hp]
    exact H
  change ∀ i j, Point.map (g3_proj Z (h + 1) i) x ≠ Point.map (g3_proj Z (h + 1) j) x →
    Point.evaluate ⊤ (z i) p ≠ Point.evaluate ⊤ (z j) p
  intro i k hik
  apply hsep i k
  change p ≫ (v ≫ g3_proj Z (h + 1) i) ≠ p ≫ (v ≫ g3_proj Z (h + 1) k)
  rw [← Category.assoc, ← Category.assoc, show p ≫ v = x from hp]
  exact hik


end HodgeLean.Foundations.Program
