import HodgeLean.Foundations.Program.PrymFamilyExistsDefs

/-! # The Prym family `P`: proof obligations

One auxiliary statement for each public statement of `PrymFamilyExists.lean`, with its body.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Papers
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.AppellHumbert
open TopologicalSpace
open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63gP_fiber_positive_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s₀ : V) {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s₀))
    (t : V) :
    let X := b63g5_fiber b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ B t
    ∀ h : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X.X) X.pol),
      PolarizationPositive (finiteBetti_abelian X.X) (spec_bettiDeRhamIso_abelian X.X)
        (hodgeDecomposition_of_abelian X.X) (torusCohomology_cupProductOf X.X) h := by
  intro X
  let _ : Module.Free ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Free.of_basis B
  let _ : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s₀) := Module.Finite.of_basis B
  have W := b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s₀ t
  have hsq := b63g2_operator_sq b C hC V hV s₀ (hG s₀)
  have hφ := b63g2_operator_filtration b C hC V hV hG P hP s₀ t
  have hX : X = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
  rw [hX]
  unfold b63g2_sixfold
  intro h
  let _ := b5_groupObj _ _ W.1 _ W.2
  let _ : IsIntegral (b5_model _ _ W.1 (b63e_singularQ b C hC V hV s₀ (P s₀) (Q s₀))).left :=
    b5_integral_aux _ _ W.1 _ W.2
  let _ := b5_smooth_aux _ _ W.1 _ W.2
  let _ := b5_projective_aux _ _ W.1 _ W.2
  exact b63g4_abelian_positive _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)

theorem b63gP_family_of_cover_aux (U : Type) [TopologicalSpace U] [MulAction b4b_Group U]
    (π : U → b6t_punctured mr_base) (hπ : IsQuotientCoveringMap π b4b_Group)
    (y₀ : b6t_punctured mr_base) (u₀ : π ⁻¹' {y₀})
    (γ : Fin 13 → FundamentalGroup (b6t_punctured mr_base) y₀)
    (hγ : ∀ i, mr_IsLoop mr_base y₀ i (γ i))
    (hroot : ∀ i, hπ.fundamentalGroupToMulOpposite u₀ (γ i) = MulOpposite.op (b4b_root i))
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [MulAction b4b_Group C] [FaithfulSMul b4b_Group C] (f : C → OnePoint ℂ) (ι : U → C)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hgal : b4_IsGaloisCover b4b_Group f)
    (hsurj : Function.Surjective f)
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (hι : Continuous ι) (hproj : ∀ u, f (ι u) = π u)
    (hequiv : ∀ (g : b4b_Group) (u : U), ι (g • u) = g • ι u)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch mr_base) → MulAction.stabilizer b4b_Group x = ⊥)
    (hrot₀ : ∀ j, ∃ x, f x = b6_branch mr_base j ∧ b4_IsRotGen ℂ x (b4b_root j))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre mr_base C V hV t ↦ g • x))
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection mr_base C f V hV t))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ
      (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre mr_base C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s₀ : V) (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC V hV s₀)) :
    ∃ F : g32h_PrymFamily, (∃ j : V ≃ F.S, ∀ t : V,
      F.tuple (j t) = b63g5_tuple ∧
        F.fiber (j t) = b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀
          Q hQ P hP s₀ B t) ∧ Nonempty F.S := by
  let X : V → g32t_Sixfold := fun t ↦ b63g5_fiber mr_base C hC V hV hG mr_base_mem_chart f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t
  have key : ∀ t : V, (dim (X t).X.left : ℤ) = g32h_multCW b63g5_tuple ∧
      (((g32h_h10 (X t) : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h01 (X t) : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple) ∨
        ((g32h_h01 (X t) : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h10 (X t) : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple)) ∧
      IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol) ∧
      (letI := (torusCohomology_cupProductOf (X t).X).finite
       IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol)
        (X t).W.J) := by
    intro t
    have hb : mr_base ∈ b6_chart := mr_base_mem_chart
    let _ : Module.Free ℤ (b63l_parameterLattice mr_base C hC V hV s₀) := Module.Free.of_basis B
    let _ : Module.Finite ℤ (b63l_parameterLattice mr_base C hC V hV s₀) := Module.Finite.of_basis B
    have W := b63e_weight_one_riemann mr_base C hC V hV hG hb f hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ t
    have hsq := b63g2_operator_sq mr_base C hC V hV s₀ (hG s₀)
    have hφ := b63g2_operator_filtration mr_base C hC V hV hG P hP s₀ t
    have hX : X t = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
    obtain ⟨hgal', hs', hfree'⟩ := b63g5_fibre_galois mr_base hb C f hgal hsurj hfree V hV t
    have hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch mr_base j ∧
        MulAction.stabilizer b4b_Group x ≠ ⊥ := by
      intro j
      obtain ⟨x, hx, hrx⟩ := hrot₀ j
      refine ⟨x, hx, fun h ↦ ?_⟩
      have hmem : b4b_root j ∈ MulAction.stabilizer b4b_Group x := hrx.1
      rw [h, Subgroup.mem_bot] at hmem
      have h3 := b63_root_order j
      rw [hmem, orderOf_one] at h3
      split_ifs at h3 <;> omega
    have hbranch := b63g5_fibre_branch mr_base hb C f hgal hsurj hfree hstab V hV t (hk t) (hG t)
    have hrot := b63g5_fibre_rot U π hπ y₀ u₀ γ hγ hroot C f ι hι hproj hequiv hgal hsurj hfree
      V hV t (hk t) (hG t)
    have hE := b63g2_eigen_rank mr_base C hC V hV hG P hP s₀ t hb f (hk t) hs' hgal' hbranch hrot
    have h10 : g32h_h10 (X t) = 3 := by
      have h := (b63g2_sixfold_h10 _ _ W.1 _ W.2 _ hsq hφ).trans
        (b63g2_weil_h10 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
      rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
        norm_num] at h
      rw [hX]
      exact h.trans hE.2
    have h01 : g32h_h01 (X t) = 3 := by
      have h := (b63g2_sixfold_h01 _ _ W.1 _ W.2 _ hsq hφ).trans
        (b63g2_weil_h01 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
      rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
        norm_num] at h
      rw [hX]
      exact h.trans hE.1
    have hdim : (dim (X t).X.left : ℤ) = 6 := by
      let _ : IsIntegral (b5_model _ _ W.1
          (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left :=
        b5_integral_aux _ _ W.1 _ W.2
      have h := b63g_model_finrank _ _ W.1 _ W.2
      rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
      rw [hX]
      change (dim (b5_model _ _ W.1 (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left : ℤ)
        = 6
      omega
    have hN : g32h_Nielsen b63g5_tuple := b63d_root_nielsen
    refine ⟨?_, Or.inl ?_, ?_, ?_⟩
    · rw [hdim, g32h_multCW_of_nielsen _ hN]
    · rw [h10, h01, g32h_holoCW_of_nielsen _ hN, g32h_multCW_of_nielsen _ hN]
      norm_num
    · have h :=
        letI := b5_groupObj _ _ W.1 _ W.2
        letI : IsIntegral (b5_model _ _ W.1
            (b63e_singularQ mr_base C hC V hV s₀ (P s₀) (Q s₀))).left :=
          b5_integral_aux _ _ W.1 _ W.2
        letI := b5_smooth_aux _ _ W.1 _ W.2
        letI := b5_projective_aux _ _ W.1 _ W.2
        b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)
      rw [hX]
      unfold b63g2_sixfold
      exact h
    · rw [hX]
      exact b63g2_sixfold_rosati _ _ W.1 _ W.2 _ hsq hφ
        (b63g2_operator_skew mr_base C hC V hV s₀ (hG s₀) (P s₀) (hP s₀) (Q s₀) (hQ s₀))
  exact ⟨{ S := V
           tuple := fun _ ↦ b63g5_tuple
           tuple_nielsen := fun _ ↦ b63d_root_nielsen
           fiber := X
           dim_eq := fun t ↦ (key t).1
           hodge := fun t ↦ (key t).2.1
           nondegenerate := fun t ↦ (key t).2.2.1
           rosati := fun t ↦ (key t).2.2.2
           positive := fun t ↦ b63gP_fiber_positive_aux mr_base C hC V hV hG mr_base_mem_chart f
             hf hsurj hk Q₀ hQ₀ Q hQ P hP s₀ B t _ }, ⟨Equiv.refl _, fun _ ↦ ⟨rfl, rfl⟩⟩, ⟨s₀⟩⟩

theorem b63gP_exists_aux :
    ∃ F : g32h_PrymFamily, b63gP_IsMarked F ∧ Nonempty F.S := by
  have hb : mr_base ∈ b6_chart := mr_base_mem_chart
  have hγ : ∀ i, mr_IsLoop mr_base b63gP_basePoint i (b63gP_loops i) := fun i ↦
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  obtain ⟨U, _, _, _, π, hπ, u₀, hroot, C, _, _, _, _, _, _, _, _, f, ι, hf, hgal, hsurj, hact,
    hι, hrange, hproj, hequiv, hfree, hrot₀⟩ := mr_rootCover b63gP_basePoint b63gP_loops hγ
  have hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x) := fun g ↦ (hact g).continuous
  have hS := fun t : b6t_polydisc mr_base ↦
    b63g5_fibre_structure mr_base hb C f hf hgal hact (b6t_polydisc mr_base) Set.Subset.rfl t
  choose cs ms hk hG using hS
  obtain ⟨Q₀, hQ₀⟩ := b3_exists_intersectionForm (E := ℂ) (C := C) (Module.finrank_self ℂ)
  choose Q hQ using fun t : b6t_polydisc mr_base ↦
    b3_exists_intersectionForm (E := ℂ)
      (C := b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)
      (Module.finrank_self ℂ)
  choose P hP using fun t : b6t_polydisc mr_base ↦ b6m_period_comparison
    (b63l_parameterFibre mr_base C (b6t_polydisc mr_base) Set.Subset.rfl t)
  have hstab : ∀ j : Fin 13, ∃ x, f x = b6_branch mr_base j ∧
      MulAction.stabilizer b4b_Group x ≠ ⊥ := by
    intro j
    obtain ⟨x, hx, hrx⟩ := hrot₀ j
    refine ⟨x, hx, fun h ↦ ?_⟩
    have hmem : b4b_root j ∈ MulAction.stabilizer b4b_Group x := hrx.1
    rw [h, Subgroup.mem_bot] at hmem
    have h3 := b63_root_order j
    rw [hmem, orderOf_one] at h3
    split_ifs at h3 <;> omega
  have hgal' := (b63g5_fibre_galois mr_base hb C f hgal hsurj hfree (b6t_polydisc mr_base)
    Set.Subset.rfl b63gP_s₀)
  have B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice mr_base C hC (b6t_polydisc mr_base)
      Set.Subset.rfl b63gP_s₀) :=
    (b63d_lattice_rank mr_base C hC (b6t_polydisc mr_base) Set.Subset.rfl b63gP_s₀
      (hG b63gP_s₀) hb f (hk b63gP_s₀) hgal'.2.1 hgal'.1
      (b63g5_fibre_branch mr_base hb C f hgal hsurj hfree hstab (b6t_polydisc mr_base)
        Set.Subset.rfl b63gP_s₀ (hk b63gP_s₀) (hG b63gP_s₀))
      (b63g5_fibre_rot U π hπ b63gP_basePoint u₀ b63gP_loops hγ hroot C f ι hι.continuous hproj
        hequiv hgal hsurj hfree (b6t_polydisc mr_base) Set.Subset.rfl b63gP_s₀ (hk b63gP_s₀)
        (hG b63gP_s₀))).1.some
  obtain ⟨F, ⟨j, hj⟩, hne⟩ := b63gP_family_of_cover_aux U π hπ b63gP_basePoint u₀ b63gP_loops hγ
    hroot C f ι hf hgal hsurj hC hι.continuous hproj hequiv hfree hrot₀ (b6t_polydisc mr_base)
    Set.Subset.rfl hG hk Q₀ hQ₀ Q hQ (fun t ↦ (P t).toLinearMap) hP b63gP_s₀ B
  exact ⟨F, ⟨U, inferInstance, inferInstance, inferInstance, π, hπ, u₀, hroot, C, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, f, ι, hf, hsurj, hact, hgal, hι, hrange, hproj, hequiv, hfree, hrot₀, cs, ms,
    hG, hk, Q₀, hQ₀, Q, hQ, fun t ↦ (P t).toLinearMap, hP, B, j, hj⟩, hne⟩

theorem b63gP_family_isMarked_aux :
    b63gP_IsMarked b63gP_family ∧ Nonempty b63gP_family.S :=
  @Classical.epsilon_spec g32h_PrymFamily (fun F ↦ b63gP_IsMarked F ∧ Nonempty F.S)
    b63gP_exists_aux

theorem b63gP_family_tuple_aux (s : b63gP_family.S) :
    b63gP_family.tuple s = b63g5_tuple := by
  obtain ⟨_, _, _, _, _, _, _, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -,
    _, _, _, _, _, _, _, _, _, _, _, j, hj⟩ := b63gP_family_isMarked_aux.1
  simpa using (hj (j.symm s)).1

theorem b63gP_theoremA_aux (F : g32m_UniversalFamily)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32a_theoremA F b63gP_family h46 R hpol spread transport A W pol

theorem b63gP_theoremA_of_transport_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gP_theoremA_aux F h46 R hpol
    (hk7_spread F hF b63gP_family h46 R fun p hp h => by
      have hp' : g32t_KIsog (b63gP_family.fiber p.2) (F.univ p.1) := by rw [hF]; exact hp
      have := (transport _ _ hp').1 h
      rwa [hF] at this) transport A W pol

theorem b63gP_theoremA_of_reverse_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  g32n_theoremA_of_premises
    { F, P := b63gP_family, h46, R, hpol, reverse
      spread := hk7_spread_of_members F hF b63gP_family h46 R hpol reverse } A W pol

theorem b63gP_theoremA_of_qinv_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 b63gP_family) (R : g32r_PeriodMap F b63gP_family)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized b63gP_family s))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  qinv_g32_theoremA_of_premises
    { F, P := b63gP_family, h46, R, hpol, qinv
      spread := hk7_spread_of_witness F hF b63gP_family h46 R
        fun _ _ f hf hi => qinv _ _ f hf hi } A W pol

end HodgeLean.Foundations.Program
