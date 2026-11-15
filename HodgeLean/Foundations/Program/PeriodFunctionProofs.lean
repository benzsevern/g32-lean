import HodgeLean.Foundations.Program.PeriodFunctionDefs
import HodgeLean.Foundations.Program.PrymFamilyCentreNaturality

/-! # B6-4c: period-function obligations -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers Filter Set
open scoped Manifold ContDiff TensorProduct Topology
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b64c_marked_coord_analytic_aux (M : Type*) [AddCommGroup M] {ι κ : Type} [Fintype ι]
    (B : Module.Basis ι ℤ M) (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (c : κ → (Fin 10 → ℂ) → ι → ℂ)
    (hc : ∀ i, AnalyticOnNhd ℂ (c i) W) :
    ∀ i p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr
      (b64b_complexMarking M m (b63e_coordVector B (c i t))) p) W := by
  classical
  intro i p
  have hv (t : Fin 10 → ℂ) :
      b60c_eigenBasis.repr
        (b64b_complexMarking M m (b63e_coordVector B (c i t))) p =
      ∑ j, c i t j * b60c_eigenBasis.repr
        (b64b_complexMarking M m ((1 : ℂ) ⊗ₜ[ℤ] B j)) p := by
    simp only [b63e_coordVector, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [show c i t j ⊗ₜ[ℤ] B j = c i t j • ((1 : ℂ) ⊗ₜ[ℤ] B j) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [hv]
  refine Finset.analyticOnNhd_fun_sum _ fun j _ => ?_
  refine AnalyticOnNhd.mul (fun t ht => ?_) analyticOnNhd_const
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt _).comp
    (hc i t ht)

theorem b64c_period_analyticOnNhd_aux (M : Type*) [AddCommGroup M] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℤ M) (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (V : Set (Fin 10 → ℂ)) (hV : IsOpen V) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hframe : ∀ t₀ ∈ V, ∃ W : Set (Fin 10 → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ V ∧
      ∃ n : ℕ, ∃ c : Fin n → (Fin 10 → ℂ) → ι → ℂ, (∀ i, AnalyticOnNhd ℂ (c i) W) ∧
        ∀ t ∈ W, Submodule.span ℂ (Set.range fun i => b63e_coordVector B (c i t)) = G t)
    (hchart : ∀ t ∈ V, ∃ z : Fin 9 → ℂ, b64c_markedF M m G t = b60_F z) :
    AnalyticOnNhd ℂ (b64c_period M m V G) V := by
  intro t₀ ht₀
  obtain ⟨W, hWo, htW, hWV, n, c, hc, hspan⟩ := hframe t₀ ht₀
  let u : (Fin 10 → ℂ) → Fin n → ℂ ⊗[ℤ] b60_Lattice := fun t i =>
    b64b_complexMarking M m (b63e_coordVector B (c i t))
  have hu : ∀ k p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (u t k) p) W :=
    b64c_marked_coord_analytic_aux M B m W c hc
  have hspan' : ∀ t ∈ W, Submodule.span ℂ (Set.range (u t)) = b64c_markedF M m G t := by
    intro t ht
    rw [b64c_markedF, ← hspan t ht, Submodule.map_span, ← Set.range_comp]
    rfl
  have hF : ∀ t ∈ W, ∃ z : Fin 9 → ℂ, b64c_markedF M m G t = b60_F z :=
    fun t ht => hchart t (hWV ht)
  have h := b64_coordOf_analyticOnNhd u (b64c_markedF M m G) W hWo hu hspan' hF t₀ htW
  refine h.congr ?_
  filter_upwards [hV.mem_nhds ht₀] with t ht
  simp [b64c_period, ht]

theorem b64c_period_filtration_aux (M : Type*) [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : ∀ t ∈ V, b2_IsRiemannForm M (G t) Q)
    (hdim : ∀ t ∈ V, Module.finrank ℂ (G t) = 6)
    (hneg : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    ∀ t ∈ V, b60_F (b64c_period M m V G t) = b64c_markedF M m G t := by
  intro t ht
  obtain ⟨hR', hdim', hneg', hpos'⟩ :=
    b64b_marking_riemann M Q A m hA hQ (G t) (hR t ht) (hdim t ht) (hneg t ht) (hpos t ht)
  obtain ⟨τ, hτ⟩ := b60c_fixed_filtration_chart _ hdim' hneg' hpos' hR'
  have hτ' : b64c_markedF M m G t = b60_F τ := hτ
  rw [show b64c_period M m V G t = b64_coordOf (b64c_markedF M m G t) by
    simp [b64c_period, ht], hτ', b64_coordOf_eq]

theorem b64c_period_mapsTo_aux (M : Type*) [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (V : Set (Fin 10 → ℂ)) (G : (Fin 10 → ℂ) → Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : ∀ t ∈ V, b2_IsRiemannForm M (G t) Q)
    (hdim : ∀ t ∈ V, Module.finrank ℂ (G t) = 6)
    (hneg : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : ∀ t ∈ V, Module.finrank ℂ ↥(G t ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    MapsTo (b64c_period M m V G) V (g32m_Domain : Set (Fin 9 → ℂ)) := by
  intro t ht
  obtain ⟨hR', hdim', hneg', hpos'⟩ :=
    b64b_marking_riemann M Q A m hA hQ (G t) (hR t ht) (hdim t ht) (hneg t ht) (hpos t ht)
  obtain ⟨τ, hτ⟩ := b60c_fixed_filtration_chart _ hdim' hneg' hpos' hR'
  have hτ' : b64c_markedF M m G t = b60_F τ := hτ
  rw [show b64c_period M m V G t = b64_coordOf (b64c_markedF M m G t) by
    simp [b64c_period, ht], hτ', b64_coordOf_eq]
  exact τ.2

theorem b64c_transported_finrank_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s t : V) :
    Module.finrank ℂ (b63e_transportedF b C hC V hV P s t) = 6 := by
  obtain ⟨E, -, hE⟩ := b63e_lattice_period_transport b C hC V hV hG P hP s t
  have hd := (b63d_dim_eq b C hC V hV t (hG t) hb f (hk t) (hsurj t) (hgal t) (hbranch t)
    (hrot t)).2.2
  let eC := E.baseChange ℤ ℂ (b63l_parameterLattice b C hC V hV s)
    (b63l_periodLattice (b63l_parameterFibre b C V hV t))
  rw [hE]
  change Module.finrank ℂ ↥((b63l_periodF _).comap eC.toLinearMap) = 6
  exact (Submodule.comap_equiv_self_of_inj_of_le (p := b63l_periodF _)
    eC.injective (by rw [LinearMap.range_eq_top.mpr eC.surjective]; exact le_top)).finrank_eq.trans
    hd

theorem b64c_transported_eigen_ranks_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val) (t : V) :
    Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (A.baseChange ℂ) (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
      Module.finrank ℂ ↥(b63e_transportedF b C hC V hV P s t ⊓
        Module.End.eigenspace (A.baseChange ℂ) (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
  obtain ⟨E, hEv, hE⟩ := b63e_lattice_period_transport b C hC V hV hG P hP s t
  let T := b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨t.val, hV t.property⟩)
  have hA' : ∀ x, (E (A x)).val =
      b63d_periodOperator (b63l_parameterFibre b C V hV t) (hG t) (E x).val := by
    intro x
    rw [hEv, hEv]
    change P t (T (A x).val) = b63d_periodOperator _ (hG t) (P t (T x.val))
    rw [hA x]
    simp only [b63d_operator, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_add, b63d_periodOperator]
    have hc : T (b63d_centre b C hC V hV s x.val) = b63d_centre b C hC V hV t (T x.val) :=
      b63d_centre_transport b C hC V hV t s x.val
    change P t (T x.val) + P t (T ((2 : ℕ) • b63d_centre b C hC V hV s x.val)) =
      P t (T x.val) + (2 : ℕ) • b4b_centreAct _ (hG t) (P t (T x.val))
    rw [map_nsmul, map_nsmul, hc,
      b63g2_period_centre b C hC V hV t (hG t) (P t) (hP t)]
  have hcw := b63d_chevalleyWeil_hodge b C hC V hV t (hG t) hb f (hk t) (hsurj t) (hgal t)
    (hbranch t) (hrot t)
  have hEC : (E.baseChange ℤ ℂ (b63l_parameterLattice b C hC V hV s)
      (b63l_periodLattice (b63l_parameterFibre b C V hV t))).toLinearMap =
      (E : b63l_parameterLattice b C hC V hV s →ₗ[ℤ]
        b63l_periodLattice (b63l_parameterFibre b C V hV t)).baseChange ℂ := rfl
  have key (z : ℂ) := b64b_period_eigen_rank _ (hG t) E A hA' z
  have hsub : b63e_transportedF b C hC V hV P s t =
      (b63l_periodF (b63l_parameterFibre b C V hV t)).comap
        (E.baseChange ℤ ℂ (b63l_parameterLattice b C hC V hV s)
          (b63l_periodLattice (b63l_parameterFibre b C V hV t))).toLinearMap :=
    hE.trans (congrArg (fun φ => (b63l_periodF (b63l_parameterFibre b C V hV t)).comap φ)
      hEC.symm)
  rw [hsub]
  have key' (z w : ℂ) (h : 1 + 2 * z = w) :
      Module.finrank ℂ ↥((b63l_periodF (b63l_parameterFibre b C V hV t)).comap
        (E.baseChange ℤ ℂ (b63l_parameterLattice b C hC V hV s)
          (b63l_periodLattice (b63l_parameterFibre b C V hV t))).toLinearMap ⊓
        Module.End.eigenspace (A.baseChange ℂ) w) =
      Module.finrank ℂ (b63d_eigenF (b63l_parameterFibre b C V hV t) (hG t) z) := by
    subst h
    exact key z
  exact ⟨(key' _ _ b64b_conjugate_root_eigenvalue).trans hcw.2.2.2,
    (key' _ _ b64b_root_eigenvalue).trans hcw.2.2.1⟩

theorem b64c_geomPeriod_chart_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [∀ t : V, T2Space (b63l_parameterFibre b C V hV t)]
    [∀ t : V, CompactSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, ConnectedSpace (b63l_parameterFibre b C V hV t)]
    [∀ t : V, FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hG : ∀ (t : V) (g : b4b_Group), ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    (hb : b ∈ b6_chart) [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (hs : Function.Surjective f)
    (hk : ∀ t : V, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hsurj : ∀ t : V, Function.Surjective (b63d_projection b C f V hV t))
    (hgal : ∀ t : V, b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : ∀ t : V,
      b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ (t : V) (i : Fin 13), ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q₀ : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (hQ₀ : b3_IsIntersectionForm ℂ Q₀)
    (Q : (t : V) → LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : ∀ t : V, b3_IsIntersectionForm ℂ (Q t))
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ (t : V) (γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t)),
      P t (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    (s : V) (A : b63l_parameterLattice b C hC V hV s →ₗ[ℤ] b63l_parameterLattice b C hC V hV s)
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV s x.val)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ b C hC V hV s (P s) (Q s)).baseChange ℚ x y) :
    ∀ t ∈ V, b64c_geomPeriod b C hC V hV P s m t ∈ g32m_Domain ∧
      b60_F (b64c_geomPeriod b C hC V hV P s m t) =
        b64c_markedF _ m (b64c_transportedFamily b C hC V hV P s) t := by
  obtain ⟨⟨B⟩, -⟩ := b63d_lattice_rank b C hC V hV s (hG s) hb f (hk s) (hsurj s) (hgal s)
    (hbranch s) (hrot s)
  have : Module.Free ℤ (b63l_parameterLattice b C hC V hV s) := Module.Free.of_basis B
  have : Module.Finite ℤ (b63l_parameterLattice b C hC V hV s) := Module.Finite.of_basis B
  have hfam (u : Fin 10 → ℂ) (hu : u ∈ V) :
      b64c_transportedFamily b C hC V hV P s u = b63e_transportedF b C hC V hV P s ⟨u, hu⟩ := by
    simp [b64c_transportedFamily, hu]
  have hR : ∀ u ∈ V, b2_IsRiemannForm _ (b64c_transportedFamily b C hC V hV P s u)
      (b63e_singularQ b C hC V hV s (P s) (Q s)) := by
    intro u hu
    rw [hfam u hu]
    exact (b63e_weight_one_riemann b C hC V hV hG hb f hf hs hk Q₀ hQ₀ Q hQ P hP s
      ⟨u, hu⟩).2
  have hdim : ∀ u ∈ V, Module.finrank ℂ (b64c_transportedFamily b C hC V hV P s u) = 6 := by
    intro u hu
    rw [hfam u hu]
    exact b64c_transported_finrank_aux b C hC V hV hG hb f hk hsurj hgal hbranch hrot P hP s
      ⟨u, hu⟩
  have hneg : ∀ u ∈ V, Module.finrank ℂ ↥(b64c_transportedFamily b C hC V hV P s u ⊓
      Module.End.eigenspace (A.baseChange ℂ) (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    intro u hu
    rw [hfam u hu]
    exact (b64c_transported_eigen_ranks_aux b C hC V hV hG hb f hk hsurj hgal hbranch hrot P
      hP s A hA ⟨u, hu⟩).1
  have hpos : ∀ u ∈ V, Module.finrank ℂ ↥(b64c_transportedFamily b C hC V hV P s u ⊓
      Module.End.eigenspace (A.baseChange ℂ) (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
    intro u hu
    rw [hfam u hu]
    exact (b64c_transported_eigen_ranks_aux b C hC V hV hG hb f hk hsurj hgal hbranch hrot P
      hP s A hA ⟨u, hu⟩).2
  intro t ht
  exact ⟨b64c_period_mapsTo_aux _ _ A m hJ hpol V _ hR hdim hneg hpos ht,
    b64c_period_filtration_aux _ _ A m hJ hpol V _ hR hdim hneg hpos t ht⟩

end HodgeLean.Foundations.Program
