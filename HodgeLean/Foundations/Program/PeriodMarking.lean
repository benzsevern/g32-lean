import HodgeLean.Foundations.Program.PeriodMarkingProofs

/-! # B6-4b: polarized rational period markings

Implication from the marked G32 cover geometry to a rational polarized K-linear marking,
and from such a marking to the four fixed-chart inputs and analytic marked frames.
The shared H7 lattice discriminant computation is used by the marking proof; it is not
a premise here. HC no distance; AV milestone no distance. Fibre uniformization and the
Schlesinger path belong to later stages.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The saturated G32 lattice gives a rank-twelve nondegenerate Hermitian space.
Source: G32 v0.16, Proposition 3.1 and §3.3; Birkenhake–Lange, §12.2;
`b63d_lattice_rank`, `b63d_prymOperator_sq`. -/
theorem b64b_lattice_hermitian (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q)
    (P : b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t),
      P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ) :

    let L := b63l_parameterLattice b C hC V hV t
    let E := b63e_singularQ b C hC V hV t P Q
    ∃ _B : Module.Basis (Fin 12) ℤ L,
    ∃ A : L →ₗ[ℤ] L,
      (∀ x, (A x).val = b63d_operator b C hC V hV t x.val) ∧
      ∃ hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id,
      ∃ hskew : ∀ x y, E.baseChange ℚ (A.baseChange ℚ x) y =
          -E.baseChange ℚ x (A.baseChange ℚ y),
        (b64b_latticeH L E ⟨A.baseChange ℚ, hJ⟩ hskew).IsSymm ∧
        (b64b_latticeH L E ⟨A.baseChange ℚ, hJ⟩ hskew).Nondegenerate :=
  b64b_lattice_hermitian_aux b C hC V hV t hG hb f hf hs hgal hbranch hrot Q hQ P hP

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    [T2Space (b63l_parameterFibre b C V hV t)] [CompactSpace (b63l_parameterFibre b C V hV t)]
    [ConnectedSpace (b63l_parameterFibre b C V hV t)]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun x : b63l_parameterFibre b C V hV t ↦ g • x))
    [FaithfulSMul b4b_Group (b63l_parameterFibre b C V hV t)]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (b63d_projection b C f V hV t))
    (hs : Function.Surjective (b63d_projection b C f V hV t))
    (hgal : b4_IsGaloisCover b4b_Group (b63d_projection b C f V hV t))
    (hbranch : b4_branchSet ℂ ℂ (b63d_projection b C f V hV t) = Set.range (b6_branch t.val))
    (hrot : ∀ i : Fin 13, ∃ x : b63l_parameterFibre b C V hV t,
      b63d_projection b C f V hV t x = b6_branch t.val i ∧ b4_IsRotGen ℂ x (b4b_root i))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)))
    (hQ : b3_IsIntersectionForm ℂ Q)
    (P : b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (hP : ∀ γ : b3_SmoothLoop ℂ (b63l_parameterFibre b C V hV t),
      P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ) :

    let L := b63l_parameterLattice b C hC V hV t
    let E := b63e_singularQ b C hC V hV t P Q
    ∃ _B : Module.Basis (Fin 12) ℤ L,
    ∃ A : L →ₗ[ℤ] L,
      (∀ x, (A x).val = b63d_operator b C hC V hV t x.val) ∧
      ∃ hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id,
      ∃ hskew : ∀ x y, E.baseChange ℚ (A.baseChange ℚ x) y =
          -E.baseChange ℚ x (A.baseChange ℚ y),
        (b64b_latticeH L E ⟨A.baseChange ℚ, hJ⟩ hskew).IsSymm ∧
        (b64b_latticeH L E ⟨A.baseChange ℚ, hJ⟩ hskew).Nondegenerate :=
  b64b_lattice_hermitian b C hC V hV t hG hb f hf hs hgal hbranch hrot Q hQ P hP

/-- Balanced Hodge eigenspaces give the signature of the lattice Hermitian form.
Source: van Geemen, LNM 1594, §§5.2–5.3; `hermSignature_weilHermitian`.
The balanced pair is insensitive to the homology sign convention. -/
theorem b64b_lattice_signature (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (Q : LinearMap.BilinForm ℤ M)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (hskew : ∀ x y, Q.baseChange ℚ (J.1 x) y = -Q.baseChange ℚ x (J.1 y))
    (A : M →ₗ[ℤ] M) (hA : A.baseChange ℚ = J.1)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hW : b2_IsWeightOne M F) (hR : b2_IsRiemannForm M F Q)
    (hdim : Module.finrank ℂ F = 6)
    (hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    hermSignature (b64b_latticeH M Q J hskew) = (3, 3) :=
  b64b_lattice_signature_aux M Q J hskew A hA F hW hR hdim hneg hpos

example (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (Q : LinearMap.BilinForm ℤ M)
    (J : {J : Module.End ℚ (ℚ ⊗[ℤ] M) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id})
    (hskew : ∀ x y, Q.baseChange ℚ (J.1 x) y = -Q.baseChange ℚ x (J.1 y))
    (A : M →ₗ[ℤ] M) (hA : A.baseChange ℚ = J.1)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hW : b2_IsWeightOne M F) (hR : b2_IsRiemannForm M F Q)
    (hdim : Module.finrank ℂ F = 6)
    (hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    hermSignature (b64b_latticeH M Q J hskew) = (3, 3) :=
  b64b_lattice_signature M Q J hskew A hA F hW hR hdim hneg hpos

/-- Complexification of a rational map commutes with real conjugation.
Source: Bourbaki, Algebra, Ch. II, §5, extension of scalars. -/
theorem b64b_complex_conj (M : Type*) [AddCommGroup M]
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (x : ℂ ⊗[ℤ] M) :
    b64b_complexMarking M m (b2_conj M x) =
      b2_conj b60_Lattice (b64b_complexMarking M m x) :=
  b64b_complex_conj_aux M m x

example (M : Type*) [AddCommGroup M]
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (x : ℂ ⊗[ℤ] M) :
    b64b_complexMarking M m (b2_conj M x) =
      b2_conj b60_Lattice (b64b_complexMarking M m x) :=
  b64b_complex_conj M m x

/-- A K-linear rational marking identifies eigenspaces with the same eigenvalue.
Source: van Geemen, LNM 1594, §5.1; scalar extension of an intertwining map.
The homology action has positive sign. -/
theorem b64b_complex_action (M : Type*) [AddCommGroup M] (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (z : ℂ) :
    (Module.End.eigenspace (A.baseChange ℂ) z).map
      (b64b_complexMarking M m).toLinearMap = Module.End.eigenspace b60_omegaC z :=
  b64b_complex_action_aux M A m hA z

example (M : Type*) [AddCommGroup M] (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (z : ℂ) :
    (Module.End.eigenspace (A.baseChange ℂ) z).map
      (b64b_complexMarking M m).toLinearMap = Module.End.eigenspace b60_omegaC z :=
  b64b_complex_action M A m hA z

/-- A polarized rational marking carries the Riemann relations and both Hodge ranks.
Source: Birkenhake–Lange, §4.2; van Geemen, LNM 1594, §§5.7–5.10.
These are precisely the four inputs of `b60c_fixed_filtration_chart`. -/
theorem b64b_marking_riemann (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : b2_IsRiemannForm M F Q)
    (hdim : Module.finrank ℂ F = 6)
    (hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    let G := F.map (b64b_complexMarking M m).toLinearMap
    b2_IsRiemannForm b60_Lattice G b60_E ∧
      Module.finrank ℂ G = 6 ∧
      Module.finrank ℂ ↥(G ⊓ Module.End.eigenspace b60_omegaC
        (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
      Module.finrank ℂ ↥(G ⊓ Module.End.eigenspace b60_omegaC
        (Complex.I * (Real.sqrt 3 : ℂ))) = 3 :=
  b64b_marking_riemann_aux M Q A m hA hQ F hR hdim hneg hpos

example (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : b2_IsRiemannForm M F Q)
    (hdim : Module.finrank ℂ F = 6)
    (hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    let G := F.map (b64b_complexMarking M m).toLinearMap
    b2_IsRiemannForm b60_Lattice G b60_E ∧
      Module.finrank ℂ G = 6 ∧
      Module.finrank ℂ ↥(G ⊓ Module.End.eigenspace b60_omegaC
        (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
      Module.finrank ℂ ↥(G ⊓ Module.End.eigenspace b60_omegaC
        (Complex.I * (Real.sqrt 3 : ℂ))) = 3 :=
  b64b_marking_riemann M Q A m hA hQ F hR hdim hneg hpos

/-- Analytic coefficients in an integral frame remain analytic in the fixed eigenbasis.
Source: Griffiths, Periods I, §1; Bourbaki, Algebra, Ch. II, §5.
This applies to the coefficients of `b63e_filtration_frame`. -/
theorem b64b_marked_frame_analytic (M : Type*) [AddCommGroup M]
    (B : Module.Basis (Fin 12) ℤ M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (c : Fin 6 → (Fin 10 → ℂ) → Fin 12 → ℂ)
    (hc : ∀ i j, AnalyticOnNhd ℂ (fun t => c i t j) W) :
    ∀ i p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr
      (b64b_complexMarking M m (b63e_coordVector B (c i t))) p) W :=
  b64b_marked_frame_analytic_aux M B m W c hc

example (M : Type*) [AddCommGroup M]
    (B : Module.Basis (Fin 12) ℤ M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (c : Fin 6 → (Fin 10 → ℂ) → Fin 12 → ℂ)
    (hc : ∀ i j, AnalyticOnNhd ℂ (fun t => c i t j) W) :
    ∀ i p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr
      (b64b_complexMarking M m (b63e_coordVector B (c i t))) p) W :=
  b64b_marked_frame_analytic M B m W c hc


/-- The forward root product matches the reversed peripheral relation in the opposite group. -/
example : (List.ofFn b4b_root).prod = 1 := by
  exact b63d_root_product

example : (List.ofFn (fun i => MulOpposite.op (b4b_root i))).reverse.prod = 1 := by
  simpa only [List.map_ofFn, Function.comp_def, MulOpposite.op_one] using
    (MulOpposite.op_list_prod (List.ofFn b4b_root)).symm.trans
      (congrArg MulOpposite.op b63d_root_product)

/-- Input check on a lattice of rank twelve with a nonidentity polarized marking.
The action is not the identity, and its two Hodge ranks are both three. -/
example :
    Module.finrank ℚ (ℚ ⊗[ℤ] b60_Lattice) = 12 ∧
    b60_omega ≠ LinearMap.id ∧
    (∃ x : ℚ ⊗[ℤ] b60_Lattice, (LinearEquiv.neg ℚ) x ≠ x) ∧
    (∀ x, (LinearEquiv.neg ℚ) (b60_omega.baseChange ℚ x) =
      b60_omega.baseChange ℚ ((LinearEquiv.neg ℚ) x)) ∧
    (∀ x y, b60_E.baseChange ℚ ((LinearEquiv.neg ℚ) x) ((LinearEquiv.neg ℚ) y) =
      b60_E.baseChange ℚ x y) ∧
    b2_IsWeightOne b60_Lattice (b60_F 0) ∧
    b2_IsRiemannForm b60_Lattice (b60_F 0) b60_E ∧
    Module.finrank ℂ (b60_F 0) = 6 ∧
    Module.finrank ℂ ↥(b60_F 0 ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
    Module.finrank ℂ ↥(b60_F 0 ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
  let B := (Pi.basisFun ℤ (Fin 6 × Fin 2)).baseChange ℚ
  refine ⟨?_, ?_, ?_, fun x => ?_, fun x y => ?_,
    b60_weight_one ⟨0, g32m_zero_mem⟩,
    (b60_riemann_iff 0).2 g32m_zero_mem, ?_,
    (b60_weil_dimensions 0).2, (b60_weil_dimensions 0).1⟩
  · simp
  · intro h
    have hh := congrArg (fun A : b60_Lattice →ₗ[ℤ] b60_Lattice =>
      A (Pi.single (0, 0) 1) (0, 1)) h
    norm_num [b60_omega, Pi.single_apply] at hh
  · refine ⟨B (0, 0), fun h => ?_⟩
    have hh := congrArg (fun x => B.repr x (0, 0)) h
    norm_num only [LinearEquiv.neg_apply, map_neg, Module.Basis.repr_self,
      Finsupp.single_eq_same, Finsupp.neg_apply] at hh
  · simp only [LinearEquiv.neg_apply, map_neg]
  · simp only [LinearEquiv.neg_apply, map_neg, LinearMap.neg_apply, neg_neg]
  · rw [b60_F, finrank_span_eq_card (b60_frame_independent 0)]
    rfl

/-- A rank-twelve integral basis and a nonconstant six-vector graph have analytic
coefficients. Each head coordinate is one; each tail coordinate varies with `t 0`.
No vector is zero and the graph has six independent head coordinates. -/
example :
    let _B := (Pi.basisFun ℤ (Fin 6 × Fin 2)).reindex finProdFinEquiv
    let c : Fin 6 → (Fin 10 → ℂ) → Fin 12 → ℂ := fun i t j =>
      if j = Fin.castAdd 6 i then 1 else if j = Fin.natAdd 6 i then t 0 else 0
    (∀ i j, AnalyticOnNhd ℂ (fun t => c i t j) Set.univ) ∧
    (∀ i t, c i t (Fin.castAdd 6 i) = 1) ∧
    c 0 0 (Fin.natAdd 6 (0 : Fin 6)) ≠ c 0 (fun _ => 1) (Fin.natAdd 6 (0 : Fin 6)) ∧
    Module.finrank ℂ (ℂ ⊗[ℤ] b60_Lattice) = 12 := by
  dsimp only
  refine ⟨fun i j => ?_, fun i t => by simp, by norm_num, ?_⟩
  · split_ifs
    · exact analyticOnNhd_const
    · exact (ContinuousLinearMap.proj (0 : Fin 10) :
        (Fin 10 → ℂ) →L[ℂ] ℂ).analyticOnNhd Set.univ
    · exact analyticOnNhd_const
  · simp

/-- Chain check to the `mapsTo` field of `g32r_PeriodMap`: the marked filtration
has a point of the frozen nine-coordinate domain, with exactly that filtration. -/
example (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (Q : LinearMap.BilinForm ℤ M) (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (F : Submodule ℂ (ℂ ⊗[ℤ] M)) (hR : b2_IsRiemannForm M F Q)
    (hdim : Module.finrank ℂ F = 6)
    (hneg : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3)
    (hpos : Module.finrank ℂ ↥(F ⊓ Module.End.eigenspace (A.baseChange ℂ)
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3) :
    b64_coordOf (F.map (b64b_complexMarking M m).toLinearMap) ∈ g32m_Domain ∧
    b60_F (b64_coordOf (F.map (b64b_complexMarking M m).toLinearMap)) =
      F.map (b64b_complexMarking M m).toLinearMap := by
  obtain ⟨hR', hd, hn, hp⟩ := b64b_marking_riemann M Q A m hA hQ F hR hdim hneg hpos
  obtain ⟨τ, hτ⟩ := b60c_fixed_filtration_chart _ hd hn hp hR'
  rw [hτ, b64_coordOf_eq]
  exact ⟨τ.property, rfl⟩

end HodgeLean.Foundations.Program
