import HodgeLean.Foundations.Program.PeriodMarkingComparison
import HodgeLean.Foundations.Program.PeriodMarkingGeometry
import HodgeLean.Foundations.Program.PeriodMarkingDiscriminant

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open HodgeLean.Foundations.WeilHermitian HodgeLean.Foundations.HermitianForm
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b64b_lattice_hermitian_aux (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
        (b64b_latticeH L E ⟨A.baseChange ℚ, hJ⟩ hskew).Nondegenerate := by
  classical
  let D := b63l_parameterFibre b C V hV t
  let L := b63l_parameterLattice b C hC V hV t
  let E := b63e_singularQ b C hC V hV t P Q
  obtain ⟨⟨B⟩, _⟩ := b63d_lattice_rank b C hC V hV t hG hb f hf hs hgal hbranch hrot
  let : Module.Free ℤ L := Module.Free.of_basis B
  let : Module.Finite ℤ L := Module.Finite.of_basis B
  obtain ⟨A, hA, hsq⟩ := b63d_prymOperator_sq b C hC V hV t hG
  obtain ⟨e', hev, hPA⟩ := b64b_period_comparison b C hC V hV t hG P hP A hA
  have hE : E = (b63l_periodQ D Q).compl₁₂ e'.toLinearMap e'.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q (P x.val) (P y.val) = Q (e' x).val (e' y).val
    rw [hev, hev]
  refine ⟨B, A, hA, ?_⟩
  dsimp only [E] at hE
  rw [hE]
  apply b64b_period_hermitian D hG Q hQ L e' A hsq
  exact hPA

theorem b64b_lattice_signature_aux (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
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
    hermSignature (b64b_latticeH M Q J hskew) = (3, 3) := by
  obtain ⟨e⟩ := b64b_hermitian_real_isometry M Q J hskew A hA
  have hs := b64b_real_signature M Q A F hW hR hdim hneg hpos
  unfold hermSignature
  rw [QuadraticMap.Equivalent.sigPos_eq ⟨e⟩,
    QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩, hs.1, hs.2]

theorem b64b_geometric_signature (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
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
      P (b6m_loopClass _ γ) = b3_latticePeriod ℂ _ γ)
    [Module.Free ℤ (b63l_parameterLattice b C hC V hV t)] [Module.Finite ℤ (b63l_parameterLattice b C hC V hV t)]
    (A : (b63l_parameterLattice b C hC V hV t) →ₗ[ℤ] (b63l_parameterLattice b C hC V hV t))
    (hA : ∀ x, (A x).val = b63d_operator b C hC V hV t x.val)
    (hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, (b63e_singularQ b C hC V hV t P Q).baseChange ℚ (A.baseChange ℚ x) y =
      -(b63e_singularQ b C hC V hV t P Q).baseChange ℚ x (A.baseChange ℚ y)) :
    hermSignature (b64b_latticeH (b63l_parameterLattice b C hC V hV t) (b63e_singularQ b C hC V hV t P Q) ⟨A.baseChange ℚ, hJ⟩ hskew) = (3, 3) := by
  let D := b63l_parameterFibre b C V hV t
  let L := b63l_parameterLattice b C hC V hV t
  let E := b63e_singularQ b C hC V hV t P Q
  obtain ⟨e, he, hAe⟩ := b64b_period_comparison b C hC V hV t hG P hP A hA
  have hE : E = (b63l_periodQ D Q).compl₁₂ e.toLinearMap e.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q (P x.val) (P y.val) = Q (e x).val (e y).val
    rw [he, he]
  have hd := b63d_dim_eq b C hC V hV t hG hb f hf hs hgal hbranch hrot
  have hh := b63d_chevalleyWeil_hodge b C hC V hV t hG hb f hf hs hgal hbranch hrot
  exact b64b_signature_of_period_data D hG Q hQ L e A hAe E hE
    ⟨A.baseChange ℚ, hJ⟩ rfl hskew hd.2.2 hh.2.2.2 hh.2.2.1

theorem b64b_cancel_conj (N : Type*) [AddCommGroup N] (c : ℂ)
    (y : ℚ ⊗[ℤ] N) :
    b2_conj N (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ N
      (c ⊗ₜ[ℚ] y)) =
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ N
      ((starRingEnd ℂ c) ⊗ₜ[ℚ] y) := by
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | tmul q n =>
    simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      b2a_conj_tmul, starRingEnd_apply, star_smul, star_trivial]

theorem b64b_complex_conj_aux (M : Type*) [AddCommGroup M]
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (x : ℂ ⊗[ℤ] M) :
    b64b_complexMarking M m (b2_conj M x) =
      b2_conj b60_Lattice (b64b_complexMarking M m x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
    simp only [b2a_conj_tmul, b64b_complexMarking, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul]
    exact (b64b_cancel_conj b60_Lattice c (m (1 ⊗ₜ[ℤ] x))).symm

theorem b64b_cancel_action (N : Type*) [AddCommGroup N] (A : N →ₗ[ℤ] N)
    (c : ℂ) (y : ℚ ⊗[ℤ] N) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ N
      (c ⊗ₜ[ℚ] A.baseChange ℚ y) =
    A.baseChange ℂ (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ N
      (c ⊗ₜ[ℚ] y)) := by
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
  | tmul q n =>
    simp only [LinearMap.baseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

theorem b64b_complex_intertwines (M : Type*) [AddCommGroup M] (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (x : ℂ ⊗[ℤ] M) :
    b64b_complexMarking M m (A.baseChange ℂ x) =
      b60_omegaC (b64b_complexMarking M m x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
    simp only [LinearMap.baseChange_tmul, b64b_complexMarking, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul]
    have hh := hA ((1 : ℚ) ⊗ₜ[ℤ] x)
    change m ((1 : ℚ) ⊗ₜ[ℤ] A x) = _ at hh
    rw [hh]
    exact b64b_cancel_action b60_Lattice b60_omega c (m (1 ⊗ₜ[ℤ] x))

theorem b64b_complex_action_aux (M : Type*) [AddCommGroup M] (A : M →ₗ[ℤ] M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, m (A.baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (z : ℂ) :
    (Module.End.eigenspace (A.baseChange ℂ) z).map
      (b64b_complexMarking M m).toLinearMap = Module.End.eigenspace b60_omegaC z := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx ⊢
    change b60_omegaC (b64b_complexMarking M m x) = z • b64b_complexMarking M m x
    rw [← b64b_complex_intertwines M A m hA, hx, map_smul]
  · intro hy
    obtain ⟨x, rfl⟩ := (b64b_complexMarking M m).surjective y
    refine ⟨x, ?_, rfl⟩
    simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hy ⊢
    apply (b64b_complexMarking M m).injective
    rw [b64b_complex_intertwines M A m hA, map_smul]
    exact hy

theorem b64b_cancel_pairing (N : Type*) [AddCommGroup N]
    (Q : LinearMap.BilinForm ℤ N) (c d : ℂ) (x y : ℚ ⊗[ℤ] N) :
    Q.baseChange ℂ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ N (c ⊗ₜ[ℚ] x))
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ N (d ⊗ₜ[ℚ] y)) =
      c * d * ((Q.baseChange ℚ x y : ℚ) : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz =>
    simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, Rat.cast_add,
      mul_add, hx, hz]
  | tmul q n =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      simp only [TensorProduct.tmul_add, map_add, Rat.cast_add, mul_add, hy, hz]
    | tmul r k =>
      simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, Rat.smul_def,
        Rat.cast_mul, Rat.cast_intCast]
      ring

theorem b64b_complex_pairing (M : Type*) [AddCommGroup M]
    (Q : LinearMap.BilinForm ℤ M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hQ : ∀ x y, b60_E.baseChange ℚ (m x) (m y) = Q.baseChange ℚ x y)
    (x y : ℂ ⊗[ℤ] M) :
    b60_E.baseChange ℂ (b64b_complexMarking M m x) (b64b_complexMarking M m y) =
      Q.baseChange ℂ x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul c n =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul d k =>
      simp only [b64b_complexMarking, LinearEquiv.trans_apply,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        LinearEquiv.baseChange_tmul]
      rw [b64b_cancel_pairing, hQ]
      simp only [LinearMap.BilinForm.baseChange_tmul, mul_one, Rat.cast_intCast, zsmul_eq_mul]
      ring

theorem b64b_marking_riemann_aux (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
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
        (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
  let e := b64b_complexMarking M m
  have hp (x y : ℂ ⊗[ℤ] M) :
      b60_E.baseChange ℂ (e x) (e y) = Q.baseChange ℂ x y :=
    b64b_complex_pairing M Q m hQ x y
  have hr : b2_IsRiemannForm b60_Lattice (F.map e.toLinearMap) b60_E := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := e.surjective ((1 : ℂ) ⊗ₜ[ℤ] x)
      have hz := (hp y y).trans (b2a_baseChange_alt Q hR.alt y)
      rw [hy, LinearMap.BilinForm.baseChange_tmul] at hz
      norm_cast at hz
      simpa using hz
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (hp x y).trans (hR.isotropic x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩ hn
      have hx0 : x ≠ 0 := fun h => hn (by simp only [h, map_zero])
      change 0 < (Complex.I * b60_E.baseChange ℂ (e x) (b2_conj b60_Lattice (e x))).re
      rw [← b64b_complex_conj_aux M m, hp]
      exact hR.positive x hx hx0
  refine ⟨hr, (e.finrank_map_eq F).trans hdim, ?_, ?_⟩
  · rw [← b64b_complex_action_aux M A m hA,
      ← Submodule.map_inf e.toLinearMap e.injective, e.finrank_map_eq]
    exact hneg
  · rw [← b64b_complex_action_aux M A m hA,
      ← Submodule.map_inf e.toLinearMap e.injective, e.finrank_map_eq]
    exact hpos

theorem b64b_marked_frame_analytic_aux (M : Type*) [AddCommGroup M]
    (B : Module.Basis (Fin 12) ℤ M)
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (W : Set (Fin 10 → ℂ)) (c : Fin 6 → (Fin 10 → ℂ) → Fin 12 → ℂ)
    (hc : ∀ i j, AnalyticOnNhd ℂ (fun t => c i t j) W) :
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
  exact Finset.analyticOnNhd_fun_sum _ fun j _ => (hc i j).mul analyticOnNhd_const

end HodgeLean.Foundations.Program
