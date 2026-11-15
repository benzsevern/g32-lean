import HodgeLean.Foundations.Program.PeriodMultiplicationProofs

/-! Implication from retained geometry to primitive contraction and residue multiplication.
The polarized marked-coordinate identification is included; comparison with the B6-5 certified jet remains a further obligation.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Primitive restriction of the transported-period derivative formula.
Source: Griffiths, Periods II, §1(b), Theorem (1.27); b66g_griffiths. -/
theorem b66m_primitive_griffiths (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (n : ℕ) (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    ∃ E : b66g_H1O R t ≃ₗ[ℂ] ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B),
      ∀ (U : Set (Fin 10 → ℂ)) (_hU : IsOpen U) (_ht : t.val ∈ U)
      (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
      (q : b66g_primitiveForms R t)
      (_hq : ∀ (a : b66k_Index R) (p : rf8_fibre R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        θ.val t ⟨p, v⟩ = q.val a p.val.2 *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v)),
      DifferentiableAt ℂ (b66g_periods R s B θ) t.val ∧
      ∀ h : Fin 10 → ℂ, ∃ c : b66g_H1O R t,
        c.val = (b66g_scalarBoundaries R t).mkQ
          (b66g_contract R q.val (b66k_cocycle R t h)) ∧
        E c = (b66g_periodSubspace R s t B).mkQ
          (fderiv ℂ (b66g_periods R s B θ) t.val h) :=
  b66m_primitive_griffiths_aux R s t n B

example := @b66m_primitive_griffiths

/-- Scalar Serre duality takes contraction to multiplication.
Source: Forster, Lectures on Riemann Surfaces, §17, Serre duality and its tensor naturality. -/
theorem b66m_dual_contraction (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ J : b66g_H1O R t ≃ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 1),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source → u a b x = b66k_boundary R t v a b x)
      (q r : b66g_forms R t 1),
      ∃ c : b66g_H1O R t,
        c.val = (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u) ∧
        J c r = b66g_residueSum R t S v (b66g_product R q.val r.val) :=
  b66m_dual_contraction_aux R t

example := @b66m_dual_contraction

/-- Symmetric multiplication lands in invariant holomorphic quadratic differentials.
Source: Forster, §9, tensor products; Serre, Linear Representations, §2.2, Reynolds averaging. -/
theorem b66m_symmetric_product (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : b66g_primitiveForms R t) :
    b66m_multiply R t q r = b66m_multiply R t r q ∧
    b66m_multiply R t q r ∈ b66g_forms R t 2 ∧
    ∀ g : b4b_Group, b66g_pull R t 2 g (b66m_multiply R t q r) =
      b66m_multiply R t q r :=
  b66m_symmetric_product_aux R t q r

example := @b66m_symmetric_product

/-- The branch multiplication array is independent of meromorphic splittings and uses unaveraged products.
Source: Forster, §17, residue duality; b66g_invariant_primitive. -/
theorem b66m_residue_matrix (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : Fin 3 → b66g_primitiveForms R t)
    (S S' : Fin 10 → Finset R.C)
    (v v' : Fin 10 → b66k_Index R → ℂ → ℂ)
    (hmero : ∀ j a z, z ∈ b66k_domain R t a → MeromorphicAt (v j a) z)
    (hreg : ∀ j a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
    (hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v j) a b x)
    (hmero' : ∀ j a z, z ∈ b66k_domain R t a → MeromorphicAt (v' j a) z)
    (hreg' : ∀ j a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S' j → AnalyticAt ℂ (v' j a) z)
    (hv' : ∀ j a b x, x ∉ S' j → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v' j) a b x) :
    b66m_multiplicationMatrix R t q r S v = b66m_multiplicationMatrix R t q r S' v' ∧
    ∀ i j, b66m_multiplicationMatrix R t q r S v i j =
      b66g_residueSum R t (S j) (v j)
        (b66g_product R (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1).val
          (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2).val) :=
  b66m_residue_matrix_aux R t q r S S' v v' hmero hreg hv hmero' hreg' hv'

example := @b66m_residue_matrix

/-- Original polarized periods normalize six primitive forms, and their residue products
are the marked period derivative after an explicit invertible output change.
The branch basis is the standard basis, so the input change is the identity.
Source: Griffiths, Periods II, §1; Forster, §17; van Geemen, §5.10; b66_period_toMatrix. -/
theorem b66m_polarized_matrix (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    ∃ (q r : Fin 3 → b66g_primitiveForms R t)
      (ω η : Fin 3 → b3_HolForm ℂ (rf8_fibre R.C t)) (κ : ℂ),
      (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
        κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
      (∀ i, (ω i).val = b66m_chartForm R t (q i).val ∧
        (η i).val = b66m_chartForm R t (r i).val) ∧
      LinearIndependent ℂ (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) ∧
      Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 3 =>
        if ij.1 = 0 then q ij.2 else r ij.2)) = ⊤ ∧
      (∀ (i : Fin 3) (x : b63l_parameterLattice mr_base R.C R.hC
        (b6t_polydisc mr_base) (Subset.refl _) s),
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (ω i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b64i_period R s m t.val) (0, i)) ∧
        (b63e_transportMap mr_base R.C R.hC (b6t_polydisc mr_base)
          (Subset.refl _) R.P s t x).val (η i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b64i_period R s m t.val) (1, i))) ∧
      IsUnit (b66m_leftMatrix (b64i_period R s m t.val) κ) ∧
      ∀ (S : Fin 10 → Finset R.C) (v : Fin 10 → b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ j a z, z ∈ b66k_domain R t a → MeromorphicAt (v j a) z)
      (_hreg : ∀ j a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
      (_hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v j) a b x),
        b66m_multiplicationMatrix R t q r S v =
          b66m_leftMatrix (b64i_period R s m t.val) κ *
            LinearMap.toMatrix' (fderiv ℂ (b64i_period R s m) t.val).toLinearMap *
              (1 : Matrix (Fin 10) (Fin 10) ℂ) :=
  b66m_polarized_matrix_aux R s t m hJ hpol

example := @b66m_polarized_matrix

/-- The multiplication jet has the retained codiff shape along every continuous path
through the polydisc. The output change is the polarized matrix and the input change is 1.
Source: Griffiths, Periods II, §1; G32, Lemma 5.1; b66m_polarized_matrix. -/
theorem b66m_jet_codiff (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y)
    (curve : ℂ → Fin 10 → ℂ) (hcurve : ContinuousAt curve 0)
    (hzero : curve 0 ∈ b6t_polydisc mr_base) :
    ∃ (q r : (t : b6t_polydisc mr_base) → Fin 3 → b66g_primitiveForms R t)
      (S : (t : b6t_polydisc mr_base) → Fin 10 → Finset R.C)
      (v : (t : b6t_polydisc mr_base) → Fin 10 → b66k_Index R → ℂ → ℂ),
      (∀ t, LinearIndependent ℂ
        (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q t ij.2 else r t ij.2)) ∧
      (∀ t j a z, z ∈ b66k_domain R t a → MeromorphicAt (v t j a) z) ∧
      (∀ t j a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S t j → AnalyticAt ℂ (v t j a) z) ∧
      (∀ t j a b x, x ∉ S t j → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        b66k_cocycle R t (Pi.single j 1) a b x = b66k_boundary R t (v t j) a b x) ∧
      ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
        ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
          (∃ κ : ℂ, (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
            κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
            L = b66m_leftMatrix (b64i_period R s m (curve θ)) κ) ∧
          T = 1 ∧
          b66m_jet R q r S v curve θ = L * LinearMap.toMatrix'
            (fderiv ℂ (b64i_period R s m) (curve θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T :=
  b66m_jet_codiff_aux R s m hJ hpol curve hcurve hzero

example := @b66m_jet_codiff

/-- Shared geometry has twelve independent primitive cycles and nonidentity rotation.
The witness uses existing checked statements only. -/
example : ∃ R : rf8_SharedFamily,
    b4b_root 0 ≠ 1 ∧ ∀ t : b6t_polydisc mr_base,
      Nonempty (Module.Basis (Fin 12) ℤ
        (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) t)) := by
  obtain ⟨R, _⟩ := rf8_shared_root
  refine ⟨R, ?_, fun t => ?_⟩
  · intro h
    have ho := b63_root_order (0 : Fin 13)
    rw [h, orderOf_one] at ho
    norm_num at ho
  · exact (b63d_lattice_rank mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) t
      (R.hG t) mr_base_mem_chart R.atlas.f (R.hk t) (R.hsurj t) (R.hgal t)
      (R.hbranch t) (R.hrot t)).1

/-- Ten branch directions include a nonzero coordinate velocity. -/
example : Module.finrank ℂ (Fin 10 → ℂ) = 10 ∧
    (Pi.single (0 : Fin 10) (1 : ℂ) : Fin 10 → ℂ) ≠ 0 := by
  constructor
  · simp
  · intro h
    have := congrFun h 0
    norm_num at this

/-- The residue operation used in the pairing has a nonzero simple-pole value. -/
example : TauCeti.Contour.residue (fun z : ℂ => (z - 0)⁻¹) 0 = 1 :=
  TauCeti.Contour.residue_sub_inv 0

/-- Checked model frames have three independent negative directions. -/
example (z : Fin 9 → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (b64_negFrame z))) = 3 := by
  rw [← b64_negFrame_span]
  exact (b60_weil_dimensions z).2

/-- Product rows use all nine ordered pairs, rather than a diagonal-only array. -/
example : Function.Bijective (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) :=
  Equiv.bijective _

/-- Column convention at the exact retained marked derivative. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (t : Fin 10 → ℂ) (i : Fin 9) (j : Fin 10) :
    LinearMap.toMatrix'
      (fderiv ℂ (b64i_period R s m) t : (Fin 10 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ)) i j =
      fderiv ℂ (b64i_period R s m) t (Pi.single j 1) i := rfl

end HodgeLean.Foundations.Program
