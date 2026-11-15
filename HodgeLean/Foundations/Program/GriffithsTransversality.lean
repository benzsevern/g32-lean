import HodgeLean.Foundations.Program.GriffithsTransversalityProofs
import HodgeLean.Ported.TauCeti.TauCeti.Analysis.Contour.Residue.SimplePole

/-! Implication from retained shared geometry to a residue pairing and Griffiths formula
in flat full-homology period coordinates, with primitive invariant multiplication.
The comparison with the nine marked graph coordinates is a later basis calculation.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Holomorphic boundaries lie in holomorphic cocycles.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2; Forster, §12. -/
theorem b66g_boundaries (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66k_boundaries R t ≤
      b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t) ∧
    b66g_scalarBoundaries R t ≤ b66g_scalarCycles R t :=
  b66g_boundaries_aux R t

example := @b66g_boundaries

/-- Retained slice coordinates are holomorphic local coordinates on the actual fibre.
Source: Forster, §2, injective holomorphic maps; rf8_SharedFamily.hincl. -/
theorem b66g_slice_coordinate (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun p : rf8_fibre R.C t => (R.atlas.A a p.val).2)
      {p | p.val ∈ (R.atlas.A a).source} ∧
    ∀ p : rf8_fibre R.C t, p.val ∈ (R.atlas.A a).source →
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p ≠ 0 :=
  b66g_slice_coordinate_aux R t a

example := @b66g_slice_coordinate

/-- Every tangent cocycle has a meromorphic local splitting with finitely many poles.
Source: Forster, §§16–18, vanishing after a sufficiently positive divisor. -/
theorem b66g_meromorphic_splitting (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (u : b66k_Cochain R)
    (hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)) :
    ∃ (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ),
      (∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z) ∧
      (∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z) ∧
      ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x :=
  b66g_meromorphic_splitting_aux R t u hu

example := @b66g_meromorphic_splitting

/-- Perfect Serre pairing characterized by residues of every meromorphic splitting.
Source: Forster, §17, Serre duality for line bundles and the residue theorem. -/
theorem b66g_serre_pairing (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ E : b66k_cechH1 R t ≃ₗ[ℂ] Module.Dual ℂ (b66g_forms R t 2),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (c : b66k_cechH1 R t) (_hc : c.val = (b66k_boundaries R t).mkQ u)
      (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
      (_hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
      (_hreg : ∀ a z, z ∈ b66k_domain R t a →
        ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
      (_hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A b).source →
        u a b x = b66k_boundary R t v a b x) (q : b66g_forms R t 2),
      E c q = b66g_residueSum R t S v q.val :=
  b66g_serre_pairing_aux R t

example := @b66g_serre_pairing

/-- Contraction descends to the concrete scalar H¹ and multiplies differential coefficients.
Source: Griffiths, Periods II, §1(a), Proposition (1.20); Forster, §9. -/
theorem b66g_cup (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (∃ C : b66k_cechH1 R t →ₗ[ℂ] (b66g_forms R t 1 →ₗ[ℂ] b66g_H1O R t),
      ∀ (u : b66k_Cochain R)
      (_hu : u ∈ b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t))
      (c : b66k_cechH1 R t) (_hc : c.val = (b66k_boundaries R t).mkQ u)
      (q : b66g_forms R t 1),
      (C c q).val = (b66g_scalarBoundaries R t).mkQ (b66g_contract R q.val u)) ∧
    ∀ q r : b66g_forms R t 1, b66g_product R q.val r.val ∈ b66g_forms R t 2 :=
  b66g_cup_aux R t

example := @b66g_cup

/-- Griffiths formula in flat period coordinates, modulo the holomorphic period subspace.
Source: Griffiths, Periods II, §1(a), Proposition (1.20), and §1(b), Theorem (1.27); Voisin, Hodge Theory I, Theorem 10.21. -/
theorem b66g_griffiths (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (n : ℕ) (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    ∃ E : b66g_H1O R t ≃ₗ[ℂ] ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B),
      ∀ (U : Set (Fin 10 → ℂ)) (_hU : IsOpen U) (_ht : t.val ∈ U)
      (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
      (q : b66g_forms R t 1)
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
  b66g_griffiths_aux R s t n B

example := @b66g_griffiths

/-- Chart differentials identify with fibre differentials and the specified primitive image has dimension six.
Source: Forster, §9; Birkenhake–Lange, §12.2; b63d_lattice_rank. -/
theorem b66g_primitive_comparison (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (∃ M : b66g_forms R t 1 ≃ₗ[ℂ] b3_HolForm ℂ (rf8_fibre R.C t),
      (∀ (q : b66g_forms R t 1) (a : b66k_Index R) (p : rf8_fibre R.C t),
        p.val ∈ (R.atlas.A a).source → ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
        (M q).val ⟨p, v⟩ = q.val a p.val.2 *
          (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
            (fun y : rf8_fibre R.C t => (R.atlas.A a y.val).2) p v)) ∧
      ∀ q : b66g_forms R t 1, ∃ qP : b66g_forms R t 1,
        qP.val = b66g_projector R t q.val ∧
        (M qP).val = ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) •
          b3_pullback ℂ ℂ (fun x : rf8_fibre R.C t => g • x) (M q).val) ∧
    Module.finrank ℂ (b66g_primitiveForms R t) = 6 :=
  b66g_primitive_comparison_aux R t

example := @b66g_primitive_comparison

/-- Primitive multiplication followed by Reynolds averaging pairs identically with every branch deformation.
Source: Kodaira, §4.2, equivariant deformation; Forster, §17, naturality of duality; Serre, §2.2, averaging. -/
theorem b66g_invariant_primitive (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain R t a → MeromorphicAt (v a) z)
    (hreg : ∀ a z, z ∈ b66k_domain R t a →
      ((R.atlas.A a).symm (t.val, z)).2 ∉ S → AnalyticAt ℂ (v a) z)
    (hv : ∀ a b x, x ∉ S → (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      b66k_cocycle R t h a b x = b66k_boundary R t v a b x)
    (q r : b66g_primitiveForms R t) :
    ∃ Q : b66g_forms R t 2,
      Q.val = b66g_average R t (b66g_product R q.val r.val) ∧
      (∀ g : b4b_Group, b66g_pull R t 2 g Q.val = Q.val) ∧
      b66g_residueSum R t S v Q.val =
        b66g_residueSum R t S v (b66g_product R q.val r.val) :=
  b66g_invariant_primitive_aux R t h S v hmero hreg hv q r

example := @b66g_invariant_primitive

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

/-- Finite full-homology bases needed by the period formula exist on each retained fibre. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (b66g_Homology R s)) := by
  obtain ⟨P, _⟩ := b6m_period_comparison (rf8_fibre R.C s)
  let := b3_periodLattice_finite (E := ℂ) (C := rf8_fibre R.C s) (by simp)
  let := b3_periodLattice_free (E := ℂ) (C := rf8_fibre R.C s)
  exact ⟨_, ⟨(Module.finBasis ℤ (b3_periodLattice ℂ (rf8_fibre R.C s))).map P.symm⟩⟩

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

/-- The quotient derivative uses the same ten input columns as the marked field.
This is a type and column check, with no choice of geometric comparison. -/
example (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) (n : ℕ)
    (B : Module.Basis (Fin n) ℤ (b66g_Homology R s))
    (U : Set (Fin 10 → ℂ))
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (D : ((Fin n → ℂ) ⧸ b66g_periodSubspace R s t B) →ₗ[ℂ] (Fin 9 → ℂ))
    (i : Fin 9) (j : Fin 10) :
    LinearMap.toMatrix' (D.comp ((b66g_periodSubspace R s t B).mkQ.comp
      (fderiv ℂ (b66g_periods R s B θ) t.val).toLinearMap)) i j =
      D ((b66g_periodSubspace R s t B).mkQ
        (fderiv ℂ (b66g_periods R s B θ) t.val (Pi.single j 1))) i := rfl

/-- Exact derivative array occurring between L and T in the retained codiff premise. -/
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (t : Fin 10 → ℂ) (i : Fin 9) (j : Fin 10) :
    LinearMap.toMatrix'
      (fderiv ℂ (b64i_period R s m) t : (Fin 10 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ)) i j =
      fderiv ℂ (b64i_period R s m) t (Pi.single j 1) i := rfl

end HodgeLean.Foundations.Program
