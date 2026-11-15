import HodgeLean.Foundations.Program.PathCoverFamilyDefs
import HodgeLean.Foundations.Program.PeriodBasisAlignmentDefs

/-! # B6-6 stage 6e at the G32 centre: chart forms and residue arrays (definitions)

The chart coefficients, holomorphic and primitive differentials, Reynolds average, residue sums,
residue multiplication array and ordered frame change of stages 6c, 6d and the 6e preparation
(`b66k_`, `b66g_`, `b66m_`, `b66e_`), restated for a family `D : b65z_SharedFamily c g` about an
arbitrary centre `c`; and the eigen-direction of a primitive form, read from its periods in a
rational marking. Every restated definition is the original one with `mr_base` replaced by `c`
and the retained family replaced by `D`; at `mr_base` they agree with the originals by `rfl`
(checked below for `b65z_ofRetained`). No statement is asserted here.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}

/-- Indices of the total atlas of a family about `c`.
Source: `rf7_HurwitzAtlas.A`; `b66k_Index` with `mr_base` replaced by `c`. -/
abbrev b66f_Index (D : b65z_SharedFamily c g) := b6t_polydisc c × D.C
example (D : b65z_SharedFamily c g) (a : b66f_Index D) : a = a := rfl

/-- Fibre-coordinate domain of a chart.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2;
`b66k_domain` with `mr_base` replaced by `c`. -/
def b66f_domain (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (a : b66f_Index D) : Set ℂ := {z | (t.val, z) ∈ (D.atlas.A a).target}
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a : b66f_Index D)
    (z : ℂ) : z ∈ b66f_domain D t a ↔ (t.val, z) ∈ (D.atlas.A a).target := Iff.rfl

/-- Transition from chart `a` to chart `b`, including its parameter coordinate.
Source: Kodaira, §4.2, transition functions; `b66k_transition` with `mr_base` replaced by `c`. -/
def b66f_transition (D : b65z_SharedFamily c g) (a b : b66f_Index D)
    (u : (Fin 10 → ℂ) × ℂ) : ℂ := (D.atlas.A b ((D.atlas.A a).symm u)).2
example (D : b65z_SharedFamily c g) (a b : b66f_Index D) (u : (Fin 10 → ℂ) × ℂ) :
    b66f_transition D a b u = (D.atlas.A b ((D.atlas.A a).symm u)).2 := rfl

/-- Ambient one-cochains, expressed in the target chart.
Source: Kodaira, §4.2, tangent-valued Čech cochains; `b66k_Cochain`. -/
abbrev b66f_Cochain (D : b65z_SharedFamily c g) :=
  b66f_Index D → b66f_Index D → D.C → ℂ
example (D : b65z_SharedFamily c g) : (0 : b66f_Cochain D) = 0 := rfl

/-- Change of vertical tangent coordinates at a fibre point.
Source: Kodaira, §4.2, chain rule on chart overlaps; `b66k_vertical`. -/
def b66f_vertical (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (a b : b66f_Index D) (x : D.C) : ℂ :=
  fderiv ℂ (b66f_transition D a b) (D.atlas.A a (t, x)) (0, 1)
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b : b66f_Index D) (x : D.C) :
    b66f_vertical D t a b x = fderiv ℂ (b66f_transition D a b) (D.atlas.A a (t, x)) (0, 1) :=
  rfl

/-- Coboundary of chartwise coefficients, extended by zero off overlaps.
Source: Kodaira, §4.2, `d(v)_ab = D(f_ab) v_a - v_b`; `b66k_boundary`. -/
def b66f_boundary (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (v : b66f_Index D → ℂ → ℂ) : b66f_Cochain D := fun a b x =>
  if (t, x) ∈ (D.atlas.A a).source ∩ (D.atlas.A b).source then
    b66f_vertical D t a b x * v a (D.atlas.A a (t, x)).2 -
      v b (D.atlas.A b (t, x)).2 else 0
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : b66f_boundary D t 0 = 0 := by
  funext a b x
  simp [b66f_boundary]

/-- Kodaira–Spencer cochain of a parameter velocity: the parameter derivative of the transition
at fixed source coordinate.
Source: Kodaira, §4.2, Kodaira–Spencer cocycle; `b66k_cocycle`. -/
def b66f_cocycle (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    (Fin 10 → ℂ) →ₗ[ℂ] b66f_Cochain D where
  toFun h a b x := if (t, x) ∈ (D.atlas.A a).source ∩ (D.atlas.A b).source then
    fderiv ℂ (b66f_transition D a b) (D.atlas.A a (t, x)) (h, 0) else 0
  map_add' h k := by
    funext a b x
    simp only [Pi.add_apply]
    split_ifs with hmem
    · simpa only [Prod.mk_add_mk, add_zero] using
        map_add (fderiv ℂ (b66f_transition D a b) (D.atlas.A a (t, x))) (h, (0 : ℂ)) (k, (0 : ℂ))
    · exact (add_zero 0).symm
  map_smul' r h := by
    funext a b x
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs with hmem
    · simpa only [Prod.smul_mk, smul_zero] using
        (map_smul (fderiv ℂ (b66f_transition D a b) (D.atlas.A a (t, x))) r (h, 0))
    · exact (smul_zero r).symm
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : b66f_cocycle D t 0 = 0 :=
  map_zero _

/-- Deck map written in two fibre coordinates.
Source: Kodaira, §4.2; `b66k_deckCoordinate`. -/
def b66f_deckCoordinate (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (h : b4b_Group) (a b : b66f_Index D) (z : ℂ) : ℂ :=
  (D.atlas.A b (t, h • ((D.atlas.A a).symm (t.val, z)).2)).2
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (h : b4b_Group)
    (a b : b66f_Index D) (z : ℂ) : b66f_deckCoordinate D t h a b z =
      (D.atlas.A b (t, h • ((D.atlas.A a).symm (t.val, z)).2)).2 := rfl

/-- Coefficients of differentials in the charts.
Source: Forster, Lectures on Riemann Surfaces, §9; `b66g_Coeff`. -/
abbrev b66f_Coeff (D : b65z_SharedFamily c g) := b66f_Index D → D.C → ℂ
example (D : b65z_SharedFamily c g) : (0 : b66f_Coeff D) = 0 := rfl

/-- Holomorphic `m`-differentials on the fibre over `t`, with their tensor transition law and
zero extension.
Source: Forster, §9; `b66g_forms` with `mr_base` replaced by `c`. -/
def b66f_forms (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (m : ℕ) :
    Submodule ℂ (b66f_Coeff D) :=
  Submodule.span ℂ {q |
    (∀ a, AnalyticOnNhd ℂ (fun z => q a ((D.atlas.A a).symm (t.val, z)).2)
      (b66f_domain D t a)) ∧
    (∀ a b x, (t, x) ∈ (D.atlas.A a).source →
      (t, x) ∈ (D.atlas.A b).source →
      q a x = b66f_vertical D t a b x ^ m * q b x) ∧
    ∀ a x, (t, x) ∉ (D.atlas.A a).source → q a x = 0}
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (m : ℕ) :
    (0 : b66f_Coeff D) ∈ b66f_forms D t m := Submodule.zero_mem _

/-- Multiplication of differential coefficients.
Source: Forster, §9, tensor products of differentials; `b66g_product`. -/
def b66f_product (D : b65z_SharedFamily c g) (q r : b66f_Coeff D) : b66f_Coeff D :=
  fun a x => q a x * r a x
example (D : b65z_SharedFamily c g) (q : b66f_Coeff D) : b66f_product D q 0 = 0 := by
  funext a x
  exact mul_zero _

/-- Pullback coefficients of `m`-differentials along a deck transformation.
Source: Forster, §9, pullback of differentials; `b66g_pull`. -/
def b66f_pull (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (m : ℕ)
    (h : b4b_Group) : b66f_Coeff D →ₗ[ℂ] b66f_Coeff D where
  toFun q a x := if (t, x) ∈ (D.atlas.A a).source then
    q (t, h • x) (h • x) *
      deriv (b66f_deckCoordinate D t h a (t, h • x)) (D.atlas.A a (t, x)).2 ^ m
    else 0
  map_add' q r := by
    funext a x
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' r q := by
    funext a x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> ring
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (m : ℕ) (h : b4b_Group) :
    b66f_pull D t m h 0 = 0 := map_zero _

/-- The integral group-ring operator defining the primitive part.
Source: G32 v0.16, Definition 3.2; `b4b_projectorCoeff`; `b66g_projector`. -/
def b66f_projector (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    b66f_Coeff D →ₗ[ℂ] b66f_Coeff D :=
  letI := Fintype.ofFinite b4b_Group
  ∑ h : b4b_Group, (b4b_projectorCoeff h : ℂ) • b66f_pull D t 1 h
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : b66f_projector D t 0 = 0 :=
  map_zero _

/-- Primitive holomorphic forms on the fibre over `t`: the image of the group-ring operator.
Source: G32 v0.16, Definition 3.2; Birkenhake–Lange, §12.2; `b66g_primitiveForms`. -/
def b66f_primitiveForms (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    Submodule ℂ (b66f_Coeff D) :=
  b66f_forms D t 1 ⊓ LinearMap.range ((b66f_projector D t).comp (b66f_forms D t 1).subtype)
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    b66f_primitiveForms D t ≤ b66f_forms D t 1 := inf_le_left

/-- Reynolds average of quadratic coefficients.
Source: Serre, Linear Representations of Finite Groups, §2.2; `b66g_average`. -/
def b66f_average (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    b66f_Coeff D →ₗ[ℂ] b66f_Coeff D :=
  letI := Fintype.ofFinite b4b_Group
  (Fintype.card b4b_Group : ℂ)⁻¹ • ∑ h : b4b_Group, b66f_pull D t 2 h
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : b66f_average D t 0 = 0 :=
  map_zero _

/-- Residue sum of a local splitting contracted with a quadratic differential, each pole
evaluated in its centred chart.
Source: Forster, §19, residue theorem and Serre duality; `b66g_residueSum`. -/
def b66f_residueSum (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (S : Finset D.C) (v : b66f_Index D → ℂ → ℂ) (q : b66f_Coeff D) : ℂ :=
  ∑ x ∈ S, TauCeti.Contour.residue
    (fun z => v (t, x) z * q (t, x) ((D.atlas.A (t, x)).symm (t.val, z)).2)
    (D.atlas.A (t, x) (t, x)).2
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (v : b66f_Index D → ℂ → ℂ) (q : b66f_Coeff D) :
    b66f_residueSum D t ∅ v q = 0 := by simp [b66f_residueSum]

/-- Averaged products of primitive forms, as quadratic coefficients.
Source: Forster, §9; Serre, §2.2; `b66m_multiply`. -/
def b66f_multiply (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q r : b66f_primitiveForms D t) : b66f_Coeff D :=
  b66f_average D t (b66f_product D q.val r.val)
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (q r : b66f_primitiveForms D t) :
    b66f_multiply D t q r = b66f_average D t (b66f_product D q.val r.val) := rfl

/-- Residue multiplication array of three forms in each eigen-direction: row `3i + j` pairs
`q i * r j` with the splittings of the ten standard branch velocities.
Source: Griffiths, Periods II, §1; Forster, §17; `b66m_multiplicationMatrix`. -/
def b66f_multiplicationMatrix (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q r : Fin 3 → b66f_primitiveForms D t)
    (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ) :
    Matrix (Fin 9) (Fin 10) ℂ := fun i j =>
  b66f_residueSum D t (S j) (v j)
    (b66f_multiply D t (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1)
      (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2))
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q r : Fin 3 → b66f_primitiveForms D t)
    (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ) (i : Fin 9) (j : Fin 10) :
    b66f_multiplicationMatrix D t q r S v i j =
      b66f_residueSum D t (S j) (v j)
        (b66f_multiply D t (q ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).1)
          (r ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm i).2)) := rfl

/-- Tangent evaluations of chart coefficients, using the chart centred at the point.
Source: Forster, §9, coordinate expression of a differential; `b66m_chartForm`. -/
def b66f_chartForm (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q : b66f_Coeff D) : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ :=
  fun p => q (t, p.1.val.2) p.1.val.2 *
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun y : b65z_fibre c D.C t => (D.atlas.A (t, p.1.val.2) y.val).2) p.1 p.2)
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c) : b66f_chartForm D t 0 = 0 := by
  funext p
  exact zero_mul _

/-- Change a three-frame of primitive forms by the columns of a coordinate matrix.
Source: Mathlib `Module.Basis.sum_repr`; G32 v0.16, Subsection 5.5(6); `b66e_reframe`. -/
def b66f_reframe (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q : Fin 3 → b66f_primitiveForms D t) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (i : Fin 3) : b66f_primitiveForms D t := ∑ a, P a i • q a
example (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q : Fin 3 → b66f_primitiveForms D t) (i : Fin 3) :
    b66f_reframe D t q 1 i = q i := by
  simp [b66f_reframe, Matrix.one_apply]

/-- **The eigen-direction `k` of a chart coefficient** in the marking `m` at `s`: the
coefficient is the chart expression of a holomorphic form on the fibre over `t` whose periods on
the transported lattice are a combination of the three functionals
`x ↦ E(m x, b60_frame (period t) (k, i))`. For `k = 0` (`k = 1`) the frame vectors lie in the
`-1` (`+1`) eigenspace of `b60_omega`; these are the period normalizations of the two triples
in `b66m_polarized_matrix`.
Source: Griffiths, Periods II, §1; van Geemen, LNM 1594, §5.10; `b60_frame`;
`b66m_polarized_matrix` (the normalization of the two triples). -/
def b66f_direction (D : b65z_SharedFamily c g) (s t : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (k : Fin 2) : Set (b66f_Coeff D) :=
  {φ | ∃ ω : b3_HolForm ℂ (b65z_fibre c D.C t), ω.val = b66f_chartForm D t φ ∧
    ∃ a : Fin 3 → ℂ, ∀ x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s,
      (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val ω =
        ∑ i, a i * b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
          (b60_frame (b65z_period D s m t.val) (k, i))}

/-- Membership in a direction is the existence of the form and of its three coefficients. -/
example (D : b65z_SharedFamily c g) (s t : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice)) (k : Fin 2) (φ : b66f_Coeff D) :
    φ ∈ b66f_direction D s t m k ↔
      ∃ ω : b3_HolForm ℂ (b65z_fibre c D.C t), ω.val = b66f_chartForm D t φ ∧
        ∃ a : Fin 3 → ℂ, ∀ x,
          (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val ω =
            ∑ i, a i * b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b65z_period D s m t.val) (k, i)) := Iff.rfl

section retained
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- **Specialization.** At `mr_base`, for a retained family, the holomorphic and primitive forms
are those of stage 6c. -/
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ) :
    b66f_forms (b65z_ofRetained R) t m = b66g_forms R t m ∧
      b66f_primitiveForms (b65z_ofRetained R) t = b66g_primitiveForms R t := ⟨rfl, rfl⟩

/-- **Specialization.** At `mr_base` the residue array is that of stage 6d, entry by entry. -/
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : Fin 3 → b66g_primitiveForms R t)
    (S : Fin 10 → Finset R.C) (v : Fin 10 → b66k_Index R → ℂ → ℂ) :
    b66f_multiplicationMatrix (b65z_ofRetained R) t q r S v =
      b66m_multiplicationMatrix R t q r S v := rfl

/-- **Specialization.** At `mr_base` the Kodaira–Spencer cochains, coboundaries, chart forms
and frame changes are those of stages 6b–6e. -/
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (h : Fin 10 → ℂ)
    (v : b66k_Index R → ℂ → ℂ) (q : b66g_Coeff R)
    (f : Fin 3 → b66g_primitiveForms R t) (P : Matrix (Fin 3) (Fin 3) ℂ) :
    b66f_cocycle (b65z_ofRetained R) t h = b66k_cocycle R t h ∧
      b66f_boundary (b65z_ofRetained R) t v = b66k_boundary R t v ∧
      b66f_chartForm (b65z_ofRetained R) t q = b66m_chartForm R t q ∧
      b66f_reframe (b65z_ofRetained R) t f P = b66e_reframe R t f P :=
  ⟨rfl, rfl, rfl, rfl⟩

end retained

end HodgeLean.Foundations.Program
