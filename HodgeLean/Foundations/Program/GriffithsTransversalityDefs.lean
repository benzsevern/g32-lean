import HodgeLean.Foundations.Program.KodairaSpencer
import HodgeLean.Ported.TauCeti.TauCeti.Analysis.Contour.Residue.Basic

/-! Retained-chart differentials, scalar Čech classes and transported periods.
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

/-- Coefficients of differentials in the retained charts.
Source: Forster, Lectures on Riemann Surfaces, §9. -/
abbrev b66g_Coeff (R : rf8_SharedFamily) := b66k_Index R → R.C → ℂ
example (R : rf8_SharedFamily) : (0 : b66g_Coeff R) = 0 := rfl

/-- Holomorphic m-differentials, with their tensor transition law and zero extension.
The span gives the linear structure; all three defining conditions are linear.
Source: Forster, Lectures on Riemann Surfaces, §9. -/
def b66g_forms (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ) :
    Submodule ℂ (b66g_Coeff R) :=
  Submodule.span ℂ {q |
    (∀ a, AnalyticOnNhd ℂ (fun z => q a ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_domain R t a)) ∧
    (∀ a b x, (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source →
      q a x = b66k_vertical R t a b x ^ m * q b x) ∧
    ∀ a x, (t, x) ∉ (R.atlas.A a).source → q a x = 0}
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ) :
    (0 : b66g_Coeff R) ∈ b66g_forms R t m := Submodule.zero_mem _

/-- Multiplication of differential coefficients before restriction to global sections.
Source: Forster, Lectures on Riemann Surfaces, §9, tensor products of differentials. -/
def b66g_product (R : rf8_SharedFamily) (q r : b66g_Coeff R) : b66g_Coeff R :=
  fun a x => q a x * r a x
example (R : rf8_SharedFamily) (q : b66g_Coeff R) : b66g_product R q 0 = 0 := by
  funext a x
  exact mul_zero _

/-- Pullback coefficients, evaluated using the retained chart centred at the image point.
Only the restriction to global differentials has a geometric group action.
Source: Forster, §9, pullback of differentials; Kodaira, §4.2, common refinements. -/
def b66g_pull (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ)
    (g : b4b_Group) : b66g_Coeff R →ₗ[ℂ] b66g_Coeff R where
  toFun q a x := if (t, x) ∈ (R.atlas.A a).source then
    q (t, g • x) (g • x) *
      deriv (b66k_deckCoordinate R t g a (t, g • x)) (R.atlas.A a (t, x)).2 ^ m
    else 0
  map_add' q r := by
    funext a x
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c q := by
    funext a x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> ring
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ) (g : b4b_Group) :
    b66g_pull R t m g 0 = 0 := map_zero _

/-- The same integral group-ring operator used to define the primitive Prym lattice.
Source: G32 v0.16, Definition 3.2; b4b_projectorCoeff. -/
def b66g_projector (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_Coeff R →ₗ[ℂ] b66g_Coeff R :=
  letI := Fintype.ofFinite b4b_Group
  ∑ g : b4b_Group, (b4b_projectorCoeff g : ℂ) • b66g_pull R t 1 g
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_projector R t 0 = 0 := map_zero _

/-- Primitive holomorphic forms, obtained from the specified group-ring image.
Source: G32 v0.16, Definition 3.2; Birkenhake–Lange, §12.2. -/
def b66g_primitiveForms (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule ℂ (b66g_Coeff R) :=
  b66g_forms R t 1 ⊓ LinearMap.range
    ((b66g_projector R t).comp (b66g_forms R t 1).subtype)
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_primitiveForms R t ≤ b66g_forms R t 1 := inf_le_left

/-- Reynolds average of quadratic coefficients.
Source: Serre, Linear Representations of Finite Groups, §2.2, averaging projector. -/
def b66g_average (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_Coeff R →ₗ[ℂ] b66g_Coeff R :=
  letI := Fintype.ofFinite b4b_Group
  (Fintype.card b4b_Group : ℂ)⁻¹ • ∑ g : b4b_Group, b66g_pull R t 2 g
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_average R t 0 = 0 := map_zero _

/-- Scalar coboundary, extended by zero away from overlaps.
Source: Forster, §12, the additive Cousin problem. -/
def b66g_scalarBoundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v : b66k_Index R → ℂ → ℂ) : b66k_Cochain R := fun a b x =>
  if (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source then
    v a (R.atlas.A a (t, x)).2 - v b (R.atlas.A b (t, x)).2 else 0
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66g_scalarBoundary R t 0 = 0 := by
  funext a b x
  simp [b66g_scalarBoundary]

/-- Holomorphic scalar boundaries.
Source: Forster, §12, Čech description of H¹(O). -/
def b66g_scalarBoundaries (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule ℂ (b66k_Cochain R) :=
  Submodule.span ℂ {u | ∃ v : b66k_Index R → ℂ → ℂ,
    (∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) ∧
      u = b66g_scalarBoundary R t v}
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66k_Cochain R) ∈ b66g_scalarBoundaries R t := Submodule.zero_mem _

/-- Holomorphic scalar cocycles, with zero extension off overlaps.
Source: Forster, §12, additive Čech cocycles. -/
def b66g_scalarCycles (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule ℂ (b66k_Cochain R) :=
  Submodule.span ℂ {u |
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 a b)) ∧
    (∀ a b x, (t, x) ∉ (R.atlas.A a).source ∩ (R.atlas.A b).source → u a b x = 0) ∧
    ∀ a b c x, (t, x) ∈ (R.atlas.A a).source →
      (t, x) ∈ (R.atlas.A b).source → (t, x) ∈ (R.atlas.A c).source →
      u a c x = u b c x + u a b x}
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66k_Cochain R) ∈ b66g_scalarCycles R t := Submodule.zero_mem _

/-- Ambient scalar quotient.
Source: Forster, §12. -/
abbrev b66g_scalarQuotient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :=
  b66k_Cochain R ⧸ b66g_scalarBoundaries R t
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66g_scalarQuotient R t) = 0 := rfl

/-- The concrete scalar H¹, as the image of holomorphic cocycles.
Source: Forster, §12, Čech cohomology. -/
def b66g_H1O (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule ℂ (b66g_scalarQuotient R t) :=
  (b66g_scalarCycles R t).map (b66g_scalarBoundaries R t).mkQ
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66g_scalarQuotient R t) ∈ b66g_H1O R t := Submodule.zero_mem _

/-- Contraction of tangent cochains with a differential in the target chart.
Source: Griffiths, Periods II, §1, cup product followed by contraction. -/
def b66g_contract (R : rf8_SharedFamily) (q : b66g_Coeff R)
    (u : b66k_Cochain R) : b66k_Cochain R := fun a b x => q b x * u a b x
example (R : rf8_SharedFamily) (q : b66g_Coeff R) : b66g_contract R q 0 = 0 := by
  funext a b x
  exact mul_zero _

/-- Residue sum of a meromorphic local splitting contracted with a quadratic differential.
Each pole is evaluated in its retained centred chart; no pairing is chosen here.
Source: Forster, §19, residue theorem and Serre duality. -/
def b66g_residueSum (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset R.C) (v : b66k_Index R → ℂ → ℂ) (q : b66g_Coeff R) : ℂ :=
  ∑ x ∈ S, TauCeti.Contour.residue
    (fun z => v (t, x) z * q (t, x) ((R.atlas.A (t, x)).symm (t.val, z)).2)
    (R.atlas.A (t, x) (t, x)).2
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v : b66k_Index R → ℂ → ℂ) (q : b66g_Coeff R) :
    b66g_residueSum R t ∅ v q = 0 := by simp [b66g_residueSum]

/-- Full homology of a retained fibre.
Source: b6m_H1, singular integral homology. -/
abbrev b66g_Homology (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :=
  b6m_H1 (rf8_fibre R.C t)
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    AddCommGroup (b66g_Homology R t) := inferInstance

/-- Period coordinates of a relative form on flatly transported integral cycles.
Source: Griffiths, Periods II, §1; b63e_periodFunction. -/
def b66g_periods (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    {n : ℕ} (B : Module.Basis (Fin n) ℤ (b66g_Homology R s))
    {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (u : Fin 10 → ℂ) : Fin n → ℂ := fun i =>
  b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
    R.P θ s (B i) u
example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base) {n : ℕ}
    (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) {U : Set (Fin 10 → ℂ)}
    (θ : b63e_relForm mr_base R.C (b6t_polydisc mr_base) (Subset.refl _) U)
    (u : Fin 10 → ℂ) (i : Fin n) : b66g_periods R s B θ u i =
      b63e_periodFunction mr_base R.C (b6t_polydisc mr_base) (Subset.refl _)
        R.P θ s (B i) u := rfl

/-- The actual holomorphic period subspace in these flat cohomology coordinates.
This is dual to the kernel filtration used by rf8_transportedFamily.
Source: Griffiths, Periods II, §1; b3_periodF. -/
def b66g_periodSubspace (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    {n : ℕ} (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ {v | ∃ ω : b3_HolForm ℂ (rf8_fibre R.C t),
    v = fun i => (R.P t (b6m_H1Equiv (b6m_transport mr_base R.C s t) (B i))).val ω}
example (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base) {n : ℕ}
    (B : Module.Basis (Fin n) ℤ (b66g_Homology R s)) :
    (0 : Fin n → ℂ) ∈ b66g_periodSubspace R s t B := Submodule.zero_mem _

end HodgeLean.Foundations.Program
