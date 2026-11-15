import HodgeLean.Foundations.Program.PeriodDerivative
import HodgeLean.Foundations.Program.RelativeFrameAssembly

/-! Chart cochains for the retained family. HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan

/-- Indices of the retained total atlas.
Source: `rf7_HurwitzAtlas.A`. -/
abbrev b66k_Index (R : rf8_SharedFamily) := b6t_polydisc mr_base × R.C
example (R : rf8_SharedFamily) (a : b66k_Index R) : a = a := rfl

/-- Fibre-coordinate domain of a retained chart.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2. -/
def b66k_domain (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a : b66k_Index R) : Set ℂ := {z | (t.val, z) ∈ (R.atlas.A a).target}
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) (a : b66k_Index R)
    (z : ℂ) : z ∈ b66k_domain R t a ↔ (t.val, z) ∈ (R.atlas.A a).target := Iff.rfl

/-- Transition from chart a to chart b, including its parameter coordinate.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, transition-function construction. -/
def b66k_transition (R : rf8_SharedFamily) (a b : b66k_Index R)
    (u : (Fin 10 → ℂ) × ℂ) : ℂ := (R.atlas.A b ((R.atlas.A a).symm u)).2
example (R : rf8_SharedFamily) (a b : b66k_Index R)
    (u : (Fin 10 → ℂ) × ℂ) : b66k_transition R a b u =
      (R.atlas.A b ((R.atlas.A a).symm u)).2 := rfl

/-- Ambient one-cochains, expressed in the target chart.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, tangent-valued Čech cochains. -/
abbrev b66k_Cochain (R : rf8_SharedFamily) :=
  b66k_Index R → b66k_Index R → R.C → ℂ
example (R : rf8_SharedFamily) : (0 : b66k_Cochain R) = 0 := rfl

/-- Change of vertical tangent coordinates at a fibre point.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, chain rule on chart overlaps. -/
def b66k_vertical (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (x : R.C) : ℂ :=
  fderiv ℂ (b66k_transition R a b) (R.atlas.A a (t, x)) (0, 1)
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (a b : b66k_Index R) (x : R.C) : b66k_vertical R t a b x =
      fderiv ℂ (b66k_transition R a b) (R.atlas.A a (t, x)) (0, 1) := rfl

/-- Coboundary of chartwise coefficients, extended by zero off overlaps.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2; d(v)ab = D(fab)va - vb. -/
def b66k_boundary (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (v : b66k_Index R → ℂ → ℂ) : b66k_Cochain R := fun a b x =>
  if (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source then
    b66k_vertical R t a b x * v a (R.atlas.A a (t, x)).2 -
      v b (R.atlas.A b (t, x)).2 else 0
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66k_boundary R t 0 = 0 := by
  funext a b x
  simp [b66k_boundary]

/-- Span of coboundaries of holomorphic local vector fields.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, tangent sheaf coboundaries. -/
def b66k_boundaries (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule ℂ (b66k_Cochain R) :=
  Submodule.span ℂ {c | ∃ v : b66k_Index R → ℂ → ℂ,
    (∀ a, AnalyticOnNhd ℂ (v a) (b66k_domain R t a)) ∧ c = b66k_boundary R t v}
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66k_Cochain R) ∈ b66k_boundaries R t := Submodule.zero_mem _

/-- Ambient cochain quotient. Arbitrary members need not be cocycle classes.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, cochains modulo coboundaries. -/
abbrev b66k_Quotient (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :=
  b66k_Cochain R ⧸ b66k_boundaries R t
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66k_Quotient R t) = 0 := rfl

/-- Parameter derivative at fixed source coordinate.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, Kodaira–Spencer cocycle. -/
def b66k_cocycle (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (Fin 10 → ℂ) →ₗ[ℂ] b66k_Cochain R where
  toFun h a b x := if (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source then
    fderiv ℂ (b66k_transition R a b) (R.atlas.A a (t, x)) (h, 0) else 0
  map_add' h k := by
    funext a b x
    simp only [Pi.add_apply]
    split_ifs with hmem
    · simpa only [Prod.mk_add_mk, add_zero] using map_add (fderiv ℂ (b66k_transition R a b) (R.atlas.A a (t, x)))
        (h, (0 : ℂ)) (k, (0 : ℂ))
    · exact (add_zero 0).symm
  map_smul' c h := by
    funext a b x
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs with hmem
    · simpa only [Prod.smul_mk, smul_zero] using
        (map_smul (fderiv ℂ (b66k_transition R a b) (R.atlas.A a (t, x))) c (h, 0))
    · exact (smul_zero c).symm

example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66k_cocycle R t 0 = 0 := map_zero _

/-- Kodaira–Spencer map represented in the ambient chart quotient. The holomorphic
cocycle law is a separate statement, rather than a premise in this definition.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2; FGP, §2. -/
def b66k_kodairaSpencer (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (Fin 10 → ℂ) →ₗ[ℂ] b66k_Quotient R t :=
  (b66k_boundaries R t).mkQ.comp (b66k_cocycle R t)
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66k_kodairaSpencer R t 0 = 0 := map_zero _

/-- Domain of the common refinement of a chart and a deck translate of another.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, refinement of Čech covers. -/
def b66k_refinementDomain (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) : Set ℂ :=
  {z | (t.val, z) ∈ (R.atlas.A a).target ∧
    (t, g • ((R.atlas.A a).symm (t.val, z)).2) ∈ (R.atlas.A b).source}
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) :
    b66k_refinementDomain R t g a b ⊆ b66k_domain R t a := fun _ h => h.1

/-- Deck map written in two retained fibre coordinates.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, functoriality of tangent cocycles. -/
def b66k_deckCoordinate (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ) : ℂ :=
  (R.atlas.A b (t, g • ((R.atlas.A a).symm (t.val, z)).2)).2
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (g : b4b_Group) (a b : b66k_Index R) (z : ℂ) :
    b66k_deckCoordinate R t g a b z =
      (R.atlas.A b (t, g • ((R.atlas.A a).symm (t.val, z)).2)).2 := rfl

/-- Čech differential, with coefficients in the last chart and zero off triple overlaps.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, tangent sheaf Čech complex. -/
def b66k_differential (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66k_Cochain R →ₗ[ℂ]
      (b66k_Index R → b66k_Index R → b66k_Index R → R.C → ℂ) where
  toFun u a b c x :=
    if (t, x) ∈ (R.atlas.A a).source ∩ (R.atlas.A b).source ∩ (R.atlas.A c).source then
      u a c x - u b c x - b66k_vertical R t b c x * u a b x else 0
  map_add' u v := by
    funext a b c x
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' k u := by
    funext a b c x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> ring
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    b66k_differential R t 0 = 0 := map_zero _

/-- Holomorphic one-cochains, extended by zero off overlaps. The span construction
supplies the module structure without choosing bases or cohomology representatives.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, holomorphic tangent-valued cochains. -/
def b66k_holomorphicCochains (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule ℂ (b66k_Cochain R) :=
  Submodule.span ℂ {u |
    (∀ a b, AnalyticOnNhd ℂ
      (fun z => u a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 a b)) ∧
    ∀ a b x, (t, x) ∉ (R.atlas.A a).source ∩ (R.atlas.A b).source → u a b x = 0}
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66k_Cochain R) ∈ b66k_holomorphicCochains R t := Submodule.zero_mem _

/-- Concrete Čech H¹ as the image of holomorphic cocycles in the cochain quotient.
This is the subquotient Z¹/(Z¹ ∩ B¹), expressed without a chosen splitting.
No identification with derived sheaf cohomology is part of the definition.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, Čech cohomology of the tangent sheaf. -/
def b66k_cechH1 (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    Submodule ℂ (b66k_Quotient R t) :=
  (b66k_holomorphicCochains R t ⊓ LinearMap.ker (b66k_differential R t)).map
    (b66k_boundaries R t).mkQ
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    (0 : b66k_Quotient R t) ∈ b66k_cechH1 R t := Submodule.zero_mem _

end HodgeLean.Foundations.Program
