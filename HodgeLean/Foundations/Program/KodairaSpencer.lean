import HodgeLean.Foundations.Program.KodairaSpencerProofs

/-! Kodaira–Spencer in the concrete retained-atlas Čech model: implication from
shared branched-cover geometry to holomorphic cocycles, branch coordinates,
deck invariance and injectivity. The target is represented inside the ambient
cochain quotient; arbitrary quotient elements are not called cohomology classes.
No period derivative, Serre duality or codifferential basis comparison is supplied.
HC no distance; AV milestone no distance. -/
noncomputable section
open Set Filter Topology Manifold
namespace HodgeLean.Foundations.Program
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- The parameter derivatives satisfy the tangent-valued Čech cocycle law.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2,
chain rule for transition functions. -/
theorem b66k_cocycle_law (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (a b c : b66k_Index R) (x : R.C)
    (ha : (t, x) ∈ (R.atlas.A a).source)
    (hb : (t, x) ∈ (R.atlas.A b).source)
    (hc : (t, x) ∈ (R.atlas.A c).source) :
    b66k_cocycle R t h a c x = b66k_cocycle R t h b c x +
      b66k_vertical R t b c x * b66k_cocycle R t h a b x :=
  b66k_cocycle_law_aux R t h a b c x ha hb hc

example := @b66k_cocycle_law

/-- The cocycle coefficients are holomorphic on every overlap.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2; holomorphic derivatives of analytic transitions. -/
theorem b66k_cocycle_holomorphic (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (a b : b66k_Index R) :
    AnalyticOnNhd ℂ
      (fun z => b66k_cocycle R t h a b ((R.atlas.A a).symm (t.val, z)).2)
      (b66k_refinementDomain R t 1 a b) :=
  b66k_cocycle_holomorphic_aux R t h a b

example := @b66k_cocycle_holomorphic

/-- In a moving branch chart z = t_i + w^n and a free z-chart, the cocycle
is h_i times the local branch-moving vector field; its vertical factor is n w^(n-1).
Source: `rf7_HurwitzAtlas.hmark`, `rf7_HurwitzAtlas.hfree`; Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2. -/
theorem b66k_branch_coordinate (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (i : Fin 10) (a b : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 = b6_branch mr_base (Fin.castAdd 3 i))
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source)
    (hxb : (t, x) ∈ (R.atlas.A b).source) :
    b66k_cocycle R t h a b x = h i ∧
      b66k_vertical R t a b x =
        (R.atlas.n a.2 : ℂ) * (R.atlas.A a (t, x)).2 ^ (R.atlas.n a.2 - 1) :=
  b66k_branch_coordinate_aux R t h i a b x ha hb hxa hxb

example := @b66k_branch_coordinate

/-- Deck pullback changes the cocycle by a holomorphic coboundary on the
common refinement. This is invariant-class equality without choosing a deck-stable cover.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2, functoriality; FGP, §2, equivariant deformations. -/
theorem b66k_deck_invariant (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (h : Fin 10 → ℂ) (g : b4b_Group) :
    ∃ v : b66k_Index R → b66k_Index R → ℂ → ℂ,
      (∀ a b, AnalyticOnNhd ℂ (v a b) (b66k_refinementDomain R t g a b)) ∧
      ∀ (a b c d : b66k_Index R) (x : R.C),
        (t, x) ∈ (R.atlas.A a).source →
        (t, x) ∈ (R.atlas.A c).source →
        (t, g • x) ∈ (R.atlas.A b).source →
        (t, g • x) ∈ (R.atlas.A d).source →
        b66k_cocycle R t h b d (g • x) -
          deriv (b66k_deckCoordinate R t g c d) (R.atlas.A c (t, x)).2 *
            b66k_cocycle R t h a c x =
          b66k_vertical R t b d (g • x) * v a b (R.atlas.A a (t, x)).2 -
            v c d (R.atlas.A c (t, x)).2 :=
  b66k_deck_invariant_aux R t h g

example := @b66k_deck_invariant

/-- The normalized ten branch directions have independent Kodaira–Spencer classes.
Source: Kodaira, Complex Manifolds and Deformation of Complex Structures, §4.2; FGP, §2, Hurwitz deformations with three fixed marks.
An infinitesimally trivial cover deformation induces a sphere vector field vanishing
at 0, 1 and infinity, hence zero. -/
theorem b66k_injective (R : rf8_SharedFamily) (t : b6t_polydisc mr_base) :
    ∃ K : (Fin 10 → ℂ) →ₗ[ℂ] b66k_cechH1 R t,
      (b66k_cechH1 R t).subtype.comp K = b66k_kodairaSpencer R t ∧
        Function.Injective K :=
  b66k_injective_aux R t

example := @b66k_injective

/-- Checked geometry exists, with nonidentity peripheral rotation and twelve lattice directions.
No statement in this draft is used to select the witness. -/
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

/-- Ten genuine input directions, independent of any new open statement. -/
example : Module.finrank ℂ (Fin 10 → ℂ) = 10 ∧
    (Pi.single (0 : Fin 10) (1 : ℂ) : Fin 10 → ℂ) ≠ 0 := by
  constructor
  · simp
  · intro h
    have := congrFun h 0
    norm_num at this

/-- Three distinct fixed marks and all moving marks are distinct on every parameter. -/
example (t : b6t_polydisc mr_base) : Function.Injective (b6_branch t.val) :=
  (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.2 t.property

/-- The normalized polydisc includes nonconstant branch movement. -/
example : ∃ t ∈ b6t_polydisc mr_base, t 0 ≠ mr_base 0 := by
  have hr : 0 < b6t_radius mr_base := (b6t_discs mr_base mr_base_mem_chart).1
  refine ⟨Function.update mr_base 0 (mr_base 0 + (b6t_radius mr_base / 2 : ℝ)), ?_, ?_⟩
  · intro i
    rw [Metric.mem_ball]
    by_cases h : i = 0
    · subst h
      simp only [Function.update_self, dist_self_add_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ b6t_radius mr_base / 2)]
      linarith
    · simp [Function.update_of_ne h, hr]
  · simp only [Function.update_self, ne_eq, add_eq_left]
    exact_mod_cast (by positivity : (b6t_radius mr_base / 2 : ℝ) ≠ 0)

/-- The standard branch direction moves precisely the corresponding branch coordinate. -/
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (i j : Fin 10) (a b : b66k_Index R) (x : R.C)
    (ha : R.atlas.f a.2 = b6_branch mr_base (Fin.castAdd 3 j))
    (hb : R.atlas.f b.2 ∉ Set.range (b6_branch mr_base))
    (hxa : (t, x) ∈ (R.atlas.A a).source)
    (hxb : (t, x) ∈ (R.atlas.A b).source) :
    b66k_cocycle R t (Pi.single i 1) a b x = if j = i then 1 else 0 := by
  rw [(b66k_branch_coordinate R t (Pi.single i 1) j a b x ha hb hxa hxb).1]
  simp [Pi.single_apply, eq_comm]

/-- Chain check: every future contraction of these Čech classes has the exact
nine-output, ten-input column convention of `g32r_PeriodMap.codiff`.
This check does not identify such a contraction with the period derivative. -/
example (R : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (K : (Fin 10 → ℂ) →ₗ[ℂ] b66k_cechH1 R t)
    (D : b66k_cechH1 R t →ₗ[ℂ] (Fin 9 → ℂ))
    (i : Fin 9) (j : Fin 10) :
    LinearMap.toMatrix' (D.comp K) i j = D (K (Pi.single j 1)) i := rfl

end HodgeLean.Foundations.Program
