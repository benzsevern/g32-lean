import HodgeLean.Foundations.Program.PrymVariationCentre

/-! # B6-3e: relative differentials and transported period data

Data on the actual parameter fibres over a subset of the moving polydisc. A relative
holomorphic differential is a fibrewise holomorphic form whose coefficient in every
parameter chart of the total space is jointly analytic. The transported filtration and
pairing live on the saturated singular lattice of one fixed parameter. No frame, period
comparison or lattice isomorphism is selected from a statement.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Relative holomorphic differentials of the moving family over `V ∩ U`: families of fibrewise
holomorphic forms on all of `V` whose coefficient against the vertical coordinate of every
parameter chart of the total space is analytic, jointly in the parameter and the fibre
coordinate, over `V ∩ U`. Off `U` only fibrewise holomorphy is required.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1, relative holomorphic forms of a family; Forster, *Lectures on Riemann Surfaces*, §9. -/
def b63e_relForm (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (U : Set (Fin 10 → ℂ)) :
    Submodule ℂ ((t : V) → TangentBundle 𝓘(ℂ, ℂ) (b63l_parameterFibre b C V hV t) → ℂ) where
  carrier := {θ | (∀ t, θ t ∈ b3_HolForm ℂ (b63l_parameterFibre b C V hV t)) ∧
    ∀ φ ∈ atlas ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C),
      (∀ y ∈ φ.source, (φ y).1 = y.1.val) →
      ∃ a : (Fin 10 → ℂ) × ℂ → ℂ, AnalyticOn ℂ a (φ.target ∩ Prod.fst ⁻¹' (V ∩ U)) ∧
        ∀ (t : V) (x : b63l_parameterFibre b C V hV t), t.val ∈ U → x.val ∈ φ.source →
          ∀ v : TangentSpace 𝓘(ℂ, ℂ) x,
            θ t ⟨x, v⟩ = a (φ x.val) * (show ℂ from
              mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
                (fun z : b63l_parameterFibre b C V hV t ↦ (φ z.val).2) x v)}
  add_mem' := by
    rintro θ η ⟨hθ, hθ'⟩ ⟨hη, hη'⟩
    refine ⟨fun t ↦ (b3_HolForm ℂ _).add_mem (hθ t) (hη t), fun φ hφ hp ↦ ?_⟩
    obtain ⟨a, ha, haθ⟩ := hθ' φ hφ hp
    obtain ⟨c, hc, hcη⟩ := hη' φ hφ hp
    refine ⟨a + c, ha.add hc, fun t x hu hx v ↦ ?_⟩
    show θ t ⟨x, v⟩ + η t ⟨x, v⟩ = _
    rw [haθ t x hu hx v, hcη t x hu hx v]
    exact (add_mul _ _ _).symm
  zero_mem' := ⟨fun t ↦ (b3_HolForm ℂ _).zero_mem, fun φ _ _ ↦
    ⟨0, analyticOn_const, fun t x _ _ v ↦ (zero_mul _).symm⟩⟩
  smul_mem' := by
    rintro k θ ⟨hθ, hθ'⟩
    refine ⟨fun t ↦ (b3_HolForm ℂ _).smul_mem k (hθ t), fun φ hφ hp ↦ ?_⟩
    obtain ⟨a, ha, haθ⟩ := hθ' φ hφ hp
    refine ⟨fun p ↦ k * a p, analyticOn_const.mul ha, fun t x hu hx v ↦ ?_⟩
    show k * θ t ⟨x, v⟩ = _
    rw [haθ t x hu hx v]
    exact (mul_assoc _ _ _).symm

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)] :
    (0 : (t : V) → TangentBundle 𝓘(ℂ, ℂ) (b63l_parameterFibre b C V hV t) → ℂ) ∈
      b63e_relForm b C V hV Set.univ := Submodule.zero_mem _

/-- The holomorphic form on one fibre given by a relative differential.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1, restriction of relative forms to fibres. -/
def b63e_relFormAt (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm b C V hV U) (t : V) :
    b3_HolForm ℂ (b63l_parameterFibre b C V hV t) :=
  ⟨θ.val t, θ.property.1 t⟩

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)] (t : V) :
    b63e_relFormAt b C V hV (0 : b63e_relForm b C V hV Set.univ) t = 0 := rfl

open scoped Classical in
/-- The period of a relative differential on the transport of a fixed integral class, as a
function of the parameter; it is set to zero off `V`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1, periods over a locally constant family of cycles; `b6m_transport`. -/
def b63e_periodFunction (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    {U : Set (Fin 10 → ℂ)} (θ : b63e_relForm b C V hV U) (s : V)
    (x : b6m_H1 (b63l_parameterFibre b C V hV s)) : (Fin 10 → ℂ) → ℂ :=
  fun u ↦ if h : u ∈ V then
    (P ⟨u, h⟩ (b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩ ⟨u, hV h⟩) x)).val
      (b63e_relFormAt b C V hV θ ⟨u, h⟩)
  else 0

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t))
    (U : Set (Fin 10 → ℂ)) (θ : b63e_relForm b C V hV U) (s : V)
    (x : b6m_H1 (b63l_parameterFibre b C V hV s)) (u : Fin 10 → ℂ) (hu : u ∉ V) :
    b63e_periodFunction b C V hV P θ s x u = 0 := by
  exact dite_eq_right_of_eq_false (eq_false hu)

/-- The saturated singular lattice at `s`, transported to the fibre at `t` and mapped to its
periods by the given integral comparison at `t`.
Source: Harris–Morrison, *Moduli of Curves*, §1.G; Birkenhake–Lange, §12.2;
`b6m_period_comparison`. -/
def b63e_transportMap (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s t : V) :
    b63l_parameterLattice b C hC V hV s →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t) :=
  ((P t).toAddMonoidHom.comp ((b6m_H1Equiv (b6m_transport b C ⟨s.val, hV s.property⟩
    ⟨t.val, hV t.property⟩)).toAddMonoidHom.comp
      (b63l_parameterLattice b C hC V hV s).subtype.toAddMonoidHom)).toIntLinearMap

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s t : V) :
    b63e_transportMap b C hC V hV P s t 0 = 0 := map_zero _

/-- The period filtration at `t`, pulled back to the complexified saturated lattice at `s`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1; Birkenhake–Lange, §5.3 and §12.2; `b3_periodF`. -/
def b63e_transportedF (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s t : V) :
    Submodule ℂ (ℂ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) :=
  (b3_periodF ℂ (b63l_parameterFibre b C V hV t)).comap
    ((b63e_transportMap b C hC V hV P s t).baseChange ℂ)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (P : (t : V) → b6m_H1 (b63l_parameterFibre b C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV t)) (s t : V) :
    (0 : ℂ ⊗[ℤ] b63l_parameterLattice b C hC V hV s) ∈
      b63e_transportedF b C hC V hV P s t := Submodule.zero_mem _

/-- The original pairing at `s`, pulled back to the saturated singular lattice at `s` by the
given integral period comparison.
Source: Birkenhake–Lange, §5.3, induced polarization; `b63l_periodQ`. -/
def b63e_singularQ (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))) :
    LinearMap.BilinForm ℤ (b63l_parameterLattice b C hC V hV s) :=
  Q.compl₁₂ (Ps.toAddMonoidHom.comp
      (b63l_parameterLattice b C hC V hV s).subtype.toAddMonoidHom).toIntLinearMap
    (Ps.toAddMonoidHom.comp (b63l_parameterLattice b C hC V hV s).subtype.toAddMonoidHom).toIntLinearMap

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (s : V)
    [ChartedSpace ℂ (b63l_parameterFibre b C V hV s)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV s)]
    (Ps : b6m_H1 (b63l_parameterFibre b C V hV s) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre b C V hV s))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre b C V hV s)))
    (x y : b63l_parameterLattice b C hC V hV s) :
    b63e_singularQ b C hC V hV s Ps Q x y = Q (Ps x.val) (Ps y.val) := rfl

/-- The complexified lattice vector with the given coordinates in an integral basis.
Source: Bourbaki, *Algebra*, Ch. II, §7, extension of scalars of a free module. -/
def b63e_coordVector {ι : Type} [Fintype ι] {M : Type*} [AddCommGroup M]
    (B : Module.Basis ι ℤ M) (c : ι → ℂ) : ℂ ⊗[ℤ] M :=
  ∑ j, c j ⊗ₜ[ℤ] B j

example {ι : Type} [Fintype ι] {M : Type*} [AddCommGroup M] (B : Module.Basis ι ℤ M) :
    b63e_coordVector B 0 = 0 := by
  simp [b63e_coordVector]

/-- The constant lattice local system on `V` with fibre the saturated singular lattice at `s`,
made free and finite by a supplied integral basis. Product transport trivializes the integral
local system of the actual fibres over the polydisc.
Source: Voisin, *Hodge Theory I*, ch. 9, constant local systems; `b6m_homology_trivialization`. -/
def b63e_localSystem (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V) (s : V)
    {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s)) :
    b2_LatticeLocalSystem (⟨V, hVo⟩ : TopologicalSpace.Opens (Fin 10 → ℂ)) :=
  @b2_constLocalSystem _ _ (b63l_parameterLattice b C hC V hV s) _
    (Module.Free.of_basis B) (Module.Finite.of_basis B)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (hVo : IsOpen V) (s : V)
    {ι : Type} [Fintype ι] (B : Module.Basis ι ℤ (b63l_parameterLattice b C hC V hV s))
    (t : (⟨V, hVo⟩ : TopologicalSpace.Opens (Fin 10 → ℂ))) :
    (b63e_localSystem b C hC V hV hVo s B).fiber t = b63l_parameterLattice b C hC V hV s := rfl

end HodgeLean.Foundations.Program
