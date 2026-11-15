import HodgeLean.Foundations.Program.PrymVariation
import HodgeLean.Foundations.Program.HurwitzFamilyMarked
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cMatchedTransverse

/-! # B6-3b–3c: integral operators on marked moving fibres

The definitions use integral singular homology and the actual product fibres.
No analytic structure or period comparison is selected.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

/-- The integral group-algebra operator on singular homology of a surface.
Source: Hatcher, *Algebraic Topology*, §2.1; Birkenhake–Lange, §12.2;
`b4b_projectorCoeff` and `b4b_projectorDenominator`. -/
def b63l_homologyOperator (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)) :
    b6m_H1 C →ₗ[ℤ] b6m_H1 C :=
  ∑ g : b4b_Group, b4b_projectorCoeff g •
    homologyMap ℤ 1 (TopCat.ofHom ⟨fun x : C ↦ g • x, hC g⟩)

example (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x)) :
    b63l_homologyOperator C hC 0 = 0 := map_zero _

/-- The inherited deck action keeps the moving base coordinate fixed.
Source: Harris–Morrison, *Moduli of Curves*, §1.G; `b6m_deck`. -/
instance b63l_fibreAction (b : Fin 10 → ℂ) (C : Type) [MulAction b4b_Group C]
    (t : b6t_polydisc b) : MulAction b4b_Group (b6m_Fibre b C t) where
  smul g q := ⟨(t, g • q.val.2), rfl⟩
  one_smul q := by
    apply Subtype.ext
    exact Prod.ext q.property.symm (one_smul _ _)
  mul_smul g h q := by
    apply Subtype.ext
    exact Prod.ext rfl (mul_smul g h q.val.2)

example (b : Fin 10 → ℂ) (C : Type) [MulAction b4b_Group C]
    (t : b6t_polydisc b) (g : b4b_Group) (q : b6m_Fibre b C t) :
    (g • q : b6m_Fibre b C t).val.2 = g • q.val.2 := rfl

/-- The same integral operator on each filled moving fibre.
Source: Harris–Morrison, §1.G; Birkenhake–Lange, §12.2; `b6m_deck`. -/
def b63l_fibreOperator (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) : b6m_H1 (b6m_Fibre b C t) →ₗ[ℤ] b6m_H1 (b6m_Fibre b C t) :=
  b63l_homologyOperator (b6m_Fibre b C t)
    (fun g ↦ (b6m_deck b b4b_Group C hC t g).continuous)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) : b63l_fibreOperator b C hC t 0 = 0 := map_zero _

/-- The exact integral image, without rational saturation or division by the denominator.
Source: Birkenhake–Lange, §12.2, image of an integral multiple of a rational projector. -/
abbrev b63l_fibreScaledImage (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) := LinearMap.range (b63l_fibreOperator b C hC t)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) :
    b63l_fibreScaledImage b C hC t = LinearMap.range (b63l_fibreOperator b C hC t) := rfl

/-- Saturation of an integral submodule in its ambient group.
Source: Bourbaki, *Algebra*, Ch. VII, §1, torsion submodules and localization. -/
def b63l_saturation {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (L : Submodule R M) : Submodule R M where
  carrier := {x | ∃ n : R, n ≠ 0 ∧ n • x ∈ L}
  zero_mem' := ⟨1, one_ne_zero, by simpa only [one_smul] using L.zero_mem⟩
  add_mem' := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    change (m * n) • (x + y) ∈ L
    rw [smul_add]
    apply L.add_mem
    · simpa only [mul_smul, smul_comm m n x] using L.smul_mem n hx
    · simpa only [mul_smul] using L.smul_mem m hy
  smul_mem' := by
    rintro a x ⟨n, hn, hx⟩
    refine ⟨n, hn, ?_⟩
    change n • (a • x) ∈ L
    rw [smul_comm n a x]
    exact L.smul_mem a hx

example {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M] (L : Submodule R M) :
    L ≤ b63l_saturation L := fun x hx ↦ ⟨1, one_ne_zero, by simpa using hx⟩

/-- The primitive fibre lattice is the saturation of the scaled image in integral homology.
Source: Birkenhake–Lange, §12.2, the lattice of the image abelian subvariety. -/
abbrev b63l_fibreLattice (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) := b63l_saturation (b63l_fibreScaledImage b C hC t)

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) : Module ℤ (b63l_fibreLattice b C hC t) := inferInstance

/-- The actual filled fibre at each parameter of a subset of the moving polydisc.
Source: Harris–Morrison, §1.G; `b6m_Fibre`. -/
abbrev b63l_parameterFibre (b : Fin 10 → ℂ) (C : Type)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :=
  b6m_Fibre b C ⟨t.val, hV t.property⟩

example (b : Fin 10 → ℂ) (C : Type) (V : Set (Fin 10 → ℂ))
    (hV : V ⊆ b6t_polydisc b) (t : V) :
    b63l_parameterFibre b C V hV t = b6m_Fibre b C ⟨t.val, hV t.property⟩ := rfl

/-- The primitive integral lattice on every actual parameter fibre, indexed by that parameter.
Source: Birkenhake–Lange, §12.2; Harris–Morrison, §1.G. -/
abbrev b63l_parameterLattice (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    Submodule ℤ (b6m_H1 (b63l_parameterFibre b C V hV t)) :=
  b63l_fibreLattice b C hC ⟨t.val, hV t.property⟩

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b) (t : V) :
    b63l_parameterLattice b C hC V hV t =
      b63l_fibreLattice b C hC ⟨t.val, hV t.property⟩ := rfl

/-- The rational extension of the saturated lattice's ambient inclusion.
Source: Bourbaki, *Algebra*, Ch. VII, §1, localization of modules. -/
def b63l_fibreRationalInclusion (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) :=
  letI : Module ℤ (b63l_fibreLattice b C hC t) := (b63l_fibreLattice b C hC t).module
  (b63l_fibreLattice b C hC t).subtype.baseChange ℚ

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) : b63l_fibreRationalInclusion b C hC t 0 = 0 := map_zero _

/-- The normalized rational operator attached to the printed matrix coefficient.
Source: G32 v0.16, Definition 3.2 with v = e₀; Serre, §2.2. -/
def b63l_fibreProjector (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C]
    [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) :=
  (b4b_projectorDenominator : ℚ)⁻¹ • (b63l_fibreOperator b C hC t).baseChange ℚ

example (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [MulAction b4b_Group C]
    (hC : ∀ g : b4b_Group, Continuous (fun x : C ↦ g • x))
    (t : b6t_polydisc b) : b63l_fibreProjector b C hC t 0 = 0 := map_zero _

/-- The saturated period lattice in the ambient Jacobian lattice.
Source: Birkenhake–Lange, §12.2. -/
abbrev b63l_periodLattice (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C] :=
  b63l_saturation (b4_groupEnd ℂ (C := C) b4b_projectorCoeff).toIntLinearMap.range

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C] :
    Module ℤ (b63l_periodLattice C) := inferInstance

/-- The ambient period filtration pulled back to the saturated lattice.
Source: Birkenhake–Lange, §5.3 and §12.2. -/
def b63l_periodF (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C] : Submodule ℂ (ℂ ⊗[ℤ] b63l_periodLattice C) :=
  (b3_periodF ℂ C).comap ((b63l_periodLattice C).subtype.baseChange ℂ)

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C] :
    (0 : ℂ ⊗[ℤ] b63l_periodLattice C) ∈ b63l_periodF C := Submodule.zero_mem _

/-- The original integral pairing restricted to the saturated period lattice.
Source: Birkenhake–Lange, §5.3, induced polarization. -/
def b63l_periodQ (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C] (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) :=
  Q.compl₁₂ (b63l_periodLattice C).subtype (b63l_periodLattice C).subtype

example (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ C)) (x y : b63l_periodLattice C) :
    b63l_periodQ C Q x y = Q x.val y.val := rfl

/-- Doubling a nonzero rank-one lattice changes its exact range but not its saturation.
Source: Bourbaki, *Algebra*, Ch. VII, §1. -/
example :
    (1 : ℤ) ∈ b63l_saturation (LinearMap.range (2 • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) ∧
    (1 : ℤ) ∉ LinearMap.range (2 • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) ∧
    (∀ x : ℤ, (∀ y : ℤ, x * y = 0) → x = 0) := by
  refine ⟨⟨2, by norm_num, ⟨1, by simp⟩⟩, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    change 2 * x = 1 at hx
    omega
  · intro x hx
    simpa using hx 1

end HodgeLean.Foundations.Program
