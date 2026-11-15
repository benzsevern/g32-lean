import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # Projective bundles and tautological lines for singular Chern classes

Projectivization uses actual fibre lines and the quotient topology of nonzero
vectors. The tautological fibre is the line itself inside the original fibre.
HC no distance; AV milestone no distance. -/

noncomputable section
open Bundle TopologicalSpace
namespace HodgeLean.Foundations.BundleResolution

/-- Actual rank-k complex bundle data, with no characteristic-class fields.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6. -/
structure I1ComplexBundle (B : Type) [TopologicalSpace B] (k : ℕ) where
  fibre : B → Type
  addGroup : ∀ b, AddCommGroup (fibre b)
  module : ∀ b, Module ℂ (fibre b)
  fibreTopology : ∀ b, TopologicalSpace (fibre b)
  totalTopology : TopologicalSpace (TotalSpace (Fin k → ℂ) fibre)
  fiberBundle : letI := fibreTopology; letI := totalTopology
    FiberBundle (Fin k → ℂ) fibre
  vectorBundle : letI := addGroup; letI := module; letI := fibreTopology
    letI := totalTopology; letI := fiberBundle
    VectorBundle ℂ (Fin k → ℂ) fibre

attribute [instance] I1ComplexBundle.addGroup I1ComplexBundle.module
  I1ComplexBundle.fibreTopology I1ComplexBundle.totalTopology
  I1ComplexBundle.fiberBundle I1ComplexBundle.vectorBundle

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)

/-- Fibrewise projective space of lines in the actual complex bundle.
Source: Fulton, Intersection Theory, §3.2, projective bundle construction. -/
abbrev i1_projectiveBundle := Σ b, Projectivization ℂ (E.fibre b)

/-- Quotient map from nonzero total vectors to their fibre lines.
Source: Fulton, Intersection Theory, §3.2. -/
def i1_projectiveQuotient (v : {v : TotalSpace (Fin k → ℂ) E.fibre // v.2 ≠ 0}) :
    i1_projectiveBundle E := ⟨v.1.proj, Projectivization.mk ℂ v.1.2 v.2⟩

/-- Quotient topology on the actual projective bundle.
Source: Bott–Tu, complex projective bundle construction. -/
def i1_projectiveTopology : TopologicalSpace (i1_projectiveBundle E) :=
  TopologicalSpace.coinduced (i1_projectiveQuotient E) inferInstance

/-- The tautological fibre is the actual line, rather than its linear dual.
Source: Fulton, Intersection Theory, §3.2, tautological subbundle. -/
abbrev i1_projectiveLineFibre (z : i1_projectiveBundle E) : Type := z.2.submodule

/-- Subspace topology on a tautological fibre.
Source: Bott–Tu, tautological line bundle on projective space. -/
def i1_projectiveLineFibreTopology (z : i1_projectiveBundle E) :
    TopologicalSpace (i1_projectiveLineFibre E z) := inferInstance

/-- Tautological total topology induced by the base and original vector inclusion.
Source: Bott–Tu, tautological subbundle topology. -/
def i1_projectiveLineTotalTopology :
    TopologicalSpace (TotalSpace (Fin 1 → ℂ) (i1_projectiveLineFibre E)) :=
  letI := i1_projectiveTopology E
  TopologicalSpace.induced (fun z : TotalSpace (Fin 1 → ℂ) (i1_projectiveLineFibre E) =>
    (z.proj, (⟨z.proj.1, z.2.val⟩ : TotalSpace (Fin k → ℂ) E.fibre))) inferInstance

example (b : B) (v : E.fibre b) (hv : v ≠ 0) :
    (i1_projectiveQuotient E ⟨⟨b, v⟩, hv⟩).1 = b := rfl

example (z : i1_projectiveBundle E) (v : i1_projectiveLineFibre E z) :
    (v + v).val = v.val + v.val := rfl

example (z : i1_projectiveBundle E) (v : i1_projectiveLineFibre E z) :
    ((2 : ℂ) • v).val = (2 : ℂ) • v.val := rfl

example : letI := i1_projectiveTopology E
    Continuous (i1_projectiveQuotient E) := continuous_coinduced_rng

example (b : B) (v : E.fibre b) (hv : v ≠ 0) :
    v ∈ (i1_projectiveQuotient E ⟨⟨b, v⟩, hv⟩).2.submodule := by
  change v ∈ (Projectivization.mk ℂ v hv).submodule
  rw [Projectivization.submodule_mk]
  exact Submodule.mem_span_singleton_self v

example (z : i1_projectiveBundle E) :
    letI := i1_projectiveLineFibreTopology E z
    Continuous (Subtype.val : i1_projectiveLineFibre E z → E.fibre z.1) :=
  continuous_subtype_val

example (z : i1_projectiveBundle E) (v : i1_projectiveLineFibre E z) :
    (-v).val = -v.val := rfl

end HodgeLean.Foundations.BundleResolution
