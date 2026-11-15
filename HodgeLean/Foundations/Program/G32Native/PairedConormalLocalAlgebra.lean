import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Local algebra for a paired conormal modification

In a node chart the conormal map multiplies the residual direction by
its local equation and fixes the remaining directions.
-/

namespace HodgeLean.Foundations.Program.G32Native

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The elementary modification in the residual direction.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7, pp. 16–17,
local node presentation of the conormal map. -/
def pairedConormalInclusion (x : R) : R × M →ₗ[R] R × M where
  toFun v := (x * v.1, v.2)
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, mul_add, Prod.mk_add_mk]
  map_smul' a v := by
    apply Prod.ext
    · exact mul_left_comm x a v.1
    · rfl

/-- The residual quotient in the same node chart.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7, pp. 16–17. -/
def pairedConormalResidue (x : R) : R × M →ₗ[R] R ⧸ Ideal.span {x} :=
  (Ideal.span {x}).mkQ.comp (LinearMap.fst R R M)

/-- A non-zero-divisor gives the exact elementary modification sequence.
This verifies the node chart algebra; it does not identify a global sheaf.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7, pp. 16–17. -/
theorem paired_conormal_local_exact (x : R)
    (hx : ∀ a : R, x * a = 0 → a = 0) :
    Function.Injective (pairedConormalInclusion (M := M) x) ∧
    Function.Exact (pairedConormalInclusion (M := M) x) (pairedConormalResidue x) ∧
    Function.Surjective (pairedConormalResidue (M := M) x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    apply Prod.ext
    · have he : x * a.1 = x * b.1 := congrArg Prod.fst h
      exact sub_eq_zero.mp (hx (a.1 - b.1) (by rw [mul_sub, he, sub_self]))
    · simpa only [pairedConormalInclusion, LinearMap.coe_mk, AddHom.coe_mk] using congrArg Prod.snd h
  · intro v
    change Ideal.Quotient.mk (Ideal.span {x}) v.1 = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨(a, v.2), Prod.ext (by simpa only [pairedConormalInclusion, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using ha) rfl⟩
    · rintro ⟨a, ha⟩
      exact ⟨a.1, by simpa only [pairedConormalInclusion, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using congrArg Prod.fst ha⟩
  · intro z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨(a, 0), ha⟩

#print axioms paired_conormal_local_exact

end HodgeLean.Foundations.Program.G32Native
