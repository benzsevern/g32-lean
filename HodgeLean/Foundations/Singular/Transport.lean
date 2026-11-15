import HodgeLean.Foundations.Singular.GradedComm
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CohomologyZero

/-! # Normalized transport of singular cup products

The graded vector spaces are parameters so this file can be instantiated on `HQ`
without importing RealDefs or repeatedly unfolding sheaf cohomology.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Singular

variable (Y : TopCat.{0})

/-- On a path-connected space the cup unit spans degree-zero cohomology.
Source: upstream `Other/AlgebraicTopology/Singular/CohomologyZero.lean` at `2ead713`,
`exists_smul_cohomologyUnitZero`, and Hatcher, *Algebraic Topology*, §3.2 (cup unit). -/
theorem exists_smul_unit [PathConnectedSpace Y]
    (a : AlgebraicTopology.Singular.Cohomology ℚ Y 0) :
    ∃ r : ℚ, r • unit Y = a := by
  obtain ⟨s, hs⟩ := AlgebraicTopology.Singular.exists_smul_cohomologyUnitZero ℚ Y (unit Y)
  obtain ⟨t, ht⟩ := AlgebraicTopology.Singular.exists_smul_cohomologyUnitZero ℚ Y a
  have h : s ≠ 0 := by
    intro h
    apply unit_ne_zero (R := ℚ) Y
    rw [← hs, h, zero_smul]
  refine ⟨t / s, ?_⟩
  rw [← hs, smul_smul, div_mul_cancel₀ t h, ht]

example [PathConnectedSpace Y] (a : AlgebraicTopology.Singular.Cohomology ℚ Y 0) :
    ∃ r : ℚ, r • unit Y = a := exists_smul_unit Y a

variable {V : ℕ → Type} [∀ n, AddCommGroup (V n)] [∀ n, Module ℚ (V n)]
variable (e : ∀ n, V n ≃ₗ[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y n)

private def normalizationScalar [PathConnectedSpace Y] (u : V 0) : ℚ :=
  Classical.choose (exists_smul_unit Y (e 0 u))

private theorem normalizationScalar_spec [PathConnectedSpace Y] (u : V 0) :
    normalizationScalar Y e u • unit Y = e 0 u :=
  Classical.choose_spec (exists_smul_unit Y (e 0 u))

private theorem normalizationScalar_ne_zero [PathConnectedSpace Y] (u : V 0) (hu : u ≠ 0) :
    normalizationScalar Y e u ≠ 0 := by
  intro h
  have hh := normalizationScalar_spec Y e u
  rw [h, zero_smul] at hh
  exact hu ((e 0).injective (hh.symm.trans (map_zero _).symm))

/-- Rescale every degree of a comparison by the inverse of the nonzero scalar
which is its value on the chosen degree-zero unit. No naturality is asserted.
Source: linear transport and upstream `Other/AlgebraicTopology/Singular/CohomologyZero.lean`
at `2ead713`, `exists_smul_cohomologyUnitZero`. -/
def normalizedEquiv [PathConnectedSpace Y] (u : V 0) (hu : u ≠ 0) (n : ℕ) :
    V n ≃ₗ[ℚ] AlgebraicTopology.Singular.Cohomology ℚ Y n where
  toFun a := (normalizationScalar Y e u)⁻¹ • e n a
  invFun a := normalizationScalar Y e u • (e n).symm a
  map_add' a b := by simp [smul_add]
  map_smul' a b := by
    simp only [map_smul, smul_smul, RingHom.id_apply]
    rw [mul_comm]
  left_inv a := by simp [smul_smul, normalizationScalar_ne_zero Y e u hu]
  right_inv a := by simp [smul_smul, normalizationScalar_ne_zero Y e u hu]

/-- The rescaled comparison preserves the specified unit.
Source: the defining scalar identity in `normalizedEquiv`. -/
@[simp] theorem normalizedEquiv_unit [PathConnectedSpace Y] (u : V 0) (hu : u ≠ 0) :
    normalizedEquiv Y e u hu 0 u = unit Y := by
  change (normalizationScalar Y e u)⁻¹ • e 0 u = _
  rw [← normalizationScalar_spec Y e u, smul_smul,
    inv_mul_cancel₀ (normalizationScalar_ne_zero Y e u hu), one_smul]

example [PathConnectedSpace Y] (u : V 0) (hu : u ≠ 0) :
    normalizedEquiv Y e u hu 0 u = unit Y := normalizedEquiv_unit Y e u hu

/-- Pull back the singular cup product along a graded linear equivalence.
Bilinearity is encoded by the two linear-map arrows.
Source: Hatcher, *Algebraic Topology*, §3.2, transported by linear equivalences. -/
def transportedCup {i j k : ℕ} (h : i + j = k) : V i →ₗ[ℚ] V j →ₗ[ℚ] V k where
  toFun a := (e k).symm.toLinearMap ∘ₗ cup Y h (e i a) ∘ₗ (e j).toLinearMap
  map_add' a b := by ext; simp
  map_smul' a b := by ext; simp

/-- The comparison intertwines the transported and singular products.
Source: the definition of `transportedCup`. -/
@[simp] theorem map_transportedCup {i j k : ℕ} (h : i + j = k) (a : V i) (b : V j) :
    e k (transportedCup Y e h a b) = cup Y h (e i a) (e j b) := by
  simp [transportedCup]

example {i j k : ℕ} (h : i + j = k) (a : V i) (b : V j) :
    e k (transportedCup Y e h a b) = cup Y h (e i a) (e j b) :=
  map_transportedCup Y e h a b

/-- A unit-preserving comparison transports the left unit law.
Source: Hatcher, *Algebraic Topology*, §3.2, left unit law. -/
theorem transportedCup_one (u : V 0) (hu : e 0 u = unit Y) {j : ℕ} (a : V j) :
    transportedCup Y e (Nat.zero_add j) u a = a := by
  apply (e j).injective
  simp [hu, one_cup]

/-- A unit-preserving comparison transports the right unit law.
Source: Hatcher, *Algebraic Topology*, §3.2, right unit law. -/
theorem transportedCup_unit (u : V 0) (hu : e 0 u = unit Y) {i : ℕ} (a : V i) :
    transportedCup Y e (Nat.add_zero i) a u = a := by
  apply (e i).injective
  simp [hu, cup_one]

/-- Associativity survives graded linear transport.
Source: Hatcher, *Algebraic Topology*, §3.2, associativity. -/
theorem transportedCup_assoc {i j l ij jl k : ℕ} (hij : i + j = ij) (hjl : j + l = jl)
    (h₁ : ij + l = k) (h₂ : i + jl = k) (a : V i) (b : V j) (c : V l) :
    transportedCup Y e h₁ (transportedCup Y e hij a b) c =
      transportedCup Y e h₂ a (transportedCup Y e hjl b c) := by
  apply (e k).injective
  simpa only [map_transportedCup] using cup_assoc Y hij hjl h₁ h₂ (e i a) (e j b) (e l c)

/-- Graded commutativity survives graded linear transport.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11. -/
theorem transportedCup_comm {i j k : ℕ} (h : i + j = k) (h' : j + i = k)
    (a : V i) (b : V j) :
    transportedCup Y e h' b a = (-1 : ℚ) ^ (i * j) • transportedCup Y e h a b := by
  apply (e k).injective
  simpa only [map_transportedCup, map_smul] using cup_comm_graded Y h h' (e i a) (e j b)

end HodgeLean.Foundations.Singular
