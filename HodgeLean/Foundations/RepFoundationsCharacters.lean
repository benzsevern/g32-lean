import Mathlib
import HodgeLean.Foundations.RepFoundationsDefs

/-! # Representation foundations: character computations

Character identities for finite groups over `ℂ` used by the proofs of the representation
foundations: the conjugate of a character is its value at the inverse, dimensions of spaces of
intertwining maps as character inner products, the character criterion for simplicity, and the
multiplicity space `rfd_mult σ ρ` as a space of intertwining maps.
-/

noncomputable section

namespace HodgeLean.Foundations

open CategoryTheory
open scoped ComplexOrder Matrix

variable {G : Type} [Group G] [Fintype G]

/-- For a representation of a finite group, `conj (tr ρ(g)) = tr ρ(g⁻¹)`: the averaged Hermitian
matrix `Σ_h A(h)ᴴ A(h)` is invertible and `A(g)`-invariant, so `A(g⁻¹)` is conjugate to
`A(g)ᴴ`. -/
theorem rfd_star_trace {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) (g : G) :
    star (LinearMap.trace ℂ W (ρ g)) = LinearMap.trace ℂ W (ρ g⁻¹) := by
  classical
  let b := Module.finBasis ℂ W
  let A : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    fun h => LinearMap.toMatrix b b (ρ h)
  have hA : ∀ h k, A (h * k) = A h * A k := fun h k => by
    simp only [A, map_mul, LinearMap.toMatrix_mul]
  have hA1 : A 1 = 1 := by simp [A]
  let H := ∑ h, (A h)ᴴ * A h
  have hH : H.PosDef := by
    have : H = 1 + ∑ h ∈ Finset.univ.erase 1, (A h)ᴴ * A h := by
      simp only [H]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), hA1]
      simp
    rw [this]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum _ fun h _ => Matrix.posSemidef_conjTranspose_mul_self _)
  have hinv : (A g)ᴴ * H * A g = H := by
    simp only [H, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    simp [hA, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hu := hH.isUnit
  have hg : A g⁻¹ = H⁻¹ * (A g)ᴴ * H := by
    have h1 : A g * A g⁻¹ = 1 := by rw [← hA, mul_inv_cancel, hA1]
    calc A g⁻¹ = H⁻¹ * ((A g)ᴴ * H * A g) * A g⁻¹ := by
            rw [hinv, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), one_mul]
      _ = H⁻¹ * (A g)ᴴ * H := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one,
              ← Matrix.mul_assoc]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b]
  change star (A g).trace = (A g⁻¹).trace
  rw [hg, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
    Matrix.one_mul, Matrix.trace_conjTranspose]

theorem rfd_star_character (σ : FDRep ℂ G) (g : G) :
    star (σ.character g) = σ.character g⁻¹ :=
  rfd_star_trace σ.ρ g

/-- The dimension of the space of intertwining maps is the character inner product. -/
theorem rfd_finrank_intertwiningMap {V W : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (π : Representation ℂ G W) :
    (Module.finrank ℂ (Representation.IntertwiningMap ρ π) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, LinearMap.trace ℂ W (π g) * LinearMap.trace ℂ V (ρ g⁻¹) := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by simp)
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ π
  rw [Nat.card_eq_fintype_card] at h
  exact h.symm

/-- Simplicity in `FDRep ℂ G` is the condition that the intertwining endomorphisms form a line. -/
theorem rfd_simple_iff (σ : FDRep ℂ G) :
    Simple σ ↔ Module.finrank ℂ (Representation.IntertwiningMap σ.ρ σ.ρ) = 1 := by
  rw [FDRep.simple_iff_char_is_norm_one, ← Nat.cast_inj (R := ℂ),
    rfd_finrank_intertwiningMap, Nat.card_eq_fintype_card, Nat.cast_one]
  have hG : (Fintype.card G : ℂ) ≠ 0 := by simp
  constructor
  · intro h
    change _ * ∑ g, σ.character g * σ.character g⁻¹ = 1
    rw [h]; exact inv_mul_cancel₀ hG
  · intro h
    have := congrArg (fun z => (Fintype.card G : ℂ) * z) h
    simp only [← mul_assoc, mul_inv_cancel₀ hG, one_mul, mul_one] at this
    exact this

open scoped Classical in
/-- Orthogonality: between simple objects the intertwining maps have dimension one or zero. -/
theorem rfd_finrank_simple (σ τ : FDRep ℂ G) [Simple σ] [Simple τ] :
    (Module.finrank ℂ (Representation.IntertwiningMap σ.ρ τ.ρ) : ℂ) =
      if Nonempty (τ ≅ σ) then 1 else 0 := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by simp)
  rw [rfd_finrank_intertwiningMap, ← FDRep.char_orthonormal τ σ, Nat.card_eq_fintype_card]
  rfl

/-- Isomorphic objects have intertwining spaces of the same dimension. -/
theorem rfd_finrank_congr {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {τ τ' : FDRep ℂ G} (e : τ ≅ τ') (ρ : Representation ℂ G V) :
    Module.finrank ℂ (Representation.IntertwiningMap τ.ρ ρ) =
      Module.finrank ℂ (Representation.IntertwiningMap τ'.ρ ρ) := by
  rw [← Nat.cast_inj (R := ℂ), rfd_finrank_intertwiningMap, rfd_finrank_intertwiningMap]
  have h := FDRep.char_iso e
  have h' : ∀ g, LinearMap.trace ℂ τ (τ.ρ g) = LinearMap.trace ℂ τ' (τ'.ρ g) :=
    fun g => congrFun h g
  simp only [h']

/-- Between non-isomorphic simple objects every intertwining map vanishes. -/
theorem rfd_intertwining_eq_zero (σ τ : FDRep ℂ G) [Simple σ] [Simple τ]
    (h : ¬ Nonempty (τ ≅ σ)) (f : Representation.IntertwiningMap σ.ρ τ.ρ) : f = 0 := by
  classical
  have h0 : (Module.finrank ℂ (Representation.IntertwiningMap σ.ρ τ.ρ) : ℂ) = 0 := by
    simpa [h] using rfd_finrank_simple σ τ
  rw [Nat.cast_eq_zero, Module.finrank_zero_iff] at h0
  exact Subsingleton.elim _ _

/-- Schur's lemma for a simple object: every intertwining endomorphism is a scalar. -/
theorem rfd_intertwining_eq_smul (σ : FDRep ℂ G) [Simple σ]
    (f : Representation.IntertwiningMap σ.ρ σ.ρ) :
    ∃ c : ℂ, f = c • Representation.IntertwiningMap.id σ.ρ := by
  have h1 := (rfd_simple_iff σ).1 inferInstance
  have hid : Representation.IntertwiningMap.id σ.ρ ≠ 0 := by
    intro h0
    have : Subsingleton σ := ⟨fun v w => by
      have hv : v = 0 := congrArg (fun F : Representation.IntertwiningMap σ.ρ σ.ρ => F v) h0
      have hw : w = 0 := congrArg (fun F : Representation.IntertwiningMap σ.ρ σ.ρ => F w) h0
      rw [hv, hw]⟩
    have : Subsingleton (Representation.IntertwiningMap σ.ρ σ.ρ) :=
      ⟨fun F F' => Representation.IntertwiningMap.ext (LinearMap.ext fun v => Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h1
    exact zero_ne_one h1
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid).1 h1 f
  exact ⟨c, hc.symm⟩

/-- The multiplicity space is the space of intertwining maps `σ → V`. -/
def rfd_multEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (σ : FDRep ℂ G)
    (ρ : Representation ℂ G V) :
    rfd_mult σ ρ ≃ₗ[ℂ] Representation.IntertwiningMap σ.ρ ρ where
  toFun φ := ⟨φ.1, φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.toLinearMap, f.isIntertwining'⟩
  left_inv _ := rfl
  right_inv _ := rfl

end HodgeLean.Foundations
