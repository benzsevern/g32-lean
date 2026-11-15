import HodgeLean.Adapters.DegreeOneSplitDefs

/-! # Proof obligations for the degree-one lattice split (FROZEN) -/

noncomputable section

namespace HodgeLean.Adapters

private theorem smul_decomp {g : ℕ} (c : ℂ) (v : Fin g → ℂ) :
    c • v = c.re • v + c.im • (Complex.I • v) := by
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

/-- Complex-linear functionals as the holomorphic summand. -/
private def holomorphicEquiv (g : ℕ) :
    ((Fin g → ℂ) →ₗ[ℂ] ℂ) ≃ₗ[ℂ] degreeOneLatticeHolomorphic g where
  toFun φ := ⟨φ.restrictScalars ℝ, fun v => by simp⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun f :=
    { toFun := f
      map_add' := f.1.map_add
      map_smul' := fun c v => by
        change (f : DegreeOneLatticeDual g) (c • v) = c * (f : DegreeOneLatticeDual g) v
        rw [smul_decomp, map_add, LinearMap.map_smul, LinearMap.map_smul, f.2 v,
          Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  left_inv φ := rfl
  right_inv f := rfl

/-- Coordinatewise conjugation as a real-linear involution of `ℂ^g`. -/
private def coordConj (g : ℕ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun v i := star (v i)
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

private theorem coordConj_coordConj {g : ℕ} (v : Fin g → ℂ) : coordConj g (coordConj g v) = v := by
  ext i; simp [coordConj]

private theorem coordConj_I {g : ℕ} (v : Fin g → ℂ) :
    coordConj g (Complex.I • v) = -(Complex.I • coordConj g v) := by
  ext i; simp [coordConj]

/-- Precomposition with coordinate conjugation exchanges the two summands. -/
private def antiholomorphicEquiv (g : ℕ) :
    degreeOneLatticeAntiholomorphic g ≃ₗ[ℂ] degreeOneLatticeHolomorphic g where
  toFun f := ⟨f.1 ∘ₗ coordConj g, fun v => by
    simp only [LinearMap.comp_apply, coordConj_I, map_neg]
    rw [f.2]
    ring⟩
  map_add' f h := rfl
  map_smul' c f := rfl
  invFun h := ⟨h.1 ∘ₗ coordConj g, fun v => by
    simp only [LinearMap.comp_apply, coordConj_I, map_neg]
    rw [h.2]
    ring⟩
  left_inv f := by
    ext v
    simp [coordConj_coordConj]
  right_inv h := by
    ext v
    simp [coordConj_coordConj]

theorem spec_H1_lattice_split_aux (g : ℕ) :
    degreeOneLatticeHolomorphic g ⊔ degreeOneLatticeAntiholomorphic g = ⊤ := by
  refine eq_top_iff.mpr fun f _ => ?_
  let J : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := Complex.I • LinearMap.id
  have hJ : ∀ v, J v = Complex.I • v := fun v => rfl
  have hJJ : ∀ v, J (J v) = -v := fun v => by
    rw [hJ, hJ, smul_smul, Complex.I_mul_I, neg_one_smul]
  let h : DegreeOneLatticeDual g := (2⁻¹ : ℂ) • (f - Complex.I • (f ∘ₗ J))
  let a : DegreeOneLatticeDual g := (2⁻¹ : ℂ) • (f + Complex.I • (f ∘ₗ J))
  have hh : h ∈ degreeOneLatticeHolomorphic g := fun v => by
    have := hJJ v
    simp only [h, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, ← hJ, this,
      map_neg, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have ha : a ∈ degreeOneLatticeAntiholomorphic g := fun v => by
    have := hJJ v
    simp only [a, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, ← hJ, this,
      map_neg, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hf : f = h + a := by
    refine LinearMap.ext fun v => ?_
    simp only [h, a, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      smul_eq_mul]
    ring
  rw [hf]
  exact Submodule.add_mem_sup hh ha

theorem spec_H1_lattice_disjoint_aux (g : ℕ) :
    Disjoint (degreeOneLatticeHolomorphic g) (degreeOneLatticeAntiholomorphic g) := by
  rw [Submodule.disjoint_def]
  intro f hh ha
  refine LinearMap.ext fun v => ?_
  have h1 := hh v
  have h2 := ha v
  rw [h1] at h2
  have h3 : (2 * Complex.I) * f v = 0 := by linear_combination h2
  simpa [Complex.I_ne_zero] using h3

theorem spec_H1_lattice_holomorphic_dimension_aux (g : ℕ) :
    Module.finrank ℂ (degreeOneLatticeHolomorphic g) = g := by
  rw [← (holomorphicEquiv g).finrank_eq]
  simp

theorem spec_H1_lattice_antiholomorphic_dimension_aux (g : ℕ) :
    Module.finrank ℂ (degreeOneLatticeAntiholomorphic g) = g := by
  rw [(antiholomorphicEquiv g).finrank_eq, spec_H1_lattice_holomorphic_dimension_aux]

theorem spec_H1_lattice_conjugation_exchanges_aux (g : ℕ) :
    (∀ f ∈ degreeOneLatticeHolomorphic g,
      degreeOneLatticeConjugate g f ∈ degreeOneLatticeAntiholomorphic g) ∧
    (∀ f ∈ degreeOneLatticeAntiholomorphic g,
      degreeOneLatticeConjugate g f ∈ degreeOneLatticeHolomorphic g) := by
  constructor
  · intro f hf v
    change star (f (Complex.I • v)) = -Complex.I * star (f v)
    rw [hf v, star_mul']
    simp
  · intro f hf v
    change star (f (Complex.I • v)) = Complex.I * star (f v)
    rw [hf v, star_mul']
    simp

end HodgeLean.Adapters
