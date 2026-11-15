import HodgeLean.Foundations.Program.PrymFamilyAssembly

/-! # B6-3g, part 4: data for the `positive` field of the Prym family

For a complex abelian variety `X` with lattice `Λ_X = b2_abelianLattice X` (its `H₁(X(ℂ), ℤ)`)
and period equivalence `P = abelianPeriodEquiv X : H¹(X(ℂ); ℚ) ≃ (Λ_X →+ ℚ)`:

* `b63g4_periodEval X l`, the evaluation `x ↦ P x l` at a lattice vector: the image of `l` in
  `(H¹)^∨ = H₁ ⊗ ℚ`, where the form `B_ω(a, b) = b (contract ω a)` of a 2-vector `ω` lives;
* `b63g4_column X Q l = P⁻¹ (Q (l, ·))`, the cohomology class of the row `Q (l, ·)` of an
  integral form `Q`, and its complexification `b63g4_cplxColumn X Q : ℂ ⊗[ℤ] Λ_X → ℂ ⊗[ℚ] H¹`.

These are the maps through which the original form `Q` on homology is compared with `B_ω` and with
the inverse-contraction form `polarizationForm` on cohomology for `ω` the 2-vector of
`latticeClassHQ X Q`. Only data are defined here, plus one elementary theorem with a proof (the
negated 2-vector is nondegenerate when the original is). No definition selects a witness from an
open statement, and none is a proposition. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- **Evaluation at a lattice vector**, the linear form `x ↦ P x l` on `H¹(X(ℂ); ℚ)`, with
`P = abelianPeriodEquiv X`: the image of `l ∈ H₁(X(ℂ), ℤ)` in `(H¹)^∨ = H₁ ⊗ ℚ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H¹(X, ℤ) = Hom(Λ, ℤ)`);
Hatcher, *Algebraic Topology*, §3.1 (the evaluation pairing); `abelianPeriodEquiv`. -/
def b63g4_periodEval (l : b2_abelianLattice X) : Module.Dual ℚ (HQ X 1) where
  toFun x := abelianPeriodEquiv X x l
  map_add' x y := by simp
  map_smul' c x := by simp

example (l : b2_abelianLattice X) (x : HQ X 1) :
    b63g4_periodEval X l x = abelianPeriodEquiv X x l := rfl

/-- **The row class of an integral form**: `l ↦ P⁻¹ (Q (l, ·))`, the class in `H¹(X(ℂ); ℚ)`
whose periods are the values `Q (l, m)`. It is the flat map `u ↦ Q (u, ·)` of `Q` read in
cohomology.
Source: Birkenhake–Lange, §1.1 and §4.1 (the form `Q` on `Λ` and the dual polarization);
`abelianPeriodEquiv`, `b2b_flat`. -/
def b63g4_column (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) :
    b2_abelianLattice X →+ HQ X 1 :=
  AddMonoidHom.mk' (fun l ↦ (abelianPeriodEquiv X).symm
      ((Int.castAddHom ℚ).comp (b2_bilinToAddHom Q l)))
    (fun l m ↦ by
      rw [← map_add]
      congr 1
      ext x
      simp [b2_bilinToAddHom])

example (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) (l m : b2_abelianLattice X) :
    abelianPeriodEquiv X (b63g4_column X Q l) m = (Q l m : ℚ) := by
  simp [b63g4_column, b2_bilinToAddHom]

/-- **The complexified row map** `ℂ ⊗[ℤ] Λ_X → ℂ ⊗[ℚ] H¹(X(ℂ); ℚ)`, `c ⊗ l ↦ c ⊗ P⁻¹ (Q (l, ·))`:
the complex-linear extension of `b63g4_column`, between the complex homology where the period
filtration `b2_abelianF X` lives and the complex cohomology where the Hodge pieces live.
Source: Bourbaki, *Algèbre*, ch. II, §5 (extension of scalars); Mathlib
`LinearMap.liftBaseChange`; `b2bpol_musical` (the same map on `Hom(Λ, ℚ)`). -/
def b63g4_cplxColumn (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) :
    ℂ ⊗[ℤ] b2_abelianLattice X →ₗ[ℂ] ℂ ⊗[ℚ] HQ X 1 :=
  LinearMap.liftBaseChange ℂ
    (((TensorProduct.mk ℚ ℂ (HQ X 1) 1).restrictScalars ℤ).comp
      (b63g4_column X Q).toIntLinearMap)

example (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) (c : ℂ) (l : b2_abelianLattice X) :
    b63g4_cplxColumn X Q (c ⊗ₜ l) = c ⊗ₜ b63g4_column X Q l := by
  simp [b63g4_cplxColumn, TensorProduct.smul_tmul']

/-- **The negated 2-vector is nondegenerate when the original is**: `contract (-ω) =
-contract ω` is bijective with `contract ω`. This supplies the nondegeneracy witness that
`PolarizationPositive` needs for the class `-η`, the opposite sign.
Source: `Symplectic.IsNondegenerate` (bijectivity of `contract`); linearity of
`polarizationVec`. -/
theorem b63g4_neg_nondegenerate {η : HQ X 2}
    (h : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) η)) :
    IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) (-η)) := by
  have hv : polarizationVec (torusCohomology_cupProductOf X) (-η) =
      -polarizationVec (torusCohomology_cupProductOf X) η := by
    simp [polarizationVec]
  rw [IsNondegenerate, hv, map_neg]
  have hn : ⇑(-contract (polarizationVec (torusCohomology_cupProductOf X) η)) =
      Neg.neg ∘ ⇑(contract (polarizationVec (torusCohomology_cupProductOf X) η)) := by
    ext φ
    simp
  rw [hn]
  exact (Function.Involutive.bijective neg_neg).comp h

example {η : HQ X 2}
    (h : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) η)) :
    Function.Injective (contract (polarizationVec (torusCohomology_cupProductOf X) (-η))) :=
  (b63g4_neg_nondegenerate X h).1

/-- Two nondegeneracy witnesses for equal classes give the same `PolarizationPositive`.
Source: proof irrelevance; `PolarizationPositive`. -/
theorem b63g4_positive_congr {η η' : HQ X 2} (e : η = η')
    (h : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) η))
    (h' : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) η'))
    (hp : PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) h) :
    PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) h' := by
  subst e
  exact hp

example {η : HQ X 2}
    (h h' : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf X) η))
    (hp : PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) h) :
    PolarizationPositive (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
      (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) h' :=
  b63g4_positive_congr X rfl h h' hp

/-- **The sign value on the standard elliptic data**: for `v = e₀ + i e₁ ∈ b2_stdF` and
`Q = b2_stdForm`, `Q_ℂ(v, v̄) = -2i`, so `Re (i · Q_ℂ(v, v̄)) = 2`.
Source: Birkenhake–Lange, §4.1 (the elliptic curve `ℂ ⧸ (ℤ + iℤ)` and its Riemann form);
`b2a_stdVec_conj`, `b2a_stdForm_apply`. -/
theorem b63g4_std_value :
    (Complex.I * b2_stdForm.baseChange ℂ b2a_stdVec (b2_conj _ b2a_stdVec)).re = 2 := by
  rw [b2a_stdVec_conj]
  simp only [b2a_stdVec, map_add, LinearMap.add_apply, LinearMap.BilinForm.baseChange_tmul,
    b2a_stdForm_apply]
  simp
  norm_num

example : b2a_stdVec ∈ b2_stdF := Submodule.mem_span_singleton_self _

end HodgeLean.Foundations.Program
