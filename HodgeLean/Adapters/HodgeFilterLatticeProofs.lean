import HodgeLean.Adapters.HodgeDegreeOne
import HodgeLean.Adapters.DegreeOneLattice

/-! # Proof obligations for the Hodge filtration against the lattice summand

One obligation per statement of `HodgeLean.Adapters.HodgeFilterLattice`, all proved; two parallel
provers wrote them (statements 1-4 and 5-8).

* The conjugate filtration: `bettiDeRhamHQ_sigmaQ` with `sigmaQ_involutive` and
  `mem_conjHodgeFiltrationComplexSubmodule`.
* The abelian statements: `spec_bettiDeRhamIso_abelian` makes `bettiDeRhamHQ X 1` a linear
  isomorphism, so pulling back along it preserves dimension and intersections; the lattice side is
  `spec_complexH1_split`, `spec_complexH1_dimension` and `spec_complexH1_conjugation_exchanges`;
  `Submodule.eq_of_le_of_finrank_le` for the equality; `finiteBetti_abelian` for finiteness of
  `ℂ ⊗[ℚ] HQ X 1`; stage 4a (`spec_deRhamHodgePiece_one_isInternal_of_finrank`,
  `spec_finrank_hodgeFiltration_one_of_isInternal`) for the decomposition. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_comap_conjHodgeFiltration_eq_map_sigmaQ_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] (p : ℤ) (n : ℕ) :
    (conjHodgeFiltrationComplexSubmodule X p (n : ℤ)).comap (bettiDeRhamHQ X n) =
      ((F^p H_dR^(n : ℤ)(X)).comap (bettiDeRhamHQ X n)).map (HodgeBlocks.sigmaQ (HQ X n)) := by
  ext y
  have key : y ∈ ((F^p H_dR^(n : ℤ)(X)).comap (bettiDeRhamHQ X n)).map
      (HodgeBlocks.sigmaQ (HQ X n)) ↔
      HodgeBlocks.sigmaQ (HQ X n) y ∈ (F^p H_dR^(n : ℤ)(X)).comap (bettiDeRhamHQ X n) :=
    ⟨by rintro ⟨x, hx, rfl⟩; simpa using hx, fun hy => ⟨_, hy, by simp⟩⟩
  rw [key]
  simp only [Submodule.mem_comap, mem_conjHodgeFiltrationComplexSubmodule, bettiDeRhamHQ_sigmaQ]

theorem spec_disjoint_hodgeFiltration_one_of_le_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    Disjoint (F^1 H_dR^((1 : ℕ) : ℤ)(X))
      (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)) := by
  have hβ := (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective 1
  rw [Submodule.disjoint_def]
  intro α h1 h2
  obtain ⟨ω, rfl⟩ := hβ.2 α
  have hω : ω ∈ (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) := h1
  have hc : ω ∈ (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)).comap
      (bettiDeRhamHQ X 1) := h2
  rw [spec_comap_conjHodgeFiltration_eq_map_sigmaQ_aux X 1 1] at hc
  obtain ⟨ν, hν, hνω⟩ := hc
  have hA : ω ∈ complexAntiholomorphicH1 X := by
    rw [← spec_complexH1_conjugation_exchanges X, ← hνω]
    exact Submodule.mem_map_of_mem (hle hν)
  have h0 : ω = 0 :=
    Submodule.disjoint_def.mp (spec_complexH1_split X).2 ω (hle hω) hA
  rw [h0, map_zero]

/-- For abelian `X`, pulling back along the bijection `bettiDeRhamHQ X 1` preserves
dimension.

Source: `spec_bettiDeRhamIso_abelian` with `LinearEquiv.finrank_map_eq`. -/
theorem finrank_comap_bettiDeRhamHQ_one (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (P : Submodule ℂ H_dR^((1 : ℕ) : ℤ)(X)) :
    Module.finrank ℂ (P.comap (bettiDeRhamHQ X 1)) = Module.finrank ℂ P := by
  have hβ := (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective 1
  let e := LinearEquiv.ofBijective (bettiDeRhamHQ X 1) hβ
  have hP : (P.comap (bettiDeRhamHQ X 1)).map (e : _ →ₗ[ℂ] _) = P :=
    Submodule.map_comap_eq_of_surjective hβ.2 P
  conv_rhs => rw [← hP]
  exact (LinearEquiv.finrank_map_eq e _).symm

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    Module.finrank ℂ ((⊤ : Submodule ℂ H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1)) =
      Module.finrank ℂ (⊤ : Submodule ℂ H_dR^((1 : ℕ) : ℤ)(X)) :=
  finrank_comap_bettiDeRhamHQ_one X ⊤

/-- For abelian `X`, `ℂ ⊗[ℚ] HQ X 1` is finite-dimensional.

Source: `finiteBetti_abelian` (`HodgeLean/Adapters/TorusCohomology.lean`). -/
instance finiteDimensional_complexHQ_one (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    FiniteDimensional ℂ (ℂ ⊗[ℚ] HQ X 1) := by
  have := (finiteBetti_abelian X).finite 1
  infer_instance

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : Module.Finite ℂ (ℂ ⊗[ℚ] HQ X 1) := inferInstance

theorem spec_finrank_hodgeFiltration_one_le_of_le_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X) :
    Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) ≤ dim X.left := by
  rw [← finrank_comap_bettiDeRhamHQ_one X, ← (spec_complexH1_dimension X).1]
  exact Submodule.finrank_mono hle

theorem spec_comap_hodgeFiltration_one_eq_iff_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X ↔
      (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X ∧
        dim X.left ≤ Module.finrank ℂ (F^1 H_dR^((1 : ℕ) : ℤ)(X)) := by
  rw [← finrank_comap_bettiDeRhamHQ_one X, ← (spec_complexH1_dimension X).1]
  refine ⟨fun h => ⟨h.le, by rw [h]⟩, fun ⟨h, hd⟩ => Submodule.eq_of_le_of_finrank_le h hd⟩

theorem spec_comap_conjHodgeFiltration_one_eq_of_eq_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    (conjHodgeFiltrationComplexSubmodule X 1 ((1 : ℕ) : ℤ)).comap (bettiDeRhamHQ X 1) =
      complexAntiholomorphicH1 X := by
  rw [spec_comap_conjHodgeFiltration_eq_map_sigmaQ_aux X 1 1, heq]
  exact spec_complexH1_conjugation_exchanges X

theorem spec_deRhamHodgePiece_one_isInternal_of_comap_eq_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (heq : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X) :
    DirectSum.IsInternal (deRhamHodgePiece X 1) := by
  exact spec_deRhamHodgePiece_one_isInternal_of_finrank X
    (le_antisymm (spec_finrank_hodgeFiltration_one_le_of_le_aux X heq.le)
      ((spec_comap_hodgeFiltration_one_eq_iff_aux X).mp heq).2)
    (spec_disjoint_hodgeFiltration_one_of_le_aux X heq.le)

theorem spec_comap_hodgeFiltration_one_eq_of_le_of_isInternal_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hle : (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) ≤ complexHolomorphicH1 X)
    (h : DirectSum.IsInternal (deRhamHodgePiece X 1)) :
    (F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1) = complexHolomorphicH1 X := by
  exact (spec_comap_hodgeFiltration_one_eq_iff_aux X).mpr
    ⟨hle, (spec_finrank_hodgeFiltration_one_of_isInternal X h).1.ge⟩

theorem spec_complexHolomorphicH1_ne_antiholomorphic_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hg : 1 ≤ dim X.left) :
    complexHolomorphicH1 X ≠ complexAntiholomorphicH1 X := by
  intro h
  have hbot : complexHolomorphicH1 X = ⊥ := by
    have hd := (spec_complexH1_split X).2
    rw [← h] at hd
    exact disjoint_self.mp hd
  have hdim := (spec_complexH1_dimension X).1
  rw [hbot, finrank_bot] at hdim
  omega

end HodgeLean.Adapters
