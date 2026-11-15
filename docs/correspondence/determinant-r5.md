# N3: determinant comparison at release

Source commit: `2d7d1d19097bf3d518cb02e9ea3b8ad7005e8d8c`.

Checked: the excerpts below retain ambient binders, definitions and proof terms. Prefixes are original file line numbers; text after the prefix is verbatim.

The G32 consumer is `g32_quadraticDeterminant_cup_mem_weilClassOf`. Its `hM` supplies `isWeilType` and rank three; `h10_sup_h01_eq_top` supplies `hH`; positivity of 3 supplies `hd`; rank three supplies `hκ`. The quadratic adapter takes `K = QuadraticAlgebra ℚ (-3) 0`, the action induced by `W.J`, and `ω = QuadraticAlgebra.omega`. Its proof supplies `hω`, `hJ` and `hK` explicitly, along with the scalar tower and finite module instances. Thus the comparison concerns the entire degree-six determinant with quotient-section normalization. The membership hypothesis remains an input to the G32 statement.

## `HodgeLean/Blocks/Weil/DeterminantComparison.lean:1–144`

```lean
1: import HodgeLean.Blocks.Weil.ExteriorQuotientDerivation
2: import HodgeLean.Blocks.Weil.KernelQuotient
3: import HodgeLean.Blocks.Weil.KernelSemisimple
4:
5: /-! # The quadratic determinant and the rational Weil space -/
6:
7: noncomputable section
8:
9: namespace HodgeBlocks.WeilAction
10:
11: open ExteriorRestriction
12:
13: variable {K V : Type*} [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
14:   [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
15:   [Module K V] [IsScalarTower ℚ K V] [Module.Finite K V]
16:   {M : QHodgeStructure 1 V} {d : ℚ}
17:
18: /-- The exterior quotient annihilates the rational Weil operator for the compatible
19: quadratic-field action. -/
20: theorem quotient_derivationKernelOperatorQ (A : WeilAction M d) (ω : K)
21:     (hω : ω ^ 2 = algebraMap ℚ K (-d)) (hJ : A.J = scalarEnd (V := V) ω)
22:     (k : ℕ) (x : ⋀[ℚ]^(k + k) V) :
23:     quotient (K := K) (k + k) (derivationKernelOperatorQ A k x) = 0 := by
24:   change quotient (K := K) (k + k)
25:     (derivationExt A.J (k + k) (derivationExt A.J (k + k) x) +
26:       (4 * (k : ℚ) ^ 2 * d) • x) = 0
27:   rw [map_add, map_smul, hJ, quotient_derivationExt, quotient_derivationExt,
28:     smul_smul, ← IsScalarTower.algebraMap_smul K (4 * (k : ℚ) ^ 2 * d),
29:     ← add_smul]
30:   have hc : (((k + k : ℕ) : K) * ω) * (((k + k : ℕ) : K) * ω) +
31:       algebraMap ℚ K (4 * (k : ℚ) ^ 2 * d) = 0 := by
32:     calc
33:       _ = (((k + k : ℕ) : K) ^ 2) * ω ^ 2 +
34:           algebraMap ℚ K (4 * (k : ℚ) ^ 2 * d) := by ring
35:       _ = 0 := by rw [hω]; push_cast; norm_num; ring
36:   rw [hc, zero_smul]
37:
38: /-- The K-exterior quotient restricts to an isomorphism on the rational Weil space. -/
39: theorem bijective_quotient_weilClasses (A : WeilAction M d)
40:     (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
41:     (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
42:     (ω : K) (hω : ω ^ 2 = algebraMap ℚ K (-d))
43:     (hJ : A.J = scalarEnd (V := V) ω) (hK : Module.finrank ℚ K = 2)
44:     (hV : Module.finrank K V =
45:       Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
46:         Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) :
47:     Function.Bijective ((quotient (K := K) _).comp (A.weilClasses hH hW).subtype) := by
48:   let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
49:   letI : Module.Finite ℚ (⋀[K]^(k + k) V) := Module.Finite.trans K _
50:   have hn : 0 < k + k := by dsimp [k]; omega
51:   have hdim : Module.finrank ℚ (⋀[K]^(k + k) V) = 2 := by
52:     rw [← Module.finrank_mul_finrank ℚ K (⋀[K]^(k + k) V), hK]
53:     rw [← hV, finrank_topExteriorPower K V]
54:   rw [A.weilClasses_eq_ker_derivationKernelOperatorQ hH hW hd]
55:   apply bijective_quotient_restrict_ker
56:   · exact quotient_surjective (k + k) hn
57:   · exact A.quotient_derivationKernelOperatorQ ω hω hJ k
58:   · exact A.derivationKernelOperatorQ_no_nilpotent hH hW hd
59:   · rw [← A.weilClasses_eq_ker_derivationKernelOperatorQ hH hW hd,
60:       A.finrank_weilClasses_eq_two hH hW hd hκ, hdim]
61:
62: /-- Quadratic restriction of scalars gives the expected K-dimension of a Weil factor. -/
63: theorem finrank_over_quadratic (A : WeilAction M d)
64:     (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
65:     (hK : Module.finrank ℚ K = 2) :
66:     Module.finrank K V = Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
67:       Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) := by
68:   have hc := Submodule.finrank_add_eq_of_isCompl (A.isCompl_Vs_Vsbar hd)
69:   rw [A.finrank_Vsbar_eq_Vs, Module.finrank_baseChange] at hc
70:   have hVs := A.finrank_Vs_eq_twice_inf_H10 hH hW
71:   have hr := Module.finrank_mul_finrank ℚ K V
72:   rw [hK] at hr
73:   omega
74:
75: section Inclusion
76:
77: variable (A : WeilAction M d)
78:     (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
79:     (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
80:     (ω : K) (hω : ω ^ 2 = algebraMap ℚ K (-d))
81:     (hJ : A.J = scalarEnd (V := V) ω) (hK : Module.finrank ℚ K = 2)
82:
83: /-- The normalized quadratic determinant comparison: its forward map is the
84: universal exterior quotient restricted to the Weil space. -/
85: def determinantEquiv : ↥(A.weilClasses hH hW) ≃ₗ[ℚ]
86:     (⋀[K]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
87:       Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) :=
88:   LinearEquiv.ofBijective ((quotient (K := K) _).comp (A.weilClasses hH hW).subtype)
89:     (A.bijective_quotient_weilClasses hH hW hd hκ ω hω hJ hK
90:       (A.finrank_over_quadratic hH hW hd hK))
91:
92: /-- The rational inclusion of the K-determinant, normalized as a section of the
93: universal exterior quotient with image in the Weil space. -/
94: def determinantInclusion :
95:     (⋀[K]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
96:       Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) →ₗ[ℚ]
97:     (⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
98:       Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) :=
99:   (A.weilClasses hH hW).subtype.comp
100:     (A.determinantEquiv hH hW hd hκ ω hω hJ hK).symm.toLinearMap
101:
102: /-- The normalized K-determinant inclusion is injective. -/
103: theorem determinantInclusion_injective :
104:     Function.Injective (A.determinantInclusion hH hW hd hκ ω hω hJ hK) :=
105:   (A.weilClasses hH hW).injective_subtype.comp
106:     (A.determinantEquiv hH hW hd hκ ω hω hJ hK).symm.injective
107:
108: /-- Every element of the K-determinant maps to a rational Weil class. -/
109: theorem determinantInclusion_mem (w) :
110:     A.determinantInclusion hH hW hd hκ ω hω hJ hK w ∈ A.weilClasses hH hW :=
111:   ((A.determinantEquiv hH hW hd hκ ω hω hJ hK).symm w).property
112:
113: /-- The image of the K-determinant is the entire rational Weil space. -/
114: theorem range_determinantInclusion :
115:     LinearMap.range (A.determinantInclusion hH hW hd hκ ω hω hJ hK) =
116:       A.weilClasses hH hW := by
117:   let e := A.determinantEquiv hH hW hd hκ ω hω hJ hK
118:   ext x
119:   constructor
120:   · rintro ⟨w, rfl⟩
121:     exact A.determinantInclusion_mem hH hW hd hκ ω hω hJ hK w
122:   · intro hx
123:     refine ⟨e ⟨x, hx⟩, ?_⟩
124:     exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
125:
126: /-- The determinant comparison uses the normalization q ∘ i = id. -/
127: theorem quotient_determinantInclusion (w) :
128:     quotient (K := K) _ (A.determinantInclusion hH hW hd hκ ω hω hJ hK w) = w :=
129:   (A.determinantEquiv hH hW hd hκ ω hω hJ hK).apply_symm_apply w
130:
131: end Inclusion
132:
133: #print axioms finrank_over_quadratic
134: #print axioms determinantEquiv
135: #print axioms determinantInclusion
136: #print axioms determinantInclusion_injective
137: #print axioms determinantInclusion_mem
138: #print axioms range_determinantInclusion
139: #print axioms quotient_determinantInclusion
140:
141: #print axioms quotient_derivationKernelOperatorQ
142: #print axioms bijective_quotient_weilClasses
143:
144: end HodgeBlocks.WeilAction
```

## `HodgeLean/Blocks/Weil/QuadraticDeterminant.lean:1–89`

```lean
1: import HodgeLean.Blocks.Weil.DeterminantComparison
2: import HodgeLean.Foundations.WeilHermitian
3:
4: /-! # The determinant inclusion for the quadratic field generated by J -/
5:
6: noncomputable section
7: set_option maxHeartbeats 400000
8:
9: namespace HodgeBlocks.WeilAction
10:
11: open HodgeLean.Foundations.WeilHermitian
12:
13: /-- Positive d makes the polynomial defining the imaginary quadratic field irreducible. -/
14: theorem quadratic_no_root {d : ℚ} (hd : 0 < d) : ∀ r : ℚ, r ^ 2 ≠ -d + 0 * r := by
15:   intro r h
16:   have hr := sq_nonneg r
17:   nlinarith
18:
19: variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
20:   {M : QHodgeStructure 1 V} {d : ℚ}
21:   [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]
22:
23: variable (A : WeilAction M d)
24:
25: /-- The canonical inclusion for K = Q(√(-d)), with its module structure supplied by J. -/
26: def quadraticDeterminantInclusion
27:     (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
28:     (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) :
29:     (⋀[QuadraticAlgebra ℚ (-d) 0]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
30:       Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) (WithJ V (a := -d) ⟨A.J, A.J_sq⟩)) →ₗ[ℚ]
31:     (⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
32:       Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V) := by
33:   letI : Module (QuadraticAlgebra ℚ (-d) 0) V := WithJ.instModule ⟨A.J, A.J_sq⟩
34:   letI : IsScalarTower ℚ (QuadraticAlgebra ℚ (-d) 0) V :=
35:     WithJ.instIsScalarTower ⟨A.J, A.J_sq⟩
36:   letI : Module.Finite (QuadraticAlgebra ℚ (-d) 0) V :=
37:     Module.Finite.of_restrictScalars_finite ℚ _ _
38:   exact A.determinantInclusion (K := QuadraticAlgebra ℚ (-d) 0) (V := V) hH hW hd hκ
39:     QuadraticAlgebra.omega
40:     (by simp [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap])
41:     (by
42:       ext x
43:       exact (equiv_omega_smul ⟨A.J, A.J_sq⟩ x).symm)
44:     (QuadraticAlgebra.finrank_eq_two (-d) 0)
45:
46: /-- The canonical quadratic determinant inclusion is injective. -/
47: theorem quadraticDeterminantInclusion_injective
48:     (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
49:     (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) :
50:     Function.Injective (A.quadraticDeterminantInclusion hH hW hd hκ) := by
51:   letI : Module (QuadraticAlgebra ℚ (-d) 0) V := WithJ.instModule ⟨A.J, A.J_sq⟩
52:   letI : IsScalarTower ℚ (QuadraticAlgebra ℚ (-d) 0) V :=
53:     WithJ.instIsScalarTower ⟨A.J, A.J_sq⟩
54:   letI : Module.Finite (QuadraticAlgebra ℚ (-d) 0) V :=
55:     Module.Finite.of_restrictScalars_finite ℚ _ _
56:   unfold quadraticDeterminantInclusion
57:   exact A.determinantInclusion_injective (K := QuadraticAlgebra ℚ (-d) 0)
58:     (V := V) _ _ _ _ _ _ _ _
59:
60: /-- Its image is the full rational Weil space. -/
61: theorem range_quadraticDeterminantInclusion
62:     (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
63:     (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) :
64:     LinearMap.range (A.quadraticDeterminantInclusion hH hW hd hκ) =
65:       A.weilClasses hH hW := by
66:   letI : Module (QuadraticAlgebra ℚ (-d) 0) V := WithJ.instModule ⟨A.J, A.J_sq⟩
67:   letI : IsScalarTower ℚ (QuadraticAlgebra ℚ (-d) 0) V :=
68:     WithJ.instIsScalarTower ⟨A.J, A.J_sq⟩
69:   letI : Module.Finite (QuadraticAlgebra ℚ (-d) 0) V :=
70:     Module.Finite.of_restrictScalars_finite ℚ _ _
71:   unfold quadraticDeterminantInclusion
72:   exact A.range_determinantInclusion (K := QuadraticAlgebra ℚ (-d) 0)
73:     (V := V) _ _ _ _ _ _ _ _
74:
75: /-- Every quadratic determinant vector is a rational Weil class. -/
76: theorem quadraticDeterminantInclusion_mem
77:     (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
78:     (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) (w) :
79:     A.quadraticDeterminantInclusion hH hW hd hκ w ∈ A.weilClasses hH hW := by
80:   rw [← A.range_quadraticDeterminantInclusion hH hW hd hκ]
81:   exact ⟨w, rfl⟩
82:
83: #print axioms quadratic_no_root
84: #print axioms quadraticDeterminantInclusion
85: #print axioms quadraticDeterminantInclusion_injective
86: #print axioms range_quadraticDeterminantInclusion
87: #print axioms quadraticDeterminantInclusion_mem
88:
89: end HodgeBlocks.WeilAction
```

## `HodgeLean/RealDefs/WeilDeterminant.lean:1–47`

```lean
1: import HodgeLean.RealDefs.WeilClasses
2: import HodgeLean.Blocks.Weil.QuadraticDeterminant
3:
4: /-! # Transport of the quadratic determinant through the cup-wedge map -/
5:
6: open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
7: noncomputable section
8:
9: namespace HodgeLean.RealDefs
10:
11: variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
12:   [GrpObj X] {μ : CupProduct X}
13:   (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
14:   (hT : TorusCohomology μ)
15:
16: variable {d : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]
17:     (A : letI := hT.finite; HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
18:     (hW : letI := hT.finite; A.IsWeilType) (hd : 0 < d)
19:     (hκ : letI := hT.finite; 1 ≤ Module.finrank ℂ
20:       ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)))
21:
22: /-- A quadratic determinant vector carried by the same cup-wedge map as
23: `WeilClassesAlgebraic` belongs to `weilClassOf`. -/
24: theorem quadraticDeterminant_cup_mem_weilClassOf (w) :
25:     letI := hT.finite
26:     ((HQ.castEquiv X (two_mul _).symm).toLinearMap ∘ₗ μ.cupWedgeMap _)
27:       (A.quadraticDeterminantInclusion (h10_sup_h01_eq_top hF hB hD hT) hW hd hκ w) ∈
28:       weilClassOf hF hB hD hT A hW := by
29:   letI := hT.finite
30:   exact ⟨_, A.quadraticDeterminantInclusion_mem
31:     (h10_sup_h01_eq_top hF hB hD hT) hW hd hκ w, rfl⟩
32:
33: /-- Algebraicity of the rational Weil space applies to every quadratic determinant vector. -/
34: theorem quadraticDeterminant_cup_algebraic
35:     (hWA : WeilClassesAlgebraic hF hB hD hT A hW) (w) :
36:     letI := hT.finite
37:     ((HQ.castEquiv X (two_mul _).symm).toLinearMap ∘ₗ μ.cupWedgeMap _)
38:       (A.quadraticDeterminantInclusion (h10_sup_h01_eq_top hF hB hD hT) hW hd hκ w) ∈
39:       algebraicCycleClassSpan X (Module.finrank ℂ
40:         ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))) := by
41:   letI := hT.finite
42:   exact hWA (quadraticDeterminant_cup_mem_weilClassOf hF hB hD hT A hW hd hκ w)
43:
44: #print axioms quadraticDeterminant_cup_mem_weilClassOf
45: #print axioms quadraticDeterminant_cup_algebraic
46:
47: end HodgeLean.RealDefs
```

## `HodgeLean/Foundations/Program/G32Native/G32WeilDeterminant.lean:1–61`

```lean
1: import HodgeLean.RealDefs.F1569
2: import HodgeLean.Adapters.TorusCohomology
3: import HodgeLean.Adapters.AbelianHodgeDischarge
4: import HodgeLean.Foundations.ComplexSheafSingular
5: import HodgeLean.RealDefs.WeilDeterminant
6:
7: /-! # G32 Theorem A on the entire quadratic determinant space -/
8:
9: noncomputable section
10: set_option maxHeartbeats 200000
11: set_option backward.isDefEq.respectTransparency false
12: set_option backward.isDefEq.respectTransparency.types false
13:
14: open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
15: open HodgeLean.RealDefs HodgeLean.Adapters
16:
17: namespace HodgeLean.Foundations.Program
18:
19: variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] [IsIntegral X.left]
20:   [Smooth X.hom] [IsProjective X.hom]
21:
22: variable
23:     (W : letI := (torusCohomology_cupProductOf X).finite; HodgeBlocks.WeilAction
24:       (abelianVarietyCohomologyOf (finiteBetti_abelian X)
25:         (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
26:         (torusCohomology_cupProductOf X)).weight1 3)
27:     (pol : HQ X 2)
28:     (hM : IsMemberOfM (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
29:       (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) W pol)
30:
31: include hM
32:
33: /-- G32 membership ensures positive middle degree. -/
34: theorem g32_quadraticDeterminant_positive :
35:     letI := (torusCohomology_cupProductOf X).finite
36:     1 ≤ Module.finrank ℂ
37:       ↥(W.Vs ⊓ (abelianVarietyCohomologyOf (finiteBetti_abelian X)
38:         (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
39:         (torusCohomology_cupProductOf X)).weight1.H (1, 0)) := by
40:   letI := (torusCohomology_cupProductOf X).finite
41:   rw [hM.finrank_eq_three]
42:   norm_num
43:
44: /-- Every vector of the printed quadratic determinant space maps into the rational
45: Weil classes by the existing cup-wedge map. -/
46: theorem g32_quadraticDeterminant_cup_mem_weilClassOf (w) :
47:     letI := (torusCohomology_cupProductOf X).finite
48:     ((HQ.castEquiv X (two_mul _).symm).toLinearMap ∘ₗ (cupProductOf X).cupWedgeMap _)
49:       (W.quadraticDeterminantInclusion
50:         (h10_sup_h01_eq_top (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
51:           (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X))
52:         hM.isWeilType (by norm_num) (g32_quadraticDeterminant_positive X W pol hM) w) ∈
53:       weilClassOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
54:         (hodgeDecomposition_of_abelian X) (torusCohomology_cupProductOf X) W hM.isWeilType := by
55:   letI := (torusCohomology_cupProductOf X).finite
56:   exact quadraticDeterminant_cup_mem_weilClassOf _ _ _ _ W hM.isWeilType _ _ w
57:
58: #print axioms g32_quadraticDeterminant_cup_mem_weilClassOf
59: #print axioms g32_quadraticDeterminant_positive
60:
61: end HodgeLean.Foundations.Program
```

## `HodgeLean/RealDefs/F1569.lean:236–273`

```lean
236: structure IsMemberOfM (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
237:     (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
238:     (A : letI := hT.finite
239:       HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
240:     (η : HQ X 2) : Prop where
241:   dim_eq : dim X.left = 6
242:   isWeilType : letI := hT.finite; A.IsWeilType
243:   nondegenerate : IsNondegenerate (polarizationVec hT η)
244:   rosati : letI := hT.finite; IsRosatiSkew (polarizationVec hT η) A.J
245:   positive : PolarizationPositive hF hB hD hT nondegenerate
246:   datum : weilDatumClass hF hB hD hT A nondegenerate rosati = classNegTwo
247:
248: /-- For a member of `M`, `k = dim (V_s ∩ H^{1,0}) = 3`: its Weil classes lie in `H⁶`. -/
249: theorem IsMemberOfM.finrank_eq_three {hF : FiniteBetti X} {hB : BettiDeRhamIso X}
250:     {hD : HodgeDecomposition X} {hT : TorusCohomology μ}
251:     {A : letI := hT.finite
252:       HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3}
253:     {η : HQ X 2} (h : IsMemberOfM hF hB hD hT A η) :
254:     letI := hT.finite
255:     Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = 3 := by
256:   have := two_mul_finrank_vs_inf_h10_eq hF hB hD hT (by norm_num) A h.isWeilType
257:   rw [h.dim_eq] at this
258:   omega
259:
260: /-- For a member of `M`, `dim_K H¹ = 6` for `K = ℚ(√−3)` acting through `J`. -/
261: theorem IsMemberOfM.finrank_withJ {hF : FiniteBetti X} {hB : BettiDeRhamIso X}
262:     {hD : HodgeDecomposition X} {hT : TorusCohomology μ}
263:     {A : letI := hT.finite
264:       HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3}
265:     {η : HQ X 2} (h : IsMemberOfM hF hB hD hT A η) :
266:     letI := hT.finite
267:     finrank (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ X 1) ⟨A.J, A.J_sq⟩) = 6 := by
268:   let := hT.finite
269:   have h1 := WeilHermitian.finrank_withJ (V := HQ X 1) ⟨A.J, A.J_sq⟩
270:   rw [hT.finrank_eq, h.dim_eq] at h1
271:   omega
272:
273: end Member
```

Open: this evidence note makes no additional assertion about printed-family generality or construction of membership data.

## Field action implementation: `HodgeLean/Foundations/WeilHermitian.lean:91–161`

```lean
91: @[nolint unusedArguments]
92: def WithJ (V : Type*) [AddCommGroup V] [Module ℚ V] {a : ℚ}
93:     (_J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id}) : Type _ := V
94:
95: variable {a : ℚ} (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
96:
97: instance : AddCommGroup (WithJ V J) := inferInstanceAs (AddCommGroup V)
98:
99: instance : Module ℚ (WithJ V J) := inferInstanceAs (Module ℚ V)
100:
101: /-- The identity of `V`, as a `ℚ`-linear equivalence `WithJ V J ≃ₗ[ℚ] V`.
102:
103: Source: the type synonym `WithJ`, defined here. -/
104: def WithJ.equiv : WithJ V J ≃ₗ[ℚ] V := LinearEquiv.refl ℚ V
105:
106: example (x : V) : WithJ.equiv J ((WithJ.equiv J).symm x) = x := rfl
107:
108: instance WithJ.instFiniteDimensional [FiniteDimensional ℚ V] : FiniteDimensional ℚ (WithJ V J) :=
109:   inferInstanceAs (FiniteDimensional ℚ V)
110:
111: /-- `J (J x) = a • x`. -/
112: theorem apply_apply (x : V) : J.1 (J.1 x) = a • x := by
113:   simpa using LinearMap.congr_fun J.2 x
114:
115: /-- The `ℚ`-algebra map `ℚ(ω) → End V`, `x + y ω ↦ x + y J`.
116:
117: Source: `QuadraticAlgebra.lift`. -/
118: noncomputable def omegaHom : QuadraticAlgebra ℚ a 0 →ₐ[ℚ] Module.End ℚ V :=
119:   QuadraticAlgebra.lift ⟨J, by rw [Module.End.mul_eq_comp, J.2, zero_smul, add_zero]; rfl⟩
120:
121: theorem omegaHom_apply (z : QuadraticAlgebra ℚ a 0) (x : V) :
122:     omegaHom J z x = z.re • x + z.im • J.1 x := by
123:   simp [omegaHom]
124:
125: /-- `omegaHom` sends `ω` to `J`. -/
126: example : omegaHom J QuadraticAlgebra.omega = J := by
127:   ext x
128:   simp [omegaHom_apply]
129:
130: /-- The `K`-module structure on `WithJ V J`: `(x + y ω) • v = x • v + y • J v`.
131:
132: Source: restriction of scalars along `omegaHom`, as for `WithJ`. -/
133: noncomputable instance WithJ.instModule : Module (QuadraticAlgebra ℚ a 0) (WithJ V J) :=
134:   Module.compHom V (omegaHom J).toRingHom
135:
136: /-- The action of `z = x + y ω` on `WithJ V J` is `x + y J`. -/
137: theorem equiv_smul (z : QuadraticAlgebra ℚ a 0) (v : WithJ V J) :
138:     WithJ.equiv J (z • v) = z.re • WithJ.equiv J v + z.im • J.1 (WithJ.equiv J v) :=
139:   omegaHom_apply J z v
140:
141: /-- `ω` acts as `J`. -/
142: theorem equiv_omega_smul (v : WithJ V J) :
143:     WithJ.equiv J ((QuadraticAlgebra.omega : QuadraticAlgebra ℚ a 0) • v) =
144:       J.1 (WithJ.equiv J v) := by
145:   simp [equiv_smul]
146:
147: instance WithJ.instIsScalarTower : IsScalarTower ℚ (QuadraticAlgebra ℚ a 0) (WithJ V J) :=
148:   ⟨fun q z v ↦ (WithJ.equiv J).injective <| by
149:     simp only [equiv_smul, map_smul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul,
150:       smul_add, smul_eq_mul, mul_smul]⟩
151:
152: instance WithJ.instModuleFinite [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)] [FiniteDimensional ℚ V] :
153:     Module.Finite (QuadraticAlgebra ℚ a 0) (WithJ V J) :=
154:   Module.Finite.of_restrictScalars_finite ℚ _ _
155:
156: /-- `dim_ℚ V = 2 dim_K V`. -/
157: theorem finrank_withJ [Fact (∀ r : ℚ, r ^ 2 ≠ a + 0 * r)] [FiniteDimensional ℚ V] :
158:     2 * finrank (QuadraticAlgebra ℚ a 0) (WithJ V J) = finrank ℚ V := by
159:   rw [← QuadraticAlgebra.finrank_eq_two a 0, Module.finrank_mul_finrank,
160:     (WithJ.equiv J).finrank_eq]
161:
```
