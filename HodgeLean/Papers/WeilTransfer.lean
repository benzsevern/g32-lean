import HodgeLean.Papers.WeilTransferProofs
import HodgeLean.Papers.SkeletonG34

/-! # The generic Weil transfer theorem (FROZEN SPEC)

G32 v0.16's proof of Theorem A (Section 7: Lemma 7.1, Theorem 7.2) is uniform in the family
`M(n, K, δ)`. This spec freezes it for `K = ℚ(√-3)`, every half-dimension `n` and every
discriminant class `δ ∈ ℚˣ ⧸ Nm(Kˣ)`, from a `WeilTransferDatum n δ`, and shows that G32's
transfer layer is the instance `n = 3`, `δ = [-2]`. G34 Theorem A is meant to instantiate
`n = 4`, `δ = [1]`, and G34 Theorem B `n = 3` with each `δ`.

Claimed:
* a Hausdorff space charted on `ℂ^{n²}` is a Baire space; on a connected one, a countable union
  of closed analytic subsets that contains a nonempty open set is everything (the Baire step
  itself is G32's `g32t_baire_step`, which is already generic and is reused);
* from a transfer datum: each fibre is a member of `M(n, ℚ(√-3), δ)`, so a member exists; the
  algebraicity locus contains a nonempty open set and is all of the moduli space; every member
  has algebraic Weil classes; `wtr_theoremA_of_transfer` is the implication from a datum to the
  algebraicity of the Weil classes of every member `(A, W, pol)`;
* the period domain `𝓗_n = {Z ∈ Mₙ(ℂ) | 1 - Zᴴ Z > 0}` is open, convex and bounded in
  `ℂ^{n²}`, contains `0`, omits the identity matrix for `n > 0`, and as an open subset is
  connected;
* from a universal family over `𝓗_n`: a member exists; with the remaining stage fields, every
  member has algebraic Weil classes (`wtr_theoremA_of_stages`);
* the G32 bridge: the generic conclusion at `n = 3`, `δ = [-2]` gives
  `G32TheoremAStatement A W pol`, and the two statements, quantified over all carriers, are
  equivalent; `wtr_ofG32` and `wtr_ofG32Family` (definitions) send G32's datum and universal
  family to generic ones;
* the G34 instances: a generic datum at `(4, [1])` gives `G34TheoremAStatement A`, and generic
  data at every `n = 3` discriminant with a member give `G34TheoremBStatement A`.

Not claimed: any field of a datum, of a universal family or of the stage fields. Memberwise
algebraicity, dominance, the discriminant of the fibres, Hilbert spreading, Landherr coverage
and isogeny transport are premises; no datum is constructed for any `(n, δ)`, so no Theorem A
is asserted. The field stays `ℚ(√-3)`. The family structure of the fibres is not recorded.

HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff ComplexOrder Matrix
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

section Topology

/-- **Complex charted spaces are Baire.** A Hausdorff space with charts in `ℂ^{n²}` is locally
compact, hence a Baire space. The generalization of `g32t_baireSpace` from `ℂ⁹`.
Source: Bourbaki, *General Topology*, Ch. IX, §5.3, Theorem 1 (locally compact Hausdorff spaces
are Baire); charts transport local compactness from `ℂ^{n²}`. -/
theorem wtr_baireSpace (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin (n ^ 2) → ℂ) M] : BaireSpace M :=
  wtr_baireSpace_aux n

example : BaireSpace (Fin (4 ^ 2) → ℂ) := wtr_baireSpace 4

/-- **Baire and irreducibility.** On a connected Hausdorff space charted on `ℂ^{n²}`, a
countable union of closed analytic subsets that contains a nonempty open set is the whole space:
by `g32t_baire_step` and `wtr_baireSpace` one member has nonempty interior, and by the identity
principle (`IsClosedAnalytic.eq_univ_of_nonempty_interior`) it is everything. The
generalization of `g32t_eq_univ_of_open_subset` from `ℂ⁹`.
Source: G32 v0.16, proof of Theorem 7.2; Schnell, *Complex Manifolds* (lecture notes), Theorem
1.8 (identity theorem). -/
theorem wtr_eq_univ_of_open_subset (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (Fin (n ^ 2) → ℂ) M] {C : Set (Set M)} (hC : C.Countable)
    (hZ : ∀ Z ∈ C, IsClosedAnalytic (Fin (n ^ 2) → ℂ) Z) {U : Set M} (hU : IsOpen U)
    (hne : U.Nonempty) (hsub : U ⊆ ⋃₀ C) : ⋃₀ C = univ :=
  wtr_eq_univ_of_open_subset_aux n hC hZ hU hne hsub

/-- On `ℂ^{4²}` itself, the family `{univ}` of closed analytic sets. -/
example : ⋃₀ ({univ} : Set (Set (Fin (4 ^ 2) → ℂ))) = univ :=
  wtr_eq_univ_of_open_subset 4 (countable_singleton _)
    (by simpa using isClosedAnalytic_univ) isOpen_univ univ_nonempty (by simp)

end Topology

section Datum

/-- **Every fibre is a member of `M(n, ℚ(√-3), δ)`**: the polarized field and the discriminant
field together. The generalization of `g32t_fiber_isMember`.
Source: G32 v0.16, Lemma 3.6 and Proposition 6.3 (for `n = 3`); the definition of
`wtr_IsMember`. -/
theorem wtr_fiber_isMember {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (s : D.S) : wtr_IsMember n δ (D.fiber s) :=
  wtr_fiber_isMember_aux D s

example {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)} (D : WeilTransferDatum 4 δ)
    (s : D.S) : dim (D.fiber s).X.left = 8 :=
  (wtr_fiber_isMember D s).polarized.dim_eq

/-- **A transfer datum carries a member of `M(n, ℚ(√-3), δ)`.** The dominant open set is
nonempty, so some fibre exists, and it is a member. A datum therefore needs an abelian
`2n`-fold with the full membership package and discriminant `δ`; for `(n, δ)` with no member,
no datum exists. The generalization of `g32t_exists_member`.
Source: G32 v0.16, Lemma 3.6, Proposition 6.3 and Corollary 5.11 (for `n = 3`). -/
theorem wtr_exists_member {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) : ∃ P : wtr_Variety n, wtr_IsMember n δ P :=
  wtr_exists_member_aux D

example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) : ∃ P : wtr_Variety n, dim P.X.left = 2 * n :=
  (wtr_exists_member D).imp fun _ h => h.polarized.dim_eq

/-- **The algebraicity locus contains a nonempty open set**: dominance, memberwise
algebraicity and transport. The generalization of `g32t_open_subset_locus`.
Source: G32 v0.16, proof of Theorem 7.2, second paragraph, with Lemma 2.2. -/
theorem wtr_open_subset_locus {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) :
    ∃ U : Set D.M, IsOpen U ∧ U.Nonempty ∧ U ⊆ {m | wtr_WeilAlg (D.univ m)} :=
  wtr_open_subset_locus_aux D

example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) : {m | wtr_WeilAlg (D.univ m)}.Nonempty :=
  let ⟨_, _, hne, h⟩ := wtr_open_subset_locus D
  hne.mono h

/-- **The algebraicity locus is the whole moduli space**: Hilbert spreading and
`wtr_eq_univ_of_open_subset`. The generalization of `g32t_locus_eq_univ`.
Source: G32 v0.16, Lemma 7.1 and the proof of Theorem 7.2. -/
theorem wtr_locus_eq_univ {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (m : D.M) : wtr_WeilAlg (D.univ m) :=
  wtr_locus_eq_univ_aux D m

example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) : {m | wtr_WeilAlg (D.univ m)} = univ :=
  eq_univ_of_forall (wtr_locus_eq_univ D)

/-- **Every member has algebraic Weil classes**: Landherr coverage, `wtr_locus_eq_univ` and
transport. The generalization of `g32t_weilAlg_of_isMember`.
Source: G32 v0.16, last sentence of the proof of Theorem 7.2, with Lemma 2.2. -/
theorem wtr_weilAlg_of_isMember {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (P : wtr_Variety n) (hP : wtr_IsMember n δ P) :
    wtr_WeilAlg P :=
  wtr_weilAlg_of_isMember_aux D P hP

example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (P : wtr_Variety n) (hP : wtr_IsMember n δ P) :
    WeilClassesAlgebraic (finiteBetti_abelian P.X) (spec_bettiDeRhamIso_abelian P.X)
      (hodgeDecomposition_of_abelian P.X) (torusCohomology_cupProductOf P.X) P.W
      hP.polarized.isWeilType :=
  wtr_weilAlg_of_isMember D P hP _

/-- **The generic Theorem A from a transfer datum.** For every complex abelian variety `A` with
the five instances, every rational Weil action `W` of `ℚ(√-3)` on `H¹` and every degree-two class
`pol`: if `(A, W, pol)` is a member of `M(n, ℚ(√-3), δ)`, its Weil classes are algebraic. The
generalization of `g32t_theoremA_of_transfer`.

This is the implication from the datum; none of its fields is asserted here.
Source: G32 v0.16, Theorem 7.2 and the proof of Theorem A, whose argument is uniform in
`(n, δ)`; van Geemen, LNM 1594, §§5.2–5.11. -/
theorem wtr_theoremA_of_transfer {n : ℕ}
    {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)} (D : WeilTransferDatum n δ)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) (hM : wtr_IsMember n δ (⟨A, W, pol⟩ : wtr_Variety n)) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.polarized.isWeilType :=
  wtr_theoremA_of_transfer_aux D A W pol hM

/-- The G34 Theorem A shape: a datum at `n = 4`, `δ = [1]` gives algebraicity on every abelian
eightfold member. -/
example (D : WeilTransferDatum 4 1) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) (hM : wtr_IsMember 4 1 (⟨A, W, pol⟩ : wtr_Variety 4)) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.polarized.isWeilType :=
  wtr_theoremA_of_transfer D A W pol hM

end Datum

section Domain

/-- **The period domain is open.** `1 - Zᴴ Z` is positive definite exactly when the operator
norm of `Z` is less than `1`, an open condition. The generalization of `g32m_periodSet_isOpen`.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n` is a domain); Hua, Transl. Math. Monographs 6 (1963),
Introduction (the domain `ℜ_I(m, n)`). -/
theorem wtr_periodSet_isOpen (n : ℕ) : IsOpen (wtr_periodSet n) :=
  wtr_periodSet_isOpen_aux n

example (n : ℕ) : interior (wtr_periodSet n) = wtr_periodSet n :=
  (wtr_periodSet_isOpen n).interior_eq

/-- **The open subset `wtr_Domain n` is the period domain itself.** The generalization of
`g32m_domain_coe`.
Source: `wtr_periodSet_isOpen`. -/
theorem wtr_domain_coe (n : ℕ) :
    (wtr_Domain n : Set (Fin (n ^ 2) → ℂ)) = wtr_periodSet n :=
  wtr_domain_coe_aux n

example (n : ℕ) (z : Fin (n ^ 2) → ℂ) (hz : z ∈ wtr_periodSet n) : z ∈ wtr_Domain n := by
  change z ∈ (wtr_Domain n : Set (Fin (n ^ 2) → ℂ))
  rw [wtr_domain_coe]
  exact hz

/-- **The period domain is convex**: the operator-norm ball is convex. The generalization of
`g32m_periodSet_convex`.
Source: Hua, Transl. Math. Monographs 6 (1963), Introduction (`ℜ_I(m, n)` is a convex circular
domain). -/
theorem wtr_periodSet_convex (n : ℕ) : Convex ℝ (wtr_periodSet n) :=
  wtr_periodSet_convex_aux n

example (n : ℕ) : _root_.IsPreconnected (wtr_periodSet n) :=
  (wtr_periodSet_convex n).isPreconnected

/-- **The origin lies in the period domain**: `1 - 0 = 1` is positive definite. The
generalization of `g32m_zero_mem`.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n` is nonempty). -/
theorem wtr_zero_mem (n : ℕ) : (0 : Fin (n ^ 2) → ℂ) ∈ wtr_Domain n :=
  wtr_zero_mem_aux n

example (n : ℕ) : (wtr_Domain n : Set (Fin (n ^ 2) → ℂ)).Nonempty := ⟨0, wtr_zero_mem n⟩

/-- **The period domain is bounded**: positivity of `1 - Zᴴ Z` on a basis vector `e_j` gives
`∑ᵢ |Z_{ij}|² < 1`, so every coordinate has modulus less than `1`. The generalization of
`g32m_periodSet_isBounded`.
Source: Hua, Transl. Math. Monographs 6 (1963), Introduction (the classical domains are
bounded). -/
theorem wtr_periodSet_isBounded (n : ℕ) : Bornology.IsBounded (wtr_periodSet n) :=
  wtr_periodSet_isBounded_aux n

example (n : ℕ) : Bornology.IsBounded (wtr_Domain n : Set (Fin (n ^ 2) → ℂ)) :=
  (wtr_periodSet_isBounded n).subset interior_subset

/-- **The identity matrix is not in the period domain** when `n > 0`: `1 - 1ᴴ 1 = 0` is not
positive definite on `ℂⁿ ≠ 0`. For `n = 0` the domain is the single point of `ℂ⁰`, and the
identity is that point, so the hypothesis `0 < n` is needed. The generalization of
`g32m_not_mem_of_toMat_eq_one`.
Source: the bounded realization (the boundary point `Z = 1`). -/
theorem wtr_not_mem_of_toMat_eq_one (n : ℕ) (hn : 0 < n) (z : Fin (n ^ 2) → ℂ)
    (hz : wtr_toMat n z = 1) : z ∉ wtr_periodSet n :=
  wtr_not_mem_of_toMat_eq_one_aux n hn z hz

example : (fun k : Fin (3 ^ 2) => if k = 0 ∨ k = 4 ∨ k = 8 then (1 : ℂ) else 0) ∉
    wtr_periodSet 3 :=
  wtr_not_mem_of_toMat_eq_one 3 (by norm_num) _ (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wtr_toMat, finProdFinEquiv])

/-- **The period domain is connected**: it is convex and nonempty. With Mathlib's open-subset
instances, `wtr_Domain n` is a connected Hausdorff analytic manifold charted on `ℂ^{n²}`, the
structure `WeilTransferDatum.M` asks for. The generalization of `g32m_domain_connectedSpace`.
Source: G32 v0.16, Subsection 2.1 (`𝓗_n` is connected of dimension `n²`). -/
theorem wtr_domain_connectedSpace (n : ℕ) : ConnectedSpace (wtr_Domain n) :=
  wtr_domain_connectedSpace_aux n

example (n : ℕ) : PreconnectedSpace (wtr_Domain n) :=
  haveI := wtr_domain_connectedSpace n
  inferInstance

end Domain

section Family

/-- **A universal family carries a member of `M(n, ℚ(√-3), δ)`**: the fibre over `0 ∈ 𝓗_n`. For
`(n, δ)` with no member, no universal family exists. The generalization of
`g32m_exists_member`.
Source: G32 v0.16, Subsection 2.1; `wtr_zero_mem`. -/
theorem wtr_family_exists_member {n : ℕ}
    {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)} (F : wtr_UniversalFamily n δ) :
    ∃ P : wtr_Variety n, wtr_IsMember n δ P :=
  wtr_family_exists_member_aux F

example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (F : wtr_UniversalFamily n δ) : ∃ P : wtr_Variety n, dim P.X.left = 2 * n :=
  (wtr_family_exists_member F).imp fun _ h => h.polarized.dim_eq

/-- **The generic Theorem A from a universal family and the remaining stage fields**: with
connectedness from `wtr_domain_connectedSpace`, `wtr_transferFields F R` is a transfer datum and
`wtr_theoremA_of_transfer` applies. The generalization of `g32m_theoremA_of_stages`.

This is the implication from the premise and the stage fields; none of them is asserted here.
Source: G32 v0.16, Subsection 2.1, Theorem 7.2 and the proof of Theorem A. -/
theorem wtr_theoremA_of_stages {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (F : wtr_UniversalFamily n δ) (R : wtr_StageFields F)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) (hM : wtr_IsMember n δ (⟨A, W, pol⟩ : wtr_Variety n)) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.polarized.isWeilType :=
  wtr_theoremA_of_stages_aux F R A W pol hM

/-- The datum of the generic bridge, with connectedness supplied by the frozen statement. -/
example {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (F : wtr_UniversalFamily n δ) (R : wtr_StageFields F) : WeilTransferDatum n δ :=
  haveI := wtr_domain_connectedSpace n
  wtr_transferFields F R

end Family

section Bridge

/-- **G32 is the instance `n = 3`, `δ = [-2]`.** If every member of `M(3, ℚ(√-3), [-2])` in the
generic sense has algebraic Weil classes, then `G32TheoremAStatement A W pol` holds for every
`A`, `W` and `pol`: generic membership at `(3, [-2])` is `IsMemberOfM` (`wtr_isMember_three_iff`)
and `wtr_WeilAlg` is G32's algebraicity.
Source: the definitions of `wtr_IsMember`, `wtr_WeilAlg` and `G32TheoremAStatement`;
`wtr_isMember_three_iff`. -/
theorem wtr_g32_instance
    (h : ∀ P : wtr_Variety 3, wtr_IsMember 3 classNegTwo P → wtr_WeilAlg P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  wtr_g32_instance_aux h A W pol

/-- G32's Theorem A from its transfer datum, through the generic engine: `wtr_ofG32` and
`wtr_weilAlg_of_isMember`. This recovers `g32t_theoremA_of_transfer`. -/
example (D : G32TransferDatum) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  wtr_g32_instance (wtr_weilAlg_of_isMember (wtr_ofG32 D)) A W pol

/-- G32's stage-1 route through the generic one: a G32 universal family and generic stage fields
over it give G32 Theorem A. -/
example (F : g32m_UniversalFamily) (R : wtr_StageFields (wtr_ofG32Family F))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  haveI := wtr_domain_connectedSpace 3
  wtr_g32_instance (wtr_weilAlg_of_isMember (wtr_transferFields (wtr_ofG32Family F) R)) A W pol

/-- **The two statements coincide at `n = 3`, `δ = [-2]`**: "every generic member of
`M(3, ℚ(√-3), [-2])` has algebraic Weil classes" is equivalent to `G32TheoremAStatement` for
every bundled carrier.
Source: `wtr_isMember_three_iff`; the definitions of `wtr_WeilAlg` and `G32TheoremAStatement`. -/
theorem wtr_g32_statement_iff :
    (∀ P : wtr_Variety 3, wtr_IsMember 3 classNegTwo P → wtr_WeilAlg P) ↔
      ∀ P : g32t_Sixfold, G32TheoremAStatement P.X P.W P.pol :=
  wtr_g32_statement_iff_aux

example (h : ∀ P : g32t_Sixfold, G32TheoremAStatement P.X P.W P.pol) (P : wtr_Variety 3)
    (hP : wtr_IsMember 3 classNegTwo P) : wtr_WeilAlg P :=
  wtr_g32_statement_iff.2 h P hP

/-- **G34 Theorem A is the instance `n = 4`, `δ = [1]`.** A generic transfer datum for
`M(4, ℚ(√-3), [1])` gives `G34TheoremAStatement A` for every `A`: the hypotheses of that
statement (Weil type, nondegeneracy, the Rosati condition, positivity, `dim = 8`, discriminant
`1`) are exactly generic membership at `(4, [1])`, and G34's weight-one Hodge structure
`abelianWeightOneHodgeStructure A` is the package's `weight1` by computation.

This is the implication from the datum; no datum for `n = 4` is constructed.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem A; `wtr_theoremA_of_transfer`. -/
theorem wtr_g34A_of_transfer (D : WeilTransferDatum 4 1) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A :=
  wtr_g34A_of_transfer_aux D A

example (D : WeilTransferDatum 4 1) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (finiteBetti_abelian A).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) 3)
    (hW : letI := (finiteBetti_abelian A).finite 1; W.IsWeilType) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : letI := (finiteBetti_abelian A).finite 1;
      IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) W.J)
    (hPos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)
    (hDim : TopologicalSpace.dim A.left = 8)
    (hDisc : weilDatumClass (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hη hRos = 1) :
    letI := (finiteBetti_abelian A).finite 1
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W hW :=
  wtr_g34A_of_transfer D A W hW pol hη hRos hPos hDim hDisc

/-- **G34 Theorem B is the instance `n = 3` at every discriminant.** If every discriminant `δ`
for which `M(3, ℚ(√-3), δ)` has a member carries a generic transfer datum, then
`G34TheoremBStatement A` holds for every `A`: a polarized Weil sixfold is a member at its own
discriminant. The datum is asked for only at discriminants with a member, since for the others
(those of positive sign) no datum exists (`wtr_exists_member`).

This is the implication from the data; no datum is constructed for any `δ`.
Source: Benjamin Severn, *Weil classes on abelian sixfolds and eightfolds of Weil type for
ℚ(√-3)*, v1.5 (21 October 2026), Theorem B; `wtr_theoremA_of_transfer`. -/
theorem wtr_g34B_of_transfer
    (D : ∀ δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0),
      (∃ P : wtr_Variety 3, wtr_IsMember 3 δ P) → WeilTransferDatum 3 δ)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremBStatement A :=
  wtr_g34B_of_transfer_aux D A

/-- At the discriminant `[-2]`, a G32 datum supplies the data hypothesis of
`wtr_g34B_of_transfer` through `wtr_ofG32`; the other negative discriminants need their own. -/
example (D : G32TransferDatum) :
    (∃ P : wtr_Variety 3, wtr_IsMember 3 classNegTwo P) → WeilTransferDatum 3 classNegTwo :=
  fun _ => wtr_ofG32 D

end Bridge

end HodgeLean.Papers
