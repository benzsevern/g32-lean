import HodgeLean.Adapters.IntersectionProductConeSeparation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace
noncomputable section
open CategoryTheory AlgebraicGeometry Order
open scoped Matrix
open Fin.NatCast
namespace HodgeLean.Adapters
/-- A cyclic vector cannot lie in the image of a singular scalar shift of its operator. -/
theorem IntersectionProductScaf_cyclic_vector_shift_surjective
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Module.End K V) (v : V)
    (hv : Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) = ⊤)
    (c : K) (hc : v ∈ LinearMap.range (F - c • (LinearMap.id : Module.End K V))) :
    Function.Surjective (F - c • (LinearMap.id : Module.End K V)) := by
  let A : Module.End K V := F - c • (LinearMap.id : Module.End K V)
  have hstable : ∀ w ∈ LinearMap.range A, F w ∈ LinearMap.range A := by
    rintro w ⟨u, rfl⟩
    refine ⟨F u, ?_⟩
    simp [A, map_sub, map_smul]
  have hp : ∀ k : ℕ, (F ^ k) v ∈ LinearMap.range A := by
    intro k
    induction k with
    | zero => simpa [A] using hc
    | succ k hk =>
      simpa only [pow_succ', Module.End.mul_apply] using hstable _ hk
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hv]
  exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hp)
#print axioms IntersectionProductScaf_cyclic_vector_shift_surjective
/-- Every nonzero coordinate vector is the first vector of a basis with the same finite index set. -/
theorem IntersectionProductScaf_basis_with_first_vector
    {K : Type} [Field K] {n : ℕ} (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ b : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K), b 0 = v := by
  classical
  have hli : LinearIndepOn K id ({v} : Set (Fin (n + 1) → K)) :=
    (linearIndepOn_singleton_iff K).mpr hv
  let b₀ := Module.Basis.extend hli
  let i₀ : hli.extend (Set.subset_univ _) :=
    ⟨v, hli.subset_extend (Set.subset_univ _) (Set.mem_singleton v)⟩
  let e₀ := b₀.indexEquiv (Pi.basisFun K (Fin (n + 1)))
  let e := e₀.trans (Equiv.swap (e₀ i₀) 0)
  refine ⟨b₀.reindex e, ?_⟩
  have he : e i₀ = 0 := by simp [e]
  rw [← he, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  exact Module.Basis.extend_apply_self hli i₀
#print axioms IntersectionProductScaf_basis_with_first_vector

/-- The columns are the first successive iterates of the given vector. -/
def IntersectionProductScaf_krylovMatrix {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (v : Fin (n + 1) → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => ((M ^ j.val) *ᵥ v) i

/-- Ring maps preserve the matrix of successive iterates. -/
theorem IntersectionProductScaf_map_krylovMatrix
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (v : Fin (n + 1) → R) :
    (IntersectionProductScaf_krylovMatrix M v).map f =
      IntersectionProductScaf_krylovMatrix (M.map f) (f ∘ v) := by
  ext i j
  change f (((M ^ j.val) *ᵥ v) i) = (((M.map f) ^ j.val) *ᵥ (f ∘ v)) i
  rw [RingHom.map_mulVec, Matrix.map_pow]
#print axioms IntersectionProductScaf_map_krylovMatrix

/-- A basis beginning at a chosen vector produces an operator whose successive powers traverse that basis. -/
theorem IntersectionProductScaf_exists_cyclic_operator
    {K : Type} [Field K] {n : ℕ} (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ F : Module.End K (Fin (n + 1) → K),
      ∃ b : Module.Basis (Fin (n + 1)) K (Fin (n + 1) → K),
        ∀ i : Fin (n + 1), (F ^ i.val) v = b i := by
  classical
  obtain ⟨b, hb⟩ := IntersectionProductScaf_basis_with_first_vector v hv
  let F := b.constr K (fun i => b (i + 1))
  refine ⟨F, b, ?_⟩
  have hp : ∀ k : ℕ, (F ^ k) v = b (Nat.cast k : Fin (n + 1)) := by
    intro k
    induction k with
    | zero => simpa using hb.symm
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply, hk]
      change b.constr K (fun i => b (i + 1)) (b _) = _
      rw [Module.Basis.constr_basis]
      simp only [Nat.cast_add, Nat.cast_one]
  intro i
  simpa using hp i.val
#print axioms IntersectionProductScaf_exists_cyclic_operator

/-- A nonzero vector has a matrix whose successive iterates form an invertible matrix. -/
theorem IntersectionProductScaf_exists_krylov_det_ne_zero
    {K : Type} [Field K] {n : ℕ} (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      (IntersectionProductScaf_krylovMatrix M v).det ≠ 0 := by
  classical
  obtain ⟨F, b, hb⟩ := IntersectionProductScaf_exists_cyclic_operator v hv
  let M := LinearMap.toMatrix' F
  have hp (k : ℕ) : (M ^ k) *ᵥ v = (F ^ k) v := by
    have he : M ^ k = LinearMap.toMatrix' (F ^ k) :=
      (map_pow LinearMap.toMatrixAlgEquiv' F k).symm
    rw [he, LinearMap.toMatrix'_mulVec]
  refine ⟨M, ?_⟩
  have hcol : Matrix.col (IntersectionProductScaf_krylovMatrix M v) = b := by
    funext j i
    exact congrFun ((hp j.val).trans (hb j)) i
  have hli : LinearIndependent K (Matrix.col (IntersectionProductScaf_krylovMatrix M v)) := by
    rw [hcol]
    exact b.linearIndependent
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_col_iff_isUnit.mp hli)).ne_zero
#print axioms IntersectionProductScaf_exists_krylov_det_ne_zero

/-- A general complex matrix has independent iterates of any fixed nonzero vector over a field extension. -/
theorem IntersectionProductScaf_generic_krylov_det_ne_zero
    {K : Type} [Field K] [Algebra ℂ K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      (IntersectionProductScaf_krylovMatrix
        (Matrix.of fun i j => algebraMap ℂ K (a (i, j))) v).det ≠ 0} := by
  classical
  let N : Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (Fin (n + 1) × Fin (n + 1)) K) :=
    Matrix.of fun i j => MvPolynomial.X (i, j)
  let G := (IntersectionProductScaf_krylovMatrix N (MvPolynomial.C ∘ v)).det
  have heval (a : Fin (n + 1) × Fin (n + 1) → K) :
      MvPolynomial.eval a G =
        (IntersectionProductScaf_krylovMatrix (Matrix.of fun i j => a (i, j)) v).det := by
    dsimp only [G]
    rw [RingHom.map_det]
    change ((IntersectionProductScaf_krylovMatrix N (MvPolynomial.C ∘ v)).map (MvPolynomial.eval a)).det = _
    rw [IntersectionProductScaf_map_krylovMatrix]
    congr 2
    · ext i j
      simp [N]
    · funext i
      simp
  have hG : G ≠ 0 := by
    obtain ⟨M, hM⟩ := IntersectionProductScaf_exists_krylov_det_ne_zero v hv
    intro h
    apply hM
    have he := heval (fun ij => M ij.1 ij.2)
    rw [h, map_zero] at he
    exact he.symm
  exact (a3r_generic_of_ne_zero G hG).mono fun a ha => by
    change MvPolynomial.eval (fun i => algebraMap ℂ K (a i)) G ≠ 0 at ha
    change (IntersectionProductScaf_krylovMatrix (Matrix.of fun i j => algebraMap ℂ K (a (i, j))) v).det ≠ 0
    rwa [heval] at ha
#print axioms IntersectionProductScaf_generic_krylov_det_ne_zero

/-- An operator commuting with the matrix transports all successive-iterate columns. -/
theorem IntersectionProductScaf_krylov_mulVec_of_commute
    {R : Type*} [CommRing R] {n : ℕ}
    (M A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (h : Commute M A)
    (u : Fin (n + 1) → R) :
    IntersectionProductScaf_krylovMatrix M (A *ᵥ u) =
      A * IntersectionProductScaf_krylovMatrix M u := by
  ext i j
  change ((M ^ j.val) *ᵥ (A *ᵥ u)) i = (A *ᵥ ((M ^ j.val) *ᵥ u)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (h.pow_left j.val).eq]
#print axioms IntersectionProductScaf_krylov_mulVec_of_commute

/-- A matrix commuting with a cyclic operator is nonsingular if its image contains the cyclic vector. -/
theorem IntersectionProductScaf_det_ne_zero_of_cyclic_image
    {K : Type*} [Field K] {n : ℕ}
    (M A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (h : Commute M A)
    (v : Fin (n + 1) → K) (hv : (IntersectionProductScaf_krylovMatrix M v).det ≠ 0)
    (u : Fin (n + 1) → K) (hu : A *ᵥ u = v) : A.det ≠ 0 := by
  rw [← hu, IntersectionProductScaf_krylov_mulVec_of_commute M A h u, Matrix.det_mul] at hv
  exact (mul_ne_zero_iff.mp hv).1
#print axioms IntersectionProductScaf_det_ne_zero_of_cyclic_image

/-- A generic translation pencil has no singular member whose image contains a prescribed nonzero vector. -/
theorem IntersectionProductScaf_generic_pencil_image_avoids_vector
    {K : Type} [Field K] [Algebra ℂ K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v ≠ 0) :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : K, ∀ u : Fin (n + 1) → K,
        let M : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
          Matrix.of fun i j => algebraMap ℂ K (a (i, j))
        let A := (1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) + t • M
        A *ᵥ u = v → A.det ≠ 0} := by
  refine (IntersectionProductScaf_generic_krylov_det_ne_zero v hv).mono ?_
  intro a ha t u
  dsimp only
  intro hu
  apply IntersectionProductScaf_det_ne_zero_of_cyclic_image _ _ _ v ha u hu
  exact ((Commute.one_right _).smul_right (1 - t)).add_right
    ((Commute.refl _).smul_right t)
#print axioms IntersectionProductScaf_generic_pencil_image_avoids_vector

/-- The cokernel of a scalar shift of a cyclic operator is generated by the cyclic vector. -/
theorem IntersectionProductScaf_cyclic_shift_quotient_span
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Module.End K V) (v : V)
    (hv : Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) = ⊤) (c : K) :
    let A : Module.End K V := F - c • (LinearMap.id : Module.End K V)
    Submodule.span K {((LinearMap.range A).mkQ) v} = ⊤ := by
  intro A
  let q := (LinearMap.range A).mkQ
  have hq (w : V) : q (F w) = c • q w := by
    have hz : q (A w) = 0 := (Submodule.Quotient.mk_eq_zero (LinearMap.range A)).mpr ⟨w, rfl⟩
    change q (F w - c • w) = 0 at hz
    simpa only [map_sub, map_smul, sub_eq_zero] using hz
  have hp (k : ℕ) : q ((F ^ k) v) = c ^ k • q v := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ', Module.End.mul_apply, hq, hk, smul_smul, pow_succ']
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨w, rfl⟩ := (LinearMap.range A).mkQ_surjective z
  have hw : w ∈ Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) := by rw [hv]; trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    rw [hp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  | zero => simpa using (Submodule.zero_mem (Submodule.span K {q v}))
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa using Submodule.smul_mem _ a ih
#print axioms IntersectionProductScaf_cyclic_shift_quotient_span
/-- An invertible successive-iterate matrix makes its first vector cyclic. -/
theorem IntersectionProductScaf_krylov_det_ne_zero_span
    {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (v : Fin (n + 1) → K)
    (hv : (IntersectionProductScaf_krylovMatrix M v).det ≠ 0) :
    Submodule.span K (Set.range (fun k : ℕ => ((Matrix.toLin' M) ^ k) v)) = ⊤ := by
  classical
  let C := IntersectionProductScaf_krylovMatrix M v
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  have hs : Submodule.span K (Set.range C.col) = ⊤ := by
    rw [← Matrix.range_toLin']
    exact LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr hu)
  apply top_unique
  rw [← hs]
  apply Submodule.span_mono
  rintro w ⟨j, rfl⟩
  refine ⟨j.val, ?_⟩
  have he := map_pow Matrix.toLinAlgEquiv' M j.val
  exact congrArg (fun f : Module.End K (Fin (n + 1) → K) => f v) he.symm
#print axioms IntersectionProductScaf_krylov_det_ne_zero_span

/-- A scalar shift of a cyclic operator has cokernel dimension at most one. -/
theorem IntersectionProductScaf_cyclic_shift_cokernel_finrank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Module.End K V) (v : V)
    (hv : Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) = ⊤) (c : K) :
    Module.finrank K (V ⧸ LinearMap.range (F - c • (LinearMap.id : Module.End K V))) ≤ 1 := by
  classical
  let A : Module.End K V := F - c • (LinearMap.id : Module.End K V)
  have hs := IntersectionProductScaf_cyclic_shift_quotient_span F v hv c
  have hb := finrank_span_le_card (R := K)
    ({(LinearMap.range A).mkQ v} : Set (V ⧸ LinearMap.range A))
  change Submodule.span K {(LinearMap.range A).mkQ v} = ⊤ at hs
  rw [hs] at hb
  rw [Set.toFinset_singleton, Finset.card_singleton] at hb
  simpa using hb
#print axioms IntersectionProductScaf_cyclic_shift_cokernel_finrank


/-- A scalar shift of a finite dimensional cyclic operator has kernel dimension at most one. -/
theorem IntersectionProductScaf_cyclic_shift_kernel_finrank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (F : Module.End K V) (v : V)
    (hv : Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) = ⊤) (c : K) :
    Module.finrank K (LinearMap.ker (F - c • (LinearMap.id : Module.End K V))) ≤ 1 := by
  have hb := IntersectionProductScaf_cyclic_shift_cokernel_finrank F v hv c
  have hr := (F - c • (LinearMap.id : Module.End K V)).finrank_range_add_finrank_ker
  have hq := (LinearMap.range (F - c • (LinearMap.id : Module.End K V))).finrank_quotient_add_finrank
  omega
#print axioms IntersectionProductScaf_cyclic_shift_kernel_finrank

/-- Every member of the pencil of a cyclic operator has kernel dimension at most one. -/
theorem IntersectionProductScaf_cyclic_pencil_kernel_finrank
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (F : Module.End K V) (v : V)
    (hv : Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) = ⊤) (t : K) :
    Module.finrank K (LinearMap.ker ((1 - t) • (LinearMap.id : Module.End K V) + t • F)) ≤ 1 := by
  by_cases ht : t = 0
  · subst t
    rw [sub_zero, one_smul, zero_smul, add_zero, LinearMap.ker_id]
    simp
  have he : (1 - t) • (LinearMap.id : Module.End K V) + t • F =
      t • (F - ((t - 1) / t) • (LinearMap.id : Module.End K V)) := by
    have hc : t * ((t - 1) / t) = t - 1 := by field_simp
    rw [smul_sub, smul_smul, hc, sub_smul, one_smul, sub_smul, one_smul]
    abel
  rw [he, LinearMap.ker_smul _ t ht]
  exact IntersectionProductScaf_cyclic_shift_kernel_finrank F v hv _
#print axioms IntersectionProductScaf_cyclic_pencil_kernel_finrank

/-- General translation pencils have kernels of dimension at most one at every parameter. -/
theorem IntersectionProductScaf_generic_pencil_kernel_finrank {n : ℕ} :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, Module.finrank ℂ (LinearMap.ker
        (Matrix.toLin' ((1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
          t • Matrix.of (fun i j => a (i, j))))) ≤ 1} := by
  let v : Fin (n + 1) → ℂ := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa [v] using h0
  refine (IntersectionProductScaf_generic_krylov_det_ne_zero v hv).mono ?_
  intro a ha t
  have hs := IntersectionProductScaf_krylov_det_ne_zero_span
    (Matrix.of (fun i j => a (i, j))) v (by simpa using ha)
  rw [map_add, map_smul, map_smul, Matrix.toLin'_one]
  exact IntersectionProductScaf_cyclic_pencil_kernel_finrank _ v hs t
#print axioms IntersectionProductScaf_generic_pencil_kernel_finrank

/-- A cyclic vector supplies one extra direction beside the image of each scalar shift. -/
theorem IntersectionProductScaf_cyclic_shift_decomposition
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Module.End K V) (v : V)
    (hv : Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) = ⊤) (c : K) (w : V) :
    ∃ u : V, ∃ r : K, w = (F - c • (LinearMap.id : Module.End K V)) u + r • v := by
  let A : Module.End K V := F - c • (LinearMap.id : Module.End K V)
  let q := (LinearMap.range A).mkQ
  have hs := IntersectionProductScaf_cyclic_shift_quotient_span F v hv c
  have hw : q w ∈ Submodule.span K {q v} := by rw [hs]; trivial
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
  have hz : q (w - r • v) = 0 := by rw [map_sub, map_smul, hr, sub_self]
  obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range A)).mp hz
  refine ⟨u, r, ?_⟩
  change w = A u + r • v
  rw [hu, sub_add_cancel]
#print axioms IntersectionProductScaf_cyclic_shift_decomposition

/-- A cyclic vector supplies one extra direction beside the image of every pencil member. -/
theorem IntersectionProductScaf_cyclic_pencil_decomposition
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Module.End K V) (v : V)
    (hv : Submodule.span K (Set.range (fun k : ℕ => (F ^ k) v)) = ⊤) (t : K) (w : V) :
    ∃ u : V, ∃ r : K, w = ((1 - t) • (LinearMap.id : Module.End K V) + t • F) u + r • v := by
  by_cases ht : t = 0
  · refine ⟨w, 0, ?_⟩
    simp [ht]
  obtain ⟨u, r, hu⟩ := IntersectionProductScaf_cyclic_shift_decomposition F v hv ((t - 1) / t) w
  refine ⟨t⁻¹ • u, r, ?_⟩
  have he : (1 - t) • (LinearMap.id : Module.End K V) + t • F =
      t • (F - ((t - 1) / t) • (LinearMap.id : Module.End K V)) := by
    have hc : t * ((t - 1) / t) = t - 1 := by field_simp
    rw [smul_sub, smul_smul, hc, sub_smul, one_smul, sub_smul, one_smul]
    abel
  rw [he, LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
  exact hu
#print axioms IntersectionProductScaf_cyclic_pencil_decomposition

/-- General pencil rows together with the first coordinate span every coordinate vector. -/
theorem IntersectionProductScaf_generic_pencil_row_decomposition {n : ℕ} :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, ∀ w : Fin (n + 1) → ℂ, ∃ u : Fin (n + 1) → ℂ, ∃ r : ℂ,
        w = (((1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
          t • Matrix.of (fun i j => a (i, j)))ᵀ) *ᵥ u + r • Pi.single 0 1} := by
  let v : Fin (n + 1) → ℂ := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa [v] using h0
  refine ((IntersectionProductScaf_generic_krylov_det_ne_zero v hv).comap
    Prod.swap (Equiv.prodComm _ _).injective).mono ?_
  intro a ha t w
  have hs := IntersectionProductScaf_krylov_det_ne_zero_span
    (Matrix.of (fun i j => a (j, i))) v (by simpa [Function.comp_def] using ha)
  obtain ⟨u, r, hu⟩ := IntersectionProductScaf_cyclic_pencil_decomposition _ v hs t w
  refine ⟨u, r, ?_⟩
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    ← Matrix.toLin'_apply, map_add, map_smul, map_smul, Matrix.toLin'_one]
  exact hu
#print axioms IntersectionProductScaf_generic_pencil_row_decomposition

open MvPolynomial in
/-- Linear substitution transports coefficient vectors by the transpose matrix. -/
theorem IntersectionProductScaf_linear_form_substitution
    {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (u : σ → ℂ) :
    a3r_lin A (∑ i, C (u i) * X i) = ∑ i, C ((Aᵀ *ᵥ u) i) * X i := by
  rw [map_sum]
  simp only [map_mul, a3r_lin_C, a3r_lin_X, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  ring
#print axioms IntersectionProductScaf_linear_form_substitution

open MvPolynomial in
/-- One extra coordinate gives a polynomial presentation of a quotient under linear substitution. -/
theorem IntersectionProductScaf_linear_substitution_polynomial_presentation
    {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (j : σ)
    (hgen : ∀ i, ∃ p : MvPolynomial σ ℂ, ∃ c : ℂ,
      X i = a3r_lin A p + C c * X j)
    (P Q : Ideal (MvPolynomial σ ℂ))
    (hPQ : P ≤ Q.comap (a3r_lin A).toRingHom) :
    ∃ Φ : Polynomial (MvPolynomial σ ℂ ⧸ P) →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q),
      Function.Surjective Φ ∧
      ∀ p, Φ (Polynomial.C (Ideal.Quotient.mk P p)) = Ideal.Quotient.mk Q (a3r_lin A p) := by
  let f := (Ideal.Quotient.mkₐ ℂ Q).comp (a3r_lin A)
  let g : (MvPolynomial σ ℂ ⧸ P) →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q) :=
    Ideal.Quotient.liftₐ P f (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hPQ hp))
  let Φ := Polynomial.eval₂AlgHom g (Ideal.Quotient.mk Q (X j)) (fun _ => Commute.all _ _)
  have hC (p : MvPolynomial σ ℂ) :
      Φ (Polynomial.C (Ideal.Quotient.mk P p)) = Ideal.Quotient.mk Q (a3r_lin A p) := by
    simp only [Φ, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_C]
    rfl
  have hX : Φ Polynomial.X = Ideal.Quotient.mk Q (X j) := by simp [Φ]
  refine ⟨Φ, ?_, hC⟩
  let S := Φ.range
  have hlin (p : MvPolynomial σ ℂ) : Ideal.Quotient.mk Q (a3r_lin A p) ∈ S :=
    ⟨Polynomial.C (Ideal.Quotient.mk P p), hC p⟩
  have hc (c : ℂ) : Ideal.Quotient.mk Q (C c) ∈ S := by
    simpa only [a3r_lin_C] using hlin (C c)
  have hx (i : σ) : Ideal.Quotient.mk Q (X i) ∈ S := by
    obtain ⟨p, c, he⟩ := hgen i
    rw [he, map_add, map_mul]
    exact S.add_mem (hlin p) (S.mul_mem (hc c) ⟨Polynomial.X, hX⟩)
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk Q p ∈ S
  induction p using MvPolynomial.induction_on with
  | C c => exact hc c
  | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul] using S.mul_mem hp (hx i)
#print axioms IntersectionProductScaf_linear_substitution_polynomial_presentation

open MvPolynomial in
/-- A row decomposition expresses each variable using the substituted ring and one coordinate. -/
theorem IntersectionProductScaf_linear_substitution_extra_coordinate
    {σ : Type} [Fintype σ] [DecidableEq σ] (A : Matrix σ σ ℂ) (j : σ)
    (hrow : ∀ w : σ → ℂ, ∃ u : σ → ℂ, ∃ r : ℂ,
      w = Aᵀ *ᵥ u + r • Pi.single j 1) :
    ∀ i, ∃ p : MvPolynomial σ ℂ, ∃ c : ℂ, X i = a3r_lin A p + C c * X j := by
  intro i
  obtain ⟨u, r, hu⟩ := hrow (Pi.single i 1)
  refine ⟨∑ k, C (u k) * X k, r, ?_⟩
  have h := congrArg (fun w : σ → ℂ => ∑ k, C (w k) * X k) hu
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, add_mul,
    Finset.sum_add_distrib] at h
  rw [← IntersectionProductScaf_linear_form_substitution] at h
  simpa [Pi.single_apply, mul_ite, ite_mul, apply_ite] using h
#print axioms IntersectionProductScaf_linear_substitution_extra_coordinate

open MvPolynomial in
/-- A nonzero equation lost by linear substitution compensates for the extra coordinate. -/
theorem IntersectionProductScaf_linear_substitution_quotient_dimension
    {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (j : σ)
    (hgen : ∀ i, ∃ p : MvPolynomial σ ℂ, ∃ c : ℂ,
      X i = a3r_lin A p + C c * X j)
    (P Q : Ideal (MvPolynomial σ ℂ)) [P.IsPrime]
    (hPQ : P ≤ Q.comap (a3r_lin A).toRingHom)
    (p : MvPolynomial σ ℂ) (hp : p ∉ P) (hAp : a3r_lin A p ∈ Q) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ P) := by
  obtain ⟨Φ, hΦ, hC⟩ :=
    IntersectionProductScaf_linear_substitution_polynomial_presentation A j hgen P Q hPQ
  have hr : Polynomial.C (Ideal.Quotient.mk P p) ≠ 0 := by
    intro h
    exact hp (Ideal.Quotient.eq_zero_iff_mem.mp (Polynomial.C_injective (by simpa using h)))
  have hz : Φ (Polynomial.C (Ideal.Quotient.mk P p)) = 0 := by
    rw [hC]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hAp
  have hd := ringKrullDim_succ_le_of_surjective Φ.toRingHom hΦ
    (mem_nonZeroDivisors_of_ne_zero hr) hz
  rw [Polynomial.ringKrullDim_of_isNoetherianRing] at hd
  exact a3r_withBot_le_of_add_le_add 1 hd
#print axioms IntersectionProductScaf_linear_substitution_quotient_dimension

open MvPolynomial
/-- The successive-iterate determinant as a polynomial in the initial vector. -/
def IntersectionProductScaf_krylovPolynomial {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : MvPolynomial (Fin (n + 1)) ℂ :=
  (IntersectionProductScaf_krylovMatrix (M.map C) (fun i => X i)).det
/-- A commuting substitution multiplies the successive-iterate polynomial by its determinant. -/
theorem IntersectionProductScaf_krylovPolynomial_substitution {n : ℕ}
    (M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hMA : Commute M A) :
    a3r_lin A (IntersectionProductScaf_krylovPolynomial M) =
      C A.det * IntersectionProductScaf_krylovPolynomial M := by
  let f := (a3r_lin A).toRingHom
  have hM : (M.map C).map f = M.map C := by
    apply Matrix.ext
    intro i j
    exact a3r_lin_C A (M i j)
  have hX : f ∘ (fun i => X i) = (A.map C) *ᵥ (fun i => X i) := by
    funext i
    exact a3r_lin_X A i
  have hc : Commute (M.map (C : ℂ →+* MvPolynomial (Fin (n + 1)) ℂ)) (A.map C) := by
    change (M.map C) * (A.map C) = (A.map C) * (M.map C)
    rw [← Matrix.map_mul, ← Matrix.map_mul, hMA.eq]
  change f (IntersectionProductScaf_krylovMatrix (M.map C) (fun i => X i)).det = _
  rw [RingHom.map_det]
  change ((IntersectionProductScaf_krylovMatrix (M.map C) (fun i => X i)).map f).det = _
  rw [IntersectionProductScaf_map_krylovMatrix, hM, hX,
    IntersectionProductScaf_krylov_mulVec_of_commute _ _ hc, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det C A).symm
#print axioms IntersectionProductScaf_krylovPolynomial_substitution

/-- Evaluating the successive-iterate polynomial gives the determinant for the evaluated vector. -/
theorem IntersectionProductScaf_krylovPolynomial_eval
    {K : Type} [CommRing K] [Algebra ℂ K] {n : ℕ}
    (θ : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    θ (IntersectionProductScaf_krylovPolynomial M) =
      (IntersectionProductScaf_krylovMatrix (M.map (algebraMap ℂ K)) (θ ∘ (fun i => X i))).det := by
  change θ.toRingHom (IntersectionProductScaf_krylovMatrix (M.map C) (fun i => X i)).det = _
  rw [RingHom.map_det]
  change ((IntersectionProductScaf_krylovMatrix (M.map C) (fun i => X i)).map θ.toRingHom).det = _
  rw [IntersectionProductScaf_map_krylovMatrix]
  congr 2
  apply Matrix.ext
  intro i j
  exact θ.commutes (M i j)
#print axioms IntersectionProductScaf_krylovPolynomial_eval

/-- A general successive-iterate polynomial is nonzero on any prime cone with a nonzero coordinate. -/
theorem IntersectionProductScaf_generic_krylovPolynomial_not_mem {n : ℕ}
    (P : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) [P.IsPrime]
    (hj : ∃ j, X j ∉ P) :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      IntersectionProductScaf_krylovPolynomial (Matrix.of fun i j => a (i, j)) ∉ P} := by
  let R := MvPolynomial (Fin (n + 1)) ℂ ⧸ P
  let K := FractionRing R
  let θ : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] K :=
    (IsScalarTower.toAlgHom ℂ R K).comp (Ideal.Quotient.mkₐ ℂ P)
  have hθ (p : MvPolynomial (Fin (n + 1)) ℂ) : θ p = 0 ↔ p ∈ P := by
    change algebraMap R K (Ideal.Quotient.mk P p) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective R K), Ideal.Quotient.eq_zero_iff_mem]
  let v := θ ∘ (fun i => X i)
  have hv : v ≠ 0 := by
    obtain ⟨j, hj⟩ := hj
    intro h
    exact hj ((hθ (X j)).mp (congrFun h j))
  refine (IntersectionProductScaf_generic_krylov_det_ne_zero v hv).mono ?_
  intro a ha hp
  apply ha
  have hz := (hθ _).mpr hp
  rw [IntersectionProductScaf_krylovPolynomial_eval] at hz
  exact hz
#print axioms IntersectionProductScaf_generic_krylovPolynomial_not_mem

/-- Singular members of a general pencil do not increase the dimension of a prescribed prime cone. -/
theorem IntersectionProductScaf_generic_singular_pencil_dimension {n : ℕ}
    (P : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) [P.IsPrime]
    (hj : ∃ j, X j ∉ P) :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, ∀ Q : Ideal (MvPolynomial (Fin (n + 1)) ℂ),
        let M := Matrix.of (fun i j => a (i, j))
        let A := (1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + t • M
        A.det = 0 → P ≤ Q.comap (a3r_lin A).toRingHom →
        ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Q) ≤
          ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P)} := by
  refine ((IntersectionProductScaf_generic_krylovPolynomial_not_mem P hj).inter
    IntersectionProductScaf_generic_pencil_row_decomposition).mono ?_
  intro a ha t Q M A hdet hPQ
  have hc : Commute M A :=
    ((Commute.one_right M).smul_right (1 - t)).add_right ((Commute.refl M).smul_right t)
  have hgen := IntersectionProductScaf_linear_substitution_extra_coordinate A 0 (ha.2 t)
  apply IntersectionProductScaf_linear_substitution_quotient_dimension A 0 hgen P Q hPQ
    (IntersectionProductScaf_krylovPolynomial M) ha.1
  rw [IntersectionProductScaf_krylovPolynomial_substitution M A hc, hdet, map_zero, zero_mul]
  exact Q.zero_mem
#print axioms IntersectionProductScaf_generic_singular_pencil_dimension

/-- An invertible linear substitution cannot increase the dimension of an inverse-image quotient. -/
theorem IntersectionProductScaf_invertible_substitution_quotient_dimension
    {σ : Type} [Fintype σ] [DecidableEq σ] (A : Matrix σ σ ℂ) (hA : IsUnit A.det)
    (P Q : Ideal (MvPolynomial σ ℂ)) (hPQ : P ≤ Q.comap (a3r_lin A).toRingHom) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ P) := by
  let f := (Ideal.Quotient.mk Q).comp (a3r_lin A).toRingHom
  have hf : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (a3r_linEquiv A hA).surjective
  let g := Ideal.Quotient.lift P f (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hPQ hp))
  exact ringKrullDim_le_of_surjective g (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)
#print axioms IntersectionProductScaf_invertible_substitution_quotient_dimension

/-- General pencil members preserve the upper dimension bound of a prescribed prime cone. -/
theorem IntersectionProductScaf_generic_pencil_quotient_dimension {n : ℕ}
    (P : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) [P.IsPrime]
    (hj : ∃ j, X j ∉ P) :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, ∀ Q : Ideal (MvPolynomial (Fin (n + 1)) ℂ),
        let A := (1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
          t • Matrix.of (fun i j => a (i, j))
        P ≤ Q.comap (a3r_lin A).toRingHom →
        ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Q) ≤
          ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P)} := by
  refine (IntersectionProductScaf_generic_singular_pencil_dimension P hj).mono ?_
  intro a ha t Q A hPQ
  by_cases hA : A.det = 0
  · exact ha t Q hA hPQ
  · exact IntersectionProductScaf_invertible_substitution_quotient_dimension A
      (isUnit_iff_ne_zero.mpr hA) P Q hPQ
#print axioms IntersectionProductScaf_generic_pencil_quotient_dimension

/-- A nonconstant parameter lowers quotient dimension after specialization. -/
theorem IntersectionProductScaf_parameter_specialization_dimension
    {R : Type} [CommRing R] (J : Ideal (Polynomial R)) [J.IsPrime]
    (c : R) (hc : Polynomial.X - Polynomial.C c ∉ J)
    (P : Ideal R) (hP : J ≤ P.comap (Polynomial.evalRingHom c)) :
    ringKrullDim (R ⧸ P) + 1 ≤ ringKrullDim (Polynomial R ⧸ J) := by
  let f := (Ideal.Quotient.mk P).comp (Polynomial.evalRingHom c)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Polynomial.C r, by simp [f]⟩
  let g := Ideal.Quotient.lift J f (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (hP hp))
  have hg : Function.Surjective g := Ideal.Quotient.lift_surjective_of_surjective _ _ hf
  have hr : Ideal.Quotient.mk J (Polynomial.X - Polynomial.C c) ≠ 0 := by
    exact fun h => hc (Ideal.Quotient.eq_zero_iff_mem.mp h)
  apply ringKrullDim_succ_le_of_surjective g hg (mem_nonZeroDivisors_of_ne_zero hr)
  simp [g, f]
#print axioms IntersectionProductScaf_parameter_specialization_dimension

/-- The leading matrix of a general translation pencil is invertible. -/
theorem IntersectionProductScaf_generic_pencil_leading_matrix {n : ℕ} :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      IsUnit ((Matrix.of (fun i j => a (i, j))) -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det} := by
  classical
  let N : Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) := fun i j => X (i, j)
  let G := (N - 1).det
  have heval (a : Fin (n + 1) × Fin (n + 1) → ℂ) :
      eval a G = ((Matrix.of (fun i j => a (i, j))) -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det := by
    dsimp only [G]
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    change eval a (N i j - if i = j then 1 else 0) =
      a (i, j) - (if i = j then 1 else 0)
    by_cases hij : i = j <;> simp [N, hij]
  refine ⟨G, ?_, fun a ha => isUnit_iff_ne_zero.mpr (by rwa [heval] at ha)⟩
  intro hz
  have he := heval (fun ij => if ij.1 = ij.2 then 2 else 0)
  have hm : (Matrix.of (fun i j : Fin (n + 1) => if i = j then (2 : ℂ) else 0)) - 1 = 1 := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> norm_num [Matrix.sub_apply, Matrix.one_apply, hij]
  rw [hz, map_zero, hm, Matrix.det_one] at he
  exact zero_ne_one he
#print axioms IntersectionProductScaf_generic_pencil_leading_matrix

/-- A quotient killing every polynomial variable has dimension at most zero. -/
theorem IntersectionProductScaf_coordinate_zero_quotient_dimension
    {σ : Type} (P : Ideal (MvPolynomial σ ℂ)) (hP : ∀ i, X i ∈ P) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) ≤ 0 := by
  have hs : Function.Surjective (algebraMap ℂ (MvPolynomial σ ℂ ⧸ P)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨c, rfl⟩
    | add p q hp hq =>
      obtain ⟨c, hc⟩ := hp
      obtain ⟨d, hd⟩ := hq
      exact ⟨c + d, by rw [map_add, map_add, hc, hd]⟩
    | mul_X p i hp =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hP i), mul_zero]
  have hd := ringKrullDim_le_of_surjective (algebraMap ℂ (MvPolynomial σ ℂ ⧸ P)) hs
  simpa using hd
#print axioms IntersectionProductScaf_coordinate_zero_quotient_dimension

/-- A quotient with one extra coordinate has dimension at most one above the input quotient. -/
theorem IntersectionProductScaf_linear_substitution_quotient_dimension_le_add_one
    {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (j : σ)
    (hgen : ∀ i, ∃ p : MvPolynomial σ ℂ, ∃ c : ℂ,
      X i = a3r_lin A p + C c * X j)
    (P Q : Ideal (MvPolynomial σ ℂ))
    (hPQ : P ≤ Q.comap (a3r_lin A).toRingHom) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ P) + 1 := by
  obtain ⟨Φ, hΦ, _⟩ :=
    IntersectionProductScaf_linear_substitution_polynomial_presentation A j hgen P Q hPQ
  have hd := ringKrullDim_le_of_surjective Φ.toRingHom hΦ
  simpa only [Polynomial.ringKrullDim_of_isNoetherianRing] using hd
#print axioms IntersectionProductScaf_linear_substitution_quotient_dimension_le_add_one

/-- General pencil inverse images satisfy the prime-cone bound with allowance for the vertex. -/
theorem IntersectionProductScaf_generic_pencil_quotient_dimension_with_vertex {n : ℕ}
    (P : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) [P.IsPrime] :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, ∀ Q : Ideal (MvPolynomial (Fin (n + 1)) ℂ),
        let A := (1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
          t • Matrix.of (fun i j => a (i, j))
        P ≤ Q.comap (a3r_lin A).toRingHom →
        ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Q) ≤
          max (ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P)) 1} := by
  classical
  by_cases hj : ∃ j, X j ∉ P
  · refine (IntersectionProductScaf_generic_pencil_quotient_dimension P hj).mono ?_
    intro a ha t Q A hPQ
    exact (ha t Q hPQ).trans (le_max_left _ _)
  · push Not at hj
    have hd := IntersectionProductScaf_coordinate_zero_quotient_dimension P hj
    refine IntersectionProductScaf_generic_pencil_row_decomposition.mono ?_
    intro a ha t Q A hPQ
    have hgen := IntersectionProductScaf_linear_substitution_extra_coordinate A 0 (ha t)
    have hb := IntersectionProductScaf_linear_substitution_quotient_dimension_le_add_one A 0 hgen P Q hPQ
    calc
      ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Q) ≤
          ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P) + 1 := hb
      _ ≤ 0 + 1 := add_le_add hd le_rfl
      _ = 1 := zero_add 1
      _ ≤ max (ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P)) 1 := le_max_right _ _
#print axioms IntersectionProductScaf_generic_pencil_quotient_dimension_with_vertex

/-- One general pencil controls inverse images of every minimal component of an ideal. -/
theorem IntersectionProductScaf_generic_pencil_minimal_component_dimension {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℂ)) :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, ∀ Q : Ideal (MvPolynomial (Fin (n + 1)) ℂ), Q.IsPrime →
        let A := (1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
          t • Matrix.of (fun i j => a (i, j))
        I ≤ Q.comap (a3r_lin A).toRingHom →
        ∃ P ∈ I.minimalPrimes, P ≤ Q.comap (a3r_lin A).toRingHom ∧
          ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Q) ≤
            max (ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P)) 1} := by
  let U := fun P : Ideal (MvPolynomial (Fin (n + 1)) ℂ) =>
    {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, ∀ Q : Ideal (MvPolynomial (Fin (n + 1)) ℂ),
        let A := (1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
          t • Matrix.of (fun i j => a (i, j))
        P ≤ Q.comap (a3r_lin A).toRingHom →
        ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Q) ≤
          max (ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P)) 1}
  have hU : ∀ P ∈ I.minimalPrimes, a3r_Generic (U P) := by
    intro P hP
    have : P.IsPrime := hP.1.1
    exact IntersectionProductScaf_generic_pencil_quotient_dimension_with_vertex P
  refine (a3r_generic_biInter I.minimalPrimes I.finite_minimalPrimes_of_isNoetherianRing U hU).mono ?_
  intro a ha t Q hQ A hI
  have : Q.IsPrime := hQ
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hI
  exact ⟨P, hP, hPQ, ha P hP t Q hPQ⟩
#print axioms IntersectionProductScaf_generic_pencil_minimal_component_dimension

/-- A general pencil over an endpoint has a strict dimension drop from a nonconstant relative cone. -/
theorem IntersectionProductScaf_generic_endpoint_pencil_dimension {n : ℕ}
    (J : Ideal (Polynomial (MvPolynomial (Fin (n + 1)) ℂ))) [J.IsPrime]
    (c : ℂ) (hc : Polynomial.X - Polynomial.C (C c) ∉ J)
    (hd : 2 ≤ ringKrullDim (Polynomial (MvPolynomial (Fin (n + 1)) ℂ) ⧸ J)) :
    a3r_Generic {a : Fin (n + 1) × Fin (n + 1) → ℂ |
      ∀ t : ℂ, ∀ Q : Ideal (MvPolynomial (Fin (n + 1)) ℂ), Q.IsPrime →
        let A := (1 - t) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
          t • Matrix.of (fun i j => a (i, j))
        J.map (Polynomial.evalRingHom (C c)) ≤ Q.comap (a3r_lin A).toRingHom →
        ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Q) + 1 ≤
          ringKrullDim (Polynomial (MvPolynomial (Fin (n + 1)) ℂ) ⧸ J)} := by
  refine (IntersectionProductScaf_generic_pencil_minimal_component_dimension
    (J.map (Polynomial.evalRingHom (C c)))).mono ?_
  intro a ha t Q hQ A hJ
  obtain ⟨P, hP, hPQ, hdim⟩ := ha t Q hQ hJ
  have hpdim := IntersectionProductScaf_parameter_specialization_dimension J (C c) hc P
    (Ideal.map_le_iff_le_comap.mp hP.1.2)
  rcases le_max_iff.mp hdim with h | h
  · exact (add_le_add h le_rfl).trans hpdim
  · exact (add_le_add h le_rfl).trans (by convert hd using 1 <;> norm_num)
#print axioms IntersectionProductScaf_generic_endpoint_pencil_dimension

end HodgeLean.Adapters
