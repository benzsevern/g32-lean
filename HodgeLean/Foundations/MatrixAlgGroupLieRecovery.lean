import HodgeLean.Foundations.MatrixAlgGroupLieBasic

/-! # Recovery of a connected matrix group from its Lie algebra: the reduction steps

A connected `MatrixAlgGroup` has a prime vanishing ideal (its point set is Zariski irreducible),
and a proper closed subset of an irreducible set has strictly smaller Krull dimension. With the
equality `dim 𝔤 = dim G` as an explicit hypothesis, a subgroup `I ≤ G` with the same Lie algebra
as a connected `G` is all of `G`.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial Matrix HodgeLean.Foundations.Program TopologicalSpace

/-- A nonempty connected Noetherian space on which homeomorphisms act transitively is
irreducible: some point lies in exactly one irreducible component, so by transitivity every
point does, the finitely many components are disjoint, hence clopen, hence there is one.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2 (a connected algebraic group is
irreducible); Humphreys, *Linear Algebraic Groups*, §7.3. -/
theorem g1_irreducibleSpace_of_transitive {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [ConnectedSpace X] (h : ∀ x y : X, ∃ f : X ≃ₜ X, f x = y) : IrreducibleSpace X := by
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  set Z0 := irreducibleComponent x
  have hZ0 : Z0 ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨x0, -, hx0⟩ : ∃ x0 ∈ Z0, ∀ Z ∈ irreducibleComponents X, x0 ∈ Z → Z = Z0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Z0 ⊆ ⋃₀ (irreducibleComponents X \ {Z0}) := by
      intro y hy
      obtain ⟨Z, hZ, hyZ, hne⟩ := hcon y hy
      exact ⟨Z, ⟨hZ, hne⟩, hyZ⟩
    exact (mem_of_subset_sUnion_irreducibleComponents Z0 hZ0 _ hfin.sdiff
      Set.sdiff_subset hsub).2 rfl
  have huniq : ∀ y, ∀ Z1 ∈ irreducibleComponents X, ∀ Z2 ∈ irreducibleComponents X,
      y ∈ Z1 → y ∈ Z2 → Z1 = Z2 := by
    intro y Z1 hZ1 Z2 hZ2 hy1 hy2
    obtain ⟨f, hf⟩ := h y x0
    have key : ∀ Z ∈ irreducibleComponents X, y ∈ Z → f.symm ⁻¹' Z = Z0 := by
      intro Z hZ hyZ
      refine hx0 _ (preimage_mem_irreducibleComponents hZ f.symm.isOpenEmbedding
        ⟨y, hyZ, f.symm.surjective y⟩) ?_
      change f.symm x0 ∈ Z
      rwa [← hf, Homeomorph.symm_apply_apply]
    exact Set.preimage_injective.mpr f.symm.surjective
      ((key Z1 hZ1 hy1).trans (key Z2 hZ2 hy2).symm)
  have hcompl : Z0ᶜ = ⋃₀ (irreducibleComponents X \ {Z0}) := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ ⋃₀ irreducibleComponents X := by
        rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨Z, hZ, hyZ⟩ := hy'
      exact ⟨Z, ⟨hZ, fun hZe ↦ hy (hZe ▸ hyZ)⟩, hyZ⟩
    · rintro ⟨Z, ⟨hZ, hne⟩, hyZ⟩ hy0
      exact hne (huniq y Z hZ Z0 hZ0 hyZ hy0)
  have hclopen : IsClopen Z0 := by
    refine ⟨isClosed_of_mem_irreducibleComponents Z0 hZ0, ?_⟩
    rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have huniv : Z0 = Set.univ :=
    (isClopen_iff.mp hclopen).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨x, mem_irreducibleComponent⟩)
  exact (irreducibleSpace_def X).mpr (by have h := hZ0.1; rwa [huniv] at h)

variable {k : Type*} [Field k] {n : ℕ}

/-- The vanishing ideal of a Zariski-irreducible set of invertible matrices is prime.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.2 and AG.2.1. -/
theorem g1_vanishingIdealSet_isPrime (S : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hS : @IsIrreducible _ (g1_zariski k n) S) : (g1_vanishingIdealSet S).IsPrime := by
  let _ := g1_zariski k n
  have hφ : Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) k ↦
      (MvPolynomial.pointToPoint (k := k) (g1_coords g) :
        PrimeSpectrum (MvPolynomial (Fin n × Fin n) k))) := continuous_induced_dom
  have h := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp
    (hS.image _ hφ.continuousOn)
  rwa [← Set.image_image (g := MvPolynomial.pointToPoint (k := k)) (f := g1_coords),
    MvPolynomial.vanishingIdeal_pointToPoint] at h

/-- A Zariski-connected matrix algebraic group is Zariski irreducible: left translations by its
elements are homeomorphisms acting transitively, and `GL_n(k)` is a Noetherian space.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2; Humphreys, *Linear Algebraic Groups*,
§7.3. -/
theorem g1_isIrreducible_of_isConnected (G : MatrixAlgGroup k n) (hG : g1_IsConnected G) :
    @IsIrreducible _ (g1_zariski k n) (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) := by
  let _ := g1_zariski k n
  have : NoetherianSpace (Matrix.GeneralLinearGroup (Fin n) k) :=
    Topology.IsInducing.noetherianSpace (i := fun g ↦ (MvPolynomial.pointToPoint (k := k)
      (g1_coords g) : PrimeSpectrum (MvPolynomial (Fin n × Fin n) k))) ⟨rfl⟩
  have : ConnectedSpace (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) :=
    isConnected_iff_connectedSpace.mp hG
  refine isIrreducible_iff_irreducibleSpace.mpr (g1_irreducibleSpace_of_transitive ?_)
  have hcont : ∀ a : G.carrier, Continuous
      (fun g : (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) ↦
        (⟨a * g, G.carrier.mul_mem a.2 g.2⟩ :
          (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)))) := fun a ↦
    ((g1_continuous_mul_left (a : Matrix.GeneralLinearGroup (Fin n) k)).comp
      continuous_subtype_val).subtype_mk _
  intro x y
  let a : G.carrier := ⟨y * x⁻¹, G.carrier.mul_mem y.2 (G.carrier.inv_mem x.2)⟩
  let a' : G.carrier := ⟨x * y⁻¹, G.carrier.mul_mem x.2 (G.carrier.inv_mem y.2)⟩
  refine ⟨{ toFun := fun g ↦ ⟨a * g, G.carrier.mul_mem a.2 g.2⟩
            invFun := fun g ↦ ⟨a' * g, G.carrier.mul_mem a'.2 g.2⟩
            left_inv := fun g ↦ ?_
            right_inv := fun g ↦ ?_
            continuous_toFun := hcont a
            continuous_invFun := hcont a' }, ?_⟩
  · ext1; simp [a, a', mul_assoc]
  · ext1; simp [a, a', mul_assoc]
  · ext1; simp [a]

/-- The vanishing ideal of a connected matrix algebraic group is prime.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2 and AG.1.2. -/
theorem g1_vanishingIdeal_isPrime_of_isConnected (G : MatrixAlgGroup k n)
    (hG : g1_IsConnected G) : (g1_vanishingIdeal G).IsPrime :=
  g1_vanishingIdealSet_isPrime _ (g1_isIrreducible_of_isConnected G hG)

/-- A quotient by an ideal strictly larger than a prime `P` has Krull dimension different from
a finite Krull dimension of the quotient by `P`.
Source: Matsumura, *Commutative Ring Theory*, §5 (a nonzerodivisor drops the dimension). -/
theorem g1_ringKrullDim_quotient_ne_of_lt {R : Type*} [CommRing R] (P J : Ideal R) [P.IsPrime]
    (hPJ : P < J) (m : ℕ) (hm : ringKrullDim (R ⧸ P) = m) : ringKrullDim (R ⧸ J) ≠ m := by
  obtain ⟨r, hrJ, hrP⟩ := IsConcreteLE.exists_of_lt hPJ
  set r' : R ⧸ P := Ideal.Quotient.mk P r
  have hr0 : r' ≠ 0 := fun h ↦ hrP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hr : r' ∈ nonZeroDivisors (R ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  let f : (R ⧸ P) ⧸ Ideal.span {r'} →+* R ⧸ J :=
    Ideal.Quotient.lift (Ideal.span {r'}) (Ideal.Quotient.factor hPJ.le) (fun a ha ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul]
      have : Ideal.Quotient.factor hPJ.le r' = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrJ
      rw [this, zero_mul])
  have hf : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hPJ.le)
  have h2 := ringKrullDim_le_of_surjective f hf
  intro hJ
  rw [hJ] at h2
  rw [hm] at h1
  have h3 : ((m : WithBot ℕ∞) + 1) ≤ m :=
    le_trans (add_le_add_left h2 1) h1
  have h4 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : m + 1 ≤ m := by exact_mod_cast h4
  omega

/-- The intersection of two matrix algebraic groups, presented by both sets of equations.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.1 (closed subgroups). -/
def g1_inter (G H : MatrixAlgGroup k n) : MatrixAlgGroup k n where
  equations := G.equations ⊔ H.equations
  carrier := G.carrier ⊓ H.carrier
  equations_iff g := by
    rw [Subgroup.mem_inf, G.equations_iff, H.equations_iff]
    constructor
    · rintro ⟨hG, hH⟩ f hf
      have hle : G.equations ⊔ H.equations ≤ RingHom.ker (eval (g1_coords g)) :=
        sup_le (fun f hf ↦ RingHom.mem_ker.mpr (hG f hf))
          (fun f hf ↦ RingHom.mem_ker.mpr (hH f hf))
      exact RingHom.mem_ker.mp (hle hf)
    · intro h
      exact ⟨fun f hf ↦ h f (le_sup_left (a := G.equations) hf),
        fun f hf ↦ h f (le_sup_right (a := G.equations) hf)⟩

example (G H : MatrixAlgGroup k n) : (g1_inter G H).carrier = G.carrier ⊓ H.carrier := rfl

/-- A connected group `G` is contained in any subgroup `I ≤ G` with the same Lie algebra, once
the Lie algebras of `G` and `I` have the Krull dimensions of their coordinate rings: the
vanishing ideal of `G` is prime and contained in that of `I`, with the same finite dimension, so
the two ideals agree.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §7.1 and AG.10.1; Humphreys, *Linear
Algebraic Groups*, §13.1. -/
theorem g1_le_of_lie_eq_of_dim (G I : MatrixAlgGroup k n) (hG : g1_IsConnected G)
    (hIG : I.carrier ≤ G.carrier) (hlie : g1_lieAlgebra I = g1_lieAlgebra G)
    (hdimG : (Module.finrank k (g1_lieAlgebra G) : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial (Fin n × Fin n) k ⧸ g1_vanishingIdeal G))
    (hdimI : (Module.finrank k (g1_lieAlgebra I) : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial (Fin n × Fin n) k ⧸ g1_vanishingIdeal I)) :
    G.carrier ≤ I.carrier := by
  have := g1_vanishingIdeal_isPrime_of_isConnected G hG
  have hle : g1_vanishingIdeal G ≤ g1_vanishingIdeal I :=
    MvPolynomial.vanishingIdeal_anti_mono (Set.image_mono hIG)
  have heq : g1_vanishingIdeal G = g1_vanishingIdeal I := by
    by_contra hne
    rw [hlie] at hdimI
    exact g1_ringKrullDim_quotient_ne_of_lt _ _ (lt_of_le_of_ne hle hne) _ hdimG.symm
      hdimI.symm
  intro g hg
  refine (I.equations_iff g).mpr fun f hf ↦ ?_
  have hfI : f ∈ g1_vanishingIdeal I :=
    mem_vanishingIdeal_iff.mpr (by rintro _ ⟨h, hh, rfl⟩; exact (I.equations_iff h).mp hh f hf)
  rw [← heq] at hfI
  exact (mem_vanishingIdeal_iff.mp hfI) _ ⟨g, hg, rfl⟩

end HodgeLean.Foundations
