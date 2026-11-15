import HodgeLean.Foundations.Program.SchoenTransferQ3AmbientSliceComparison

/-! Local normal comparison with all slice neighbourhood refinements constructed. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular AlgebraicGeometry.SingularCycles HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Continuity constructs compatible source and target neighbourhoods for
the actual finite flat normal-slice comparison. -/
theorem s4_q3_local_ambient_finite_flat_slice_comparison
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    {P Q : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    [Smooth P.hom] [Smooth Q.hom]
    [T1Space (ComplexPoint P)] [T1Space (ComplexPoint Q)]
    (f : P ⟶ Q) [IsFinite f.left] [Flat f.left]
    (q : C(M, N)) (jX : C(ComplexPoint P, M)) (jZ : C(ComplexPoint Q, N))
    (hsquare : ∀ y, q (jX y) = jZ (Point.map f y))
    (S : Set M) (T : Set N) (hST : ∀ y, q y ∈ T → y ∈ S)
    (eX : OpenPartialHomeomorph M (E × (Fin k → ℂ)))
    (eZ : OpenPartialHomeomorph N (F × (Fin k → ℂ)))
    (hSX : ∀ y ∈ eX.source, y ∈ S ↔ (eX y).2 = 0)
    (hTZ : ∀ y ∈ eZ.source, y ∈ T ↔ (eZ y).2 = 0)
    (sX : OpenPartialHomeomorph (ComplexPoint P) ((Fin 0 → ℂ) × (Fin k → ℂ)))
    (sZ : OpenPartialHomeomorph (ComplexPoint Q) ((Fin 0 → ℂ) × (Fin k → ℂ)))
    (hsX : a3b4_IsHolChart P.hom sX) (hsZ : a3b4_IsHolChart Q.hom sZ)
    (x : ComplexPoint P) (hx : x ∈ sX.source) (hz : Point.map f x ∈ sZ.source)
    (hx0 : sX x = 0) (hz0 : sZ (Point.map f x) = 0)
    (hxe : jX x ∈ eX.source) (hxe0 : (eX (jX x)).2 = 0)
    (VZ : Set N) (hVZ : VZ ⊆ eZ.source)
    (hVZo : IsOpen VZ) (hzV : jZ (Point.map f x) ∈ VZ)
    (hnX : ∀ y ∈ sX.source, (eX (jX y)).2 = (sX y).2)
    (hnZ : ∀ y ∈ sZ.source, (eZ (jZ y)).2 = (sZ y).2)
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of N) Tᶜ) (2 * k))
    (a : ℚ)
    (hα : relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap VZ T) α =
      a • chartNormalProjectionCoclass F k eZ T hTZ VZ hVZ) :
    ∃ (V : Set M) (hVe : V ⊆ eX.source), IsOpen V ∧ jX x ∈ V ∧
      relativeCohomologyMap ℚ (2 * k) (a3b4_neighborhoodPairMap V S)
        (relativeCohomologyMap ℚ (2 * k)
          (a3b4_supportPairMap (TopCat.ofHom q) S T hST) α) =
        (a * ((pointFibreLength f.left x.underlying).toNat : ℚ)) •
          chartNormalProjectionCoclass E k eX S hSX V hVe := by
  let OX := q ⁻¹' VZ
  have hOX : IsOpen OX := hVZo.preimage q.continuous
  let eX' := eX.restrOpen OX hOX
  have hxOX : jX x ∈ OX := by change q (jX x) ∈ VZ; rw [hsquare x]; exact hzV
  have hxe' : jX x ∈ eX'.source := ⟨hxe, hxOX⟩
  let NX := flattenedSupportNeighborhood E k eX' (jX x) hxe'
  have hNX := flattenedSupportNeighborhood_subset_source E k eX' (jX x) hxe'
  let OZ := jZ ⁻¹' VZ
  have hOZ : IsOpen OZ := hVZo.preimage jZ.continuous
  let sZ' := sZ.restrOpen OZ hOZ
  have hz' : Point.map f x ∈ sZ'.source := ⟨hz, hzV⟩
  let NT := flattenedSupportNeighborhood (Fin 0 → ℂ) k sZ' (Point.map f x) hz'
  have hNT := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) k sZ' (Point.map f x) hz'
  let OS := (jX ⁻¹' (NX : Set M)) ∩ (Point.map f ⁻¹' (NT : Set (ComplexPoint Q)))
  have hOS : IsOpen OS := (NX.isOpen.preimage jX.continuous).inter
    (NT.isOpen.preimage (Point.continuous_map f))
  let sX' := sX.restrOpen OS hOS
  have hxOS : x ∈ OS :=
    ⟨mem_flattenedSupportNeighborhood E k eX' (jX x) hxe',
      mem_flattenedSupportNeighborhood (Fin 0 → ℂ) k sZ' (Point.map f x) hz'⟩
  have hx' : x ∈ sX'.source := ⟨hx, hxOS⟩
  have hSX' : ∀ y ∈ eX'.source, y ∈ S ↔ (eX' y).2 = 0 :=
    fun y hy => hSX y hy.1
  have hsX' : a3b4_IsHolChart P.hom sX' :=
    ⟨fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
      (fun _ h => h.1) (hsX.1 j),
      fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
        (fun _ h => h.1) (hsX.2 j)⟩
  have hsZ' : a3b4_IsHolChart Q.hom sZ' :=
    ⟨fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
      (fun _ h => h.1) (hsZ.1 j),
      fun j => HodgeLean.Foundations.Analytic.anb_isHolFun_restrict _
        (fun _ h => h.1) (hsZ.2 j)⟩
  have hNS := flattenedSupportNeighborhood_subset_source (Fin 0 → ℂ) k sX' x hx'
  have hcalc := s4_q3_ambient_finite_flat_slice_comparison E F k f q jX jZ hsquare S T hST
    eX' eZ hSX' hTZ sX' sZ' hsX' hsZ' x hx' hz' hx0 hz0 hxe' hxe0 VZ hVZ
    (fun y hy => (hNX hy).2)
    (fun y hy => (hNS hy).2.1)
    (fun y hy => (hNT hy).2)
    (fun y hy => (hNS hy).2.2)
    (fun y hy => hnX y (hNS hy).1)
    (fun y hy => hnZ y (hNT hy).1) α a hα
  refine ⟨NX, (fun y hy => (hNX hy).1), NX.isOpen,
    mem_flattenedSupportNeighborhood E k eX' (jX x) hxe', ?_⟩
  exact hcalc

end HodgeLean.Foundations.Program
