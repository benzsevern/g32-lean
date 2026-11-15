import HodgeLean.Foundations.Program.SchoenTowerL1bAffineGeneratorRefinement

/-! Simultaneous exact generators on a refinement of a prescribed affine open.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two exact branch generators on a prescribed affine open extend to etale coordinates after refinement whenever the same ideals already occur in an etale chart. -/
theorem s2v_l1b_simultaneous_generator_extension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    (I : Fin 2 → X.left.IdealSheafData) (p : ComplexPoint X)
    (hps : ∀ k, p.underlying ∈ (I k).support)
    (O : X.left.affineOpens) (w : Fin 2 ⊕ Fin n → Γ(X.left, O))
    (hpO : p ∈ Point.overOpen O.1)
    (hEt : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ O.1 le_top).hom w).Etale)
    (hIO : ∀ k, (I k).ideal O = Ideal.span {w (Sum.inl k)})
    (U₀ : X.left.affineOpens) (v : Fin 2 → Γ(X.left, U₀))
    (hpU : p ∈ Point.overOpen U₀.1)
    (hIU : ∀ k, (I k).ideal U₀ = Ideal.span {v k}) :
    ∃ (V : X.left.affineOpens) (hV : V.1 ≤ U₀.1)
      (z : Fin 2 ⊕ Fin n → Γ(X.left, V)),
      p ∈ Point.overOpen V.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom z).Etale ∧
      (∀ k, z (Sum.inl k) = (X.left.presheaf.map (homOfLE hV).op).hom (v k)) ∧
      ∀ k, (I k).ideal V = Ideal.span {z (Sum.inl k)} := by
  obtain ⟨W₁, hW₁, hpW, hW⟩ := exists_isAffineOpen_mem_and_subset
    (show p.underlying ∈ O.1 ⊓ U₀.1 from ⟨hpO, hpU⟩)
  let W : X.left.affineOpens := ⟨W₁, hW₁⟩
  have hWO : W.1 ≤ O.1 := fun _ hx => (hW hx).1
  have hWU : W.1 ≤ U₀.1 := fun _ hx => (hW hx).2
  let rO := (X.left.presheaf.map (homOfLE hWO).op).hom
  let rU := (X.left.presheaf.map (homOfLE hWU).op).hom
  let f : Fin 2 ⊕ Fin n → Γ(X.left, W) := fun i => rO (w i)
  let g : Fin 2 ⊕ Fin n → Γ(X.left, W) := Sum.elim (fun k => rU (v k)) (fun k => f (Sum.inr k))
  have hf (k : Fin 2) : (I k).ideal W = Ideal.span {f (Sum.inl k)} := by
    rw [← (I k).map_ideal hWO, hIO k, Ideal.map_span, Set.image_singleton]
    rfl
  have hg (k : Fin 2) : (I k).ideal W = Ideal.span {g (Sum.inl k)} := by
    rw [← (I k).map_ideal hWU, hIU k, Ideal.map_span, Set.image_singleton]
    rfl
  have hgen (i : Fin 2 ⊕ Fin n) : Ideal.span {g i} = Ideal.span {f i} := by
    rcases i with k | k
    · exact (hg k).symm.trans (hf k)
    · rfl
  have hz (i : Fin 2 ⊕ Fin n) : Point.evaluate W.1 (f i) p = 0 ∨ g i = f i := by
    rcases i with k | k
    · exact Or.inl ((s2v_l1b_evaluate_zero_iff_support X (I k) W _ (hf k) p hpW).mpr (hps k))
    · exact Or.inr rfl
  have hEtW : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ W.1 le_top).hom f).Etale :=
    s2v_l1b_affine_coordinate_restriction X O W hWO w hEt
  obtain ⟨V, hVW, hpV, hEtV⟩ :=
    s2v_l1b_affine_generator_refinement X W f g hEtW hgen p hpW hz
  let hV : V.1 ≤ U₀.1 := hVW.trans hWU
  let rV := (X.left.presheaf.map (homOfLE hVW).op).hom
  let z : Fin 2 ⊕ Fin n → Γ(X.left, V) := fun i => rV (g i)
  refine ⟨V, hV, z, hpV, hEtV, ?_, ?_⟩
  · intro k
    change (X.left.presheaf.map (homOfLE hVW).op)
      ((X.left.presheaf.map (homOfLE hWU).op) (v k)) = _
    change ((X.left.presheaf.map (homOfLE hWU).op) ≫
      X.left.presheaf.map (homOfLE hVW).op) (v k) = _
    rw [← Functor.map_comp]
    rfl
  · intro k
    rw [← (I k).map_ideal hVW, hg k, Ideal.map_span, Set.image_singleton]
    rfl

end HodgeLean.Foundations.Program
