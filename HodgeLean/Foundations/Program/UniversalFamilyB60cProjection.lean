import HodgeLean.Foundations.Program.UniversalFamilyB60cTransversality

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- A positive three-plane in the negative eigenspace projects bijectively onto
the three positive coordinates. -/
theorem b60c_negative_projection_bijective
    (F : Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (hdim : Module.finrank ℂ F = 3)
    (heig : F ≤ Module.End.eigenspace b60_omegaC (-Complex.I * (Real.sqrt 3 : ℂ)))
    (hpos : ∀ x ∈ F, x ≠ 0 →
      0 < (Complex.I * b60_E.baseChange ℂ x (b2_conj b60_Lattice x)).re) :
    Function.Bijective (fun x : F => fun i : Fin 3 =>
      b60c_eigenBasis.repr (x : ℂ ⊗[ℤ] b60_Lattice) (0, Fin.castAdd 3 i)) := by
  let p : F →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi fun i =>
    (b60c_eigenBasis.coord (0, Fin.castAdd 3 i)).comp F.subtype
  have hinj : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro x hx
    change x = 0
    by_contra hx0
    have hxne : (x : ℂ ⊗[ℤ] b60_Lattice) ≠ 0 := by
      intro h
      exact hx0 (Subtype.ext h)
    have hp := b60c_negative_eigen_positive x
      (Module.End.mem_eigenspace_iff.mp (heig x.property)) (hpos x x.property hxne)
    have hzero (i : Fin 3) :
        b60c_eigenBasis.repr (x : ℂ ⊗[ℤ] b60_Lattice) (0, Fin.castAdd 3 i) = 0 :=
      congrFun hx i
    simp only [hzero, Complex.normSq_zero, Finset.sum_const_zero] at hp
    exact (not_lt_of_ge (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)) hp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim)).mp hinj⟩

#print axioms b60c_negative_projection_bijective

open scoped Matrix ComplexOrder

/-- A positive three-plane in the negative eigenspace has the explicit negative
frame of a bounded matrix chart. -/
theorem b60c_negative_plane_graph
    (F : Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (hdim : Module.finrank ℂ F = 3)
    (heig : F ≤ Module.End.eigenspace b60_omegaC (-Complex.I * (Real.sqrt 3 : ℂ)))
    (hpos : ∀ x ∈ F, x ≠ 0 →
      0 < (Complex.I * b60_E.baseChange ℂ x (b2_conj b60_Lattice x)).re) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℂ, (1 - Aᴴ * A).PosDef ∧
      F = Submodule.span ℂ (Set.range fun i : Fin 3 =>
        b60_eigen (-1) (Fin.castAdd 3 i) +
          ∑ j : Fin 3, A j i • b60_eigen (-1) (Fin.natAdd 3 j)) := by
  classical
  let p : F →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi fun i =>
    (b60c_eigenBasis.coord (0, Fin.castAdd 3 i)).comp F.subtype
  let e : F ≃ₗ[ℂ] (Fin 3 → ℂ) := LinearEquiv.ofBijective p
    (b60c_negative_projection_bijective F hdim heig hpos)
  let q : F →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi fun i =>
    (b60c_eigenBasis.coord (0, Fin.natAdd 3 i)).comp F.subtype
  let A := LinearMap.toMatrix' (q.comp e.symm.toLinearMap)
  have hupper (u : Fin 3 → ℂ) (i : Fin 3) :
      b60c_eigenBasis.repr (e.symm u : ℂ ⊗[ℤ] b60_Lattice) (0, Fin.castAdd 3 i) = u i :=
    congrFun (e.apply_symm_apply u) i
  have hlower (u : Fin 3 → ℂ) (i : Fin 3) :
      b60c_eigenBasis.repr (e.symm u : ℂ ⊗[ℤ] b60_Lattice) (0, Fin.natAdd 3 i) =
        (A *ᵥ u) i := by
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hrec (u : Fin 3 → ℂ) : (e.symm u : ℂ ⊗[ℤ] b60_Lattice) =
      (∑ i : Fin 3, u i • b60_eigen (-1) (Fin.castAdd 3 i)) +
        ∑ i : Fin 3, (A *ᵥ u) i • b60_eigen (-1) (Fin.natAdd 3 i) := by
    have h := b60c_eigen_reconstruction 0 (e.symm u)
      (by simpa using Module.End.mem_eigenspace_iff.mp (heig (e.symm u).property))
    rw [Fin.sum_univ_add (a := 3) (b := 3)] at h
    simpa only [b60c_eigenBasis_apply, hupper, hlower, ite_true] using h
  refine ⟨A, b60c_contraction_posDef A ?_, ?_⟩
  · intro u hu
    have hne : (e.symm u : ℂ ⊗[ℤ] b60_Lattice) ≠ 0 := by
      intro h
      have hz : e.symm u = 0 := Subtype.ext h
      apply hu
      calc
        u = e (e.symm u) := (e.apply_symm_apply u).symm
        _ = e 0 := congrArg e hz
        _ = 0 := e.map_zero
    have h := b60c_negative_eigen_positive (e.symm u)
      (Module.End.mem_eigenspace_iff.mp (heig (e.symm u).property))
      (hpos (e.symm u) (e.symm u).property hne)
    simpa only [hupper, hlower] using h
  · have hframe (i : Fin 3) : (e.symm (Pi.single i 1) : ℂ ⊗[ℤ] b60_Lattice) =
        b60_eigen (-1) (Fin.castAdd 3 i) +
          ∑ j : Fin 3, A j i • b60_eigen (-1) (Fin.natAdd 3 j) := by
      simpa [Pi.single_apply, Matrix.mulVec] using hrec (Pi.single i 1)
    have hb := congrArg (Submodule.map F.subtype)
      ((Pi.basisFun ℂ (Fin 3)).map e.symm).span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      ← Set.range_comp] at hb
    have hfun : (F.subtype ∘ ((Pi.basisFun ℂ (Fin 3)).map e.symm)) =
        (fun i => b60_eigen (-1) (Fin.castAdd 3 i) +
          ∑ j : Fin 3, A j i • b60_eigen (-1) (Fin.natAdd 3 j)) := by
      funext i
      simpa only [Function.comp_apply, Module.Basis.map_apply,
        Pi.basisFun_apply, Submodule.subtype_apply] using hframe i
    rw [hfun] at hb
    exact hb.symm

#print axioms b60c_negative_plane_graph

end HodgeLean.Foundations.Program
