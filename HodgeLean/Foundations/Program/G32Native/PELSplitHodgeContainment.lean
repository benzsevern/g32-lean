import HodgeLean.Foundations.Program.G32Native.PELSplitTransport
import HodgeLean.Foundations.Program.G32Native.PELHodgeTensorContainment
import HodgeLean.Foundations.Program.G32Native.PELHodgePolarization
import HodgeLean.Foundations.Program.G32Native.PELHodgeFamilyClosure

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
namespace PELSplitFamily
variable {R : PELSplitReference} (F : PELSplitFamily R)

/-- The rational polarization matrix in the common marking. -/
theorem form_matrix_rat (z : PELSplitComponent R) :
    LinearMap.toMatrix₂ (F.basis z) (F.basis z)
      (polarizationForm (torusCohomology_cupProductOf (F.fibre z).X)
        (F.polarized z).nondegenerate) = R.form := by
  ext i j
  simpa only [LinearMap.toMatrix₂_apply, PELSplitFamily.basis,
    Module.Basis.map_apply, PELSplitReference.form] using
    F.form_eq z (R.basis i) (R.basis j)

/-- Every fibre group lies in the connected reference isometry group.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.1, 3.2. -/
theorem hodgeGroup_subset_isometries (z : PELSplitComponent R) :
    F.hodgeGroup z ⊆ pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) := by
  have hu := polarized_hodgeGroup_subset_connected_pel (F.fibre z).X (F.fibre z).pol
    (F.polarized z).nondegenerate (F.polarized z).positive
    (fun i : Fin 4 => F.action z (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))
    (F.basis z)
  rw [F.form_matrix_rat z] at hu
  have hm : (Set.range fun i : Fin 4 =>
      (LinearMap.toMatrix (F.basis z) (F.basis z)
        (abelianEnd0Action (F.fibre z).X
          (F.action z (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))).unop).map
            (algebraMap ℚ ℂ)) = (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) := by
    congr 1
    funext i
    exact congrArg (fun M => M.map (algebraMap ℚ ℂ)) (F.action_matrix z _)
  rw [hm] at hu
  exact hu

/-- The independently generated family group is connected.
Source: Borel, Linear Algebraic Groups, second edition, §2.2. -/
theorem genericGroup_isConnected :
    @IsConnected _ (g1_zariski ℂ 12) F.genericGroup := by
  letI : Nonempty (PELSplitComponent R) := ⟨pelSplitBasePoint R⟩
  exact pel_family_group_isConnected F.hodgeGroup
    (fun z => g2_isRatAlgSubgroup_hodgeGroup _ _ (F.basis z))
    (fun z => g2_hodgeGroup_isConnected _ _ (F.basis z))

/-- The family group lies in the connected reference isometry group.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.1, 3.2. -/
theorem genericGroup_subset_isometries :
    F.genericGroup ⊆ pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) := by
  let S := Set.range fun i : Fin 4 =>
    R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)
  let G := pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
    (Set.range fun i : Fin 4 =>
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
        (algebraMap ℚ ℂ))
  have ha : g2_IsRatAlgSubgroup (G.carrier : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) := by
    simpa only [G, S, ← Set.range_comp, Function.comp_def] using pelIsometryGroup_isRatAlg R.form S
  have hs : F.genericGroup ⊆ G.carrier := by
    intro g hg
    apply hg _ ⟨ha, ?_⟩
    intro z
    exact (F.hodgeGroup_subset_isometries z).trans
      (@connectedComponentIn_subset _ (g1_zariski ℂ 12) G.carrier 1)
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin 12) ℂ) ∈ F.genericGroup := by
    intro G hG
    exact hG.1.2.1
  exact @IsPreconnected.subset_connectedComponentIn _ (g1_zariski ℂ 12)
    _ _ _ (@IsConnected.isPreconnected _ (g1_zariski ℂ 12) _
      F.genericGroup_isConnected) h1 hs

#print axioms hodgeGroup_subset_isometries
#print axioms genericGroup_isConnected
#print axioms genericGroup_subset_isometries
end PELSplitFamily
end HodgeLean.Foundations.Program.GeneralTypeIII
