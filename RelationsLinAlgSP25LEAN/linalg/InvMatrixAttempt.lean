import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Init.Prelude
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Matrix
universe u v w

variable (i j : ℕ) 
variable (c : ℂ)
#check (Matrix.scalar (Fin i)) c

variable (m : Matrix (Fin i) (Fin i) ℂ)


@[simp]
theorem vecIsMat {i : ℕ} (V : Matrix (Fin i) (Fin 1) ℂ) 
                         (j : (Fin i)) 
                         (k : (Fin 1))
                         :
                         V j k = V j 0 := by 
                                          have t : k = 0 := by exact Fin.fin_one_eq_zero k
                                          rw[t]


/-
theorem charpolyRootsEigenvalueEq {i : ℕ}
(M : Matrix (Fin i) (Fin i) ℂ) :
∀ x ∈ M.charpoly.roots, (is_eigenvalue M x) := by
  intro eig root
  rw[is_eigenvalue]
  rw[charpoly] at root
  rw[charmatrix] at root
-/
                                              

/-theorem detMulEigenvalue {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ) :
                         M.det = M.eigenvalues := by sorry
-- char poly roots are eigenvalues

theorem temporary {i : ℕ}
                  (M : Matrix (Fin i) (Fin i) ℂ) 
                  (c : Matrix (Fin i) (Fin i) ℂ) 
                  (v : Matrix (Fin i) (Fin 1) ℂ): 
                  (M - c) * v = M * v - c * v := by exact Matrix.sub_mul M c v

theorem stupidLemma {i j : ℕ}
                    (v : Matrix (Fin i) (Fin 1) ℂ)
                    (c : ℂ):
                    c • v = c • (1 : Matrix (Fin i) (Fin i) ℂ) * v := by simp
                    
theorem lemmat {i : ℕ}
               (M : Matrix (Fin i) (Fin i) ℂ)
               (c : ℂ) : Polynomial.eval c M.charpoly = (M.charmatrix.map (λ x => Polynomial.eval c x)).det := by sorry


                
-/
-- determinant is formed from conjugation of vectors
/-
theorem quicktest {i : ℕ} 
                  (ne : i > 0)
                  (M : Matrix (Fin i) (Fin i) ℂ) : 
                  ∀ x ∈ M.charpoly.roots, (is_eigenvalue M x) := by 

                  intro c hrt
                  
                  rw[is_eigenvalue]
                  have tM := (M - (Matrix.scalar (Fin i) c))
                  have t2 : (M.charpoly.IsRoot c) := by 
                            exact Polynomial.isRoot_of_mem_roots hrt
                  
                  have t1 : (Polynomial.eval c M.charmatrix.det) = 0 := by 
                            exact t2
                


                  have zf : Fin i := ⟨0, ne⟩

                  have tV : (Matrix (Fin i) (Fin 1) ℂ) := 
                            (λ x : (Fin i) => (λ y : (Fin 1) =>  tM zf x))


                  have pr : M * tV = c • tV := by
                            rw[← sub_eq_zero]
                            rw[stupidLemma tV c]
                            rw[← temporary]
                            rw[hrt]
                           
-/

theorem detMulCharpolyRoot {i : ℕ}
                         (M : Matrix (Fin i) (Fin i) ℂ) : 
                         M.det = M.charpoly.roots.prod := by exact det_eq_prod_roots_charpoly M

def nonsingular {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                : 
                Prop 
                := ∀ v : (Fin i → ℂ), M.mulVec v = 0 → v = 0



def nullspace {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ) 
                      : 
                      Set ((Fin i) → ℂ) 
                      := 
                      {v : (Fin i) → ℂ | M.mulVec v = 0}


noncomputable def nullspaceSpan {i : ℕ}
                  (M : Matrix (Fin i) (Fin i) ℂ)
                  := (Submodule.span ℂ (nullspace M))

noncomputable def rowspace {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ) 
                           := (Submodule.span ℂ (Set.range M.row))
@[simp]
theorem nullspace_span_simp {i : ℕ}
                            (M : Matrix (Fin i) (Fin i) ℂ)
                            : 
                            nullspaceSpan M = (Submodule.span ℂ (nullspace M)) 
                            := by rfl
@[simp]
theorem nullspace_for_simp {i : ℕ}
                           (M : Matrix (Fin i) (Fin i) ℂ)
                           :
                           (nullspace M) = {v : (Fin i) → ℂ | M.mulVec v = 0} 
                           := by rfl

@[simp]
theorem crankEQrrank {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                             :
                             M.rank = M.transpose.rank 
                             := by 
                             have x := Matrix.rank_transpose M
                             simp
              
@[simp]
theorem ns_mul_zero {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                            :
                            ∀ v ∈ (nullspace M), M.mulVec v = 0 := by exact λ v a => a
             



variable (a b c : ℕ)
#check a * b

-- TODO

                      
-- Distributes a vector multiplication over a sum of a list.
@[simp]
theorem mulvec_distr {i : ℕ} 
              (L : List (Fin i → ℂ))
              (M : Matrix (Fin i) (Fin i) ℂ)
              :
              M.mulVec L.sum
              = (L.map M.mulVec).sum
              := by
              induction L with 
              | nil => simp_all
              | cons v L' => rw[List.sum_cons, mulVec_add]
                             simp_all        
                 
-- Allows distributing a vector multiply 
-- over a sum of vectors multiplied by a coefficient.
-- Useful when translating to a basis, for instance.
@[simp]
theorem finset_scalar_mul_ignore {i : ℕ}
        (f : (Fin i → ℂ) → ℂ)
        (V : Finset (Fin i → ℂ))
        :
        ∃ V₂ : List (Fin i → ℂ), 
        V₂.sum = ∑ v ∈ V, (f v) • v ∧ ∀ v ∈ V₂, ∃ v₁ ∈ V,  v = (f v₁) • v₁
        := by 
        let t (v : Fin i → ℂ) := f v • v
        have l2 : ∀ v ∈ V, f v • v = t v := by intro _ _; rfl
        let V₂ := V.toList.map t
        use V₂
        apply And.intro
        . exact Finset.sum_map_toList V t
        . intro v vm
          rcases List.mem_map.mp vm with ⟨vx, hvx, rfl⟩
          rw [← l2] at vm        
          rw [← l2]
          
          have p1 : vx ∈ V := by exact (Finset.mem_toList).mp hvx
          
          apply Exists.intro vx
          apply And.intro
          . exact p1
          . rfl
          exact Finset.mem_toList.mp hvx
          exact Finset.mem_toList.mp hvx
          -- Why do I need both???
          
        
        

@[simp]
theorem nsSpan_in_ns {i : ℕ}
                     (M : Matrix (Fin i) (Fin i) ℂ)
                     :
                     ∀ v ∈ nullspaceSpan M, v ∈ nullspace M := by
                     intro v
                     intro vm
                     have b := Basis.ofVectorSpace ℂ (nullspaceSpan M)
                     simp_all [Submodule.mem_span_iff_exists_finset_subset]
                     obtain ⟨ f, t, p1, p2, p3⟩ := vm
                     rw[← p3]
                     have T := finset_scalar_mul_ignore f t
                     obtain ⟨ V₂, pV₁, pV₂ ⟩ := T
                     rw[← pV₁]  
                     rw[mulvec_distr]
                     have hnull : ∀ x ∈ V₂, M.mulVec x = 0 := by
                                   intro x hx
                                   rcases pV₂ x hx with ⟨w, hw, rfl⟩
                                   simp [Matrix.mulVec_smul, p1 hw]
                     rw[List.sum_eq_zero]                         
                     simp_all    

-- The span of a nullspace is the same as the nullspace itself.                          
@[simp]
theorem nsSpan_eq_ns {i : ℕ}
                   (M : Matrix (Fin i) (Fin i) ℂ)
                   :
                   nullspaceSpan M = nullspace M 
                   := by 
                      simp_all
                      apply Set.ext
                      intro v
                      apply Iff.intro
                      . apply nsSpan_in_ns                         
                      . apply Submodule.subset_span

@[simp] 
theorem nss_mul_zero {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                             :
                             ∀ v ∈ (nullspaceSpan M), M.mulVec v = 0 := by 
                             intro v nssv
                             have : v ∈ (nullspace M) := by apply nsSpan_in_ns M v nssv
                             simp_all

-- 0 is in the nullspace.
@[simp]                 
theorem nullSpaceNotEmpty {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ) 
                          : 
                          ∃ v : (Fin i →  ℂ), v ∈ (nullspace M) 
                          := by 
                          constructor 
                          . rw[nullspace]
                            have x : M * 0 = 0 := by simp
                            have z : 0 ∈ nullspace M := by rw[nullspace]; simp;
                            exact z
--The nullspace of a nonsingular matrix is trivial.
@[simp]
theorem nonsingNullspaceTrivial {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                                      : nonsingular M ↔ nullspace M = {0} := by
                                      apply Iff.intro
                                      . intro nsm
                                        rw[nonsingular] at nsm
                                        rw[nullspace];
                                        rw [Set.eq_singleton_iff_unique_mem]
                                        simp_all
                                      . intro nst
                                        rw[nullspace] at nst
                                        rw[nonsingular]
                                        intro v mvz
                                        rw [Set.eq_singleton_iff_unique_mem] at nst
                                        have p1 := nst.right
                                        have p2 : v ∈ nullspace M := by exact mvz
                                        simp_all                 


def orthogComplement {i : ℕ} (Sv1 : Submodule ℂ (Fin i → ℂ))
                             (Sv2 : Submodule ℂ (Fin i → ℂ))
                             :
                             Prop
                             := (∀ v ∈ Sv1, ∀ u ∈ Sv2, dotProduct u v = 0 )
@[simp]
theorem orthog_complement_simp {i : ℕ} (Sv1 : Submodule ℂ (Fin i → ℂ))
                                       (Sv2 : Submodule ℂ (Fin i → ℂ))
                                       : orthogComplement Sv1 Sv2 = 
                                         (∀ v ∈ Sv1, ∀ u ∈ Sv2, dotProduct u v = 0 ) := by rfl
                                       
                                                                      
instance tsetismonoid : AddCommMonoid PUnit := inferInstance

noncomputable def rowspaceSpan {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ) 
                               := (Submodule.span ℂ (Set.range M.row))


@[simp]
theorem rs_for_simp {i : ℕ}
                    (M : Matrix (Fin i) (Fin i) ℂ)
                    :
                    rowspaceSpan M = Submodule.span ℂ (Set.range M.row) 
                    := by rfl

#check Matrix.row                  


@[simp]
theorem lincom_rowspaceSpan {i : ℕ} 
                                 (M : Matrix (Fin i) (Fin i) ℂ)
                                 (v : (Fin i) → ℂ)
                                 :
                                 v ∈ rowspaceSpan M → 
                                 ∃ f : Fin i → ℂ, v = ∑ k : (Fin i), f k • M.row k
                                 := by 
                                 rw [rowspaceSpan]
                                 rw [Submodule.mem_span_range_iff_exists_fun]
                                 intro c
                                 rcases c with ⟨ cf, cprop ⟩
                                 refine Exists.intro cf (by rw[cprop])

                                    
@[simp]
theorem mulvec_is_dp_rows {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                                  (v : Fin i → ℂ)
                                  :
                                  M.mulVec v = 
                                  (λ x : (Fin i) => dotProduct (M.row x) v) 
                                  := by rfl

theorem lemma_1 {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                        (v : Fin i → ℂ)
                        :
                        ∀ v1 ∈ rowspaceSpan M, dotProduct v1 v ∈ Submodule.span ℂ (Set.range (M.mulVec v)) 
                        := by 
                           intro v1 rspv1 sp spset
                           have p := lincom_rowspaceSpan M v1 rspv1
                           rw [mulvec_is_dp_rows] at spset
                           rcases p with ⟨ pf, pp ⟩
                           rw[pp]
                           apply Set.mem_preimage.mp
                           sorry
                           
@[simp]
theorem setTest {α : Type*} (s : Set α) {a : α} : a ∈ s → s ∩ {a} = {a} := by simp


                     

@[simp]
theorem rs_orthog_ns {i : ℕ} (p : i > 0) (M : Matrix (Fin i) (Fin i) ℂ)
                     :
                     orthogComplement  (nullspaceSpan M) (rowspaceSpan M)
                     := by  
                     intro nsV nspP rowspV rowspVP 
                     have p1 : M.mulVec nsV = 0 := by simp_all
                                                      
                     
                     have p2 : Ideal.span (Set.range (M.mulVec nsV)) = 0
                             := by simp_all                    
                                   rw[Set.range, Ideal.span_eq_bot]
                                   simp
                     have dpz : dotProduct rowspV nsV = 0
                              := by
                                 have pt1 := lincom_rowspaceSpan M rowspV rowspVP
                                 rcases pt1 with  ⟨ pf, pp ⟩
                                 rw[mulvec_is_dp_rows] at p1
                                 have t : ∀ k : Fin i, dotProduct (M.row k) nsV = 0 
                                        := by intro k
                                              rw [funext_iff] at p1
                                              apply p1
                                 have ct : ∀ c : ℂ, ∀ k : Fin i, 
                                          (c • M.row k) ⬝ᵥ nsV = 0 
                                          := by simp_all
                                 have sumf : ∀ c1 c2 : ℂ, ∀ k1 k2: Fin i,
                                            ((c1 • M.row k1) + (c2 • M.row k2)) ⬝ᵥ nsV = 0                                          
                                           := by simp_all
                                 rw[pp]
                                 simp_all
                                 
                     simp_all




         
@[simp]
theorem trivialRank {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                            :
                            (nonsingular M) → (nullspaceSpan M).spanRank = 0 
                            := by simp_all

@[simp]
theorem dotProduct_distr {i : ℕ} 
                         (v : (Fin i → ℂ))
                         (V : List (Fin i → ℂ))
                         :
                         dotProduct v V.sum = (V.map (dotProduct v)).sum := by
                         induction V with
                         | nil => simp_all
                         | cons v₂ L ih=> rw [List.sum_cons]
                                          rw[dotProduct_add]
                                          simp_all
                                          
                                        
                                 



-- TODO
theorem rs_ns_complement {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                         :
                         M ≠ 0 → IsCompl (nullspaceSpan M) (rowspaceSpan M) := by 
                         rw[isCompl_iff]
                         intro nz
                         apply And.intro
                         . rw [Submodule.disjoint_def]
                           intro v nsv rsv
                           have p1 : M *ᵥ v = 0 := by simp_all
                           simp_all
                           have p2 : ∃ f : (Fin i → ℂ), 
                                     v = ∑ j : Fin i, f j • M.row j := by simp_all
                           have p3 : ∀ j : Fin i, (M.row j) ⬝ᵥ v = 0 := by
                                   intro j
                                   obtain ⟨f, pf⟩ := p2
                                   rw[pf]
                                   have : ∀ k : Fin i, 
                                        M.row k ⬝ᵥ ∑ j : Fin i, f j • M.row j = 
                                        ∑ j : Fin i, M.row k ⬝ᵥ f j • M.row j 
                                        := by intro k
                                              rw[← Finset.sum_map_toList]
                                              rw[dotProduct_distr]
                                              simp_all
                                   simp_all
                                        
                                        
                         . sorry

theorem nonsing_imp_lnindp {i : ℕ}
                           (M : Matrix (Fin i) (Fin i) ℂ)
                           :
                           (nonsingular M) → LinearIndependent ℂ M.row := by
                           contrapose
                           intro nld
                           have fs : Finset (Fin i) := Finset.univ
                           have si := fs.toSet
                           rw[Matrix.row] at nld
                           have p2 : ∃ (s : Finset (Fin i)) (g : Fin i → ℂ),
                                     ∑ i ∈ s, g i • M.row i = 0 
                                     ∧ ∃ i ∈ s, g i ≠ 0 := by 
                                     refine not_linearIndependent_iff.mp nld
                           obtain ⟨set, v, prop⟩ := p2
                           rw[nonsingular]
                           simp[not_forall];
                           simp_all
                           rw[AddMonCat.zero_of]
                           apply Exists.intro v
                           apply And.intro
                           . rw[← mulvec_is_dp_rows]
                             rw[mulVec]
                           . 
                           
                           
                           
                           
                           
/-
theorem rank {i : ℕ} (M : Matrix (Fin i) (Fin i) ℂ)
                     :
                     (Submodule.spanFinrank (rowspaceSpan M)) 
                     + (Submodule.spanFinrank (nullspaceSpan M)) = i := by 
                     have hrn : HasRankNullity ℂ := by exact DivisionRing.hasRankNullity
                     apply LinearAlgebra
-/




/-
noncomputable def dotProductSpecific (α : Type*) [Fintype α]
                                     (v₁ : α → ℂ)
                                     (v₂ : α → ℂ) := dotProduct v₁ v₂
                       
@[simp]
theorem dps_is_dp (α : Type*) [Fintype α] : dotProductSpecific α = dotProduct := rfl

noncomputable def dotProductBilinear (α : Type*) [Fintype α]
                                     : 
                                     (α → ℂ) →ₗ[ℂ] (α → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (dotProductSpecific α)
    (by
      intro v w u
      simp only [dps_is_dp]
      simp_all)
    (by
      intro v w u
      simp only [dps_is_dp]
      simp_all)
    (by
      intro a v w
      simp only [dps_is_dp]
      simp_all)
    (by
      intro a v w
      simp only [dps_is_dp]
      simp_all)

#check RingHom.map_dotProduct
#check LinearMap.BilinMap ℂ (Fin i → ℂ) (Fin i → ℂ)

#check LinearMap (RingHom.id ℂ)

theorem mathlibLemma {i : ℕ} (p : i > 0)
                             (M : Matrix (Fin i) (Fin i) ℂ)
                             :
                             Submodule.orthogonalBilin (nullspaceSpan M) (I₁ := RingHom.id ℂ) (I₂ := RingHom.id ℂ) (M := ℂ) (dotProductBilinear (Fin i)) = (rowspaceSpan M)
                             := by 
                                rw[Submodule.orthogonalBilin]
                                sorry
-/                                   
@[simp] 
theorem testnn {i : ℕ} (p : i > 0)
                       (M : Matrix (Fin i) (Fin i) ℂ)
                       :
                       (Module.finrank ℂ (Fin i → ℂ)) = (rowspaceSpan M).spanRank + (nullspaceSpan M).spanRank
                       := by
                          simp_all
                          sorry
                          
                          


theorem NSTiffRolLinInd {i : ℕ} 
                        (M : Matrix (Fin i) (Fin i) ℂ)
                        :
                        (nonsingular M) → LinearIndependent ℂ M.row
                        := by        
                           intro nsM
                           have rs := rowspaceSpan M
                           have ns := nullspace M
                           have nsTP := nonsingNullspaceTrivial M
                           have nsT : nullspace M = {0} := by simp_all
                           rw[LinearIndependent]
                           sorry


theorem nonsingImpdnz {i : ℕ} 
                      (M : Matrix (Fin i) (Fin i) ℂ)
                      : nonsingular M → M.det ≠ 0 := by
                      contrapose
                      intro x y
                      rw[nonsingular] at y
                      simp at x
                      rw[det_apply] at x
                      
                      sorry

theorem nonsingIFFinverse 
        (M : Matrix (Fin i) (Fin i) ℂ)
        (hvns : nonsingular M) 
        : ∃ (N : Matrix (Fin i) (Fin i) ℂ), M * N = 1 := by
            rw[nonsingular] at hvns
            sorry
            

