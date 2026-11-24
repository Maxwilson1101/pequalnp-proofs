import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
  PEqualNP.EdgeOwnership PEqualNP.PairShadow Finset

theorem PEqualNP.Outside.R_meta_4598_271
    (frontier : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p t, p ≠ t → ∃! l, I p l ∧ I t l) → IsAO2 (N+N) C →
      let v := gateVal (N+N) C
      let A := fun j : Fin C.size => univ.filter fun p => v j (unitInput (Fin.castAdd N p)) = true
      let D := fun (j : Fin C.size) (l : Fin N) => v j (Fin.addCases (fun p => decide (¬ I p l)) (fun t => decide (t=l))) = false
      ∀ B : Finset (Fin N × Fin N), (∀ e ∈ B, ∃ j, e.1 ∈ A j ∧ 1 < (A j).card ∧ D j e.2) →
        B.card ≤ 2 * Fintype.card {j // 1 < (A j).card ∧ ∃ l, D j l})
    (privateFlags : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
      (E : Finset (Fin N × Fin N)), 87 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p // I p l} = q+1) → (∀ p t, p ≠ t → ∃! l, I p l ∧ I t l) → IsAO2 (N+N) C →
      let L : Fin N → Fin (N+N) := Fin.castAdd N
      let R : Fin N → Fin (N+N) := Fin.natAdd N
      let f := circuitFun (N+N) C
      (∀ z, Fintype.card {l // z (R l) = true} ≤ q → (¬ ∃ p l, I p l ∧ z (L p) = true ∧ z (R l) = true) → f z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧ f (pairInput (L e.1) (R e.2)) = true ∧
        ¬ IsSingleRead C (N+N) (fun i => decide (N ≤ i)) [(e.1.val,N+e.2.val)]) →
      4400 < C.size → let v := gateVal (N+N) C
      let A := fun j : Fin C.size => univ.filter fun p => v j (unitInput (L p)) = true
      let D := fun (j : Fin C.size) (l : Fin N) => v j (Fin.addCases (fun p => decide (¬ I p l)) (fun t => decide (t=l))) = false
      (∀ e ∈ E, ∀ j, e.1 ∈ A j → D j e.2 → (A j).card ≤ 1) →
        E.card + 2 * Fintype.card {j // 1 < (A j).card ∧ ∃ l, D j l} ≤ 24*C.size) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p t, p ≠ t → ∃! l, I p l ∧ I t l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → circuitFun (N+N) C z = false) →
      let hits := fun (i : Fin (N+N)) (e : Fin N × Fin N) => i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun i => decide (hits i e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1 (N+e.2) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1 (N+e.2) = false) →
      (∀ e ∈ E, ∀ i, hits i e → 24 < (E.filter (hits i)).card) → 4400 < C.size → E.card ≤ 24*C.size := by
  intro q N I inst C E hq hn col uniq ao sound hits accept dense large
  let v := gateVal (N+N) C
  let A := fun j : Fin C.size => univ.filter fun p => v j (unitInput (Fin.castAdd N p)) = true
  let D := fun (j : Fin C.size) (l : Fin N) => v j (Fin.addCases (fun p => decide (¬ I p l)) (fun t => decide (t=l))) = false
  let B := E.filter fun e => ∃ j, e.1 ∈ A j ∧ 1 < (A j).card ∧ D j e.2
  have cheap := frontier N I C uniq ao B (fun _ h => (mem_filter.mp h).2)
  have left := privateFlags q N I C (E\B) hq hn col uniq ao sound (by
    intro e he; obtain ⟨adj,hot,x,y⟩ := accept e (mem_sdiff.mp he).1
    refine ⟨adj,hot,?_⟩
    have h : (fun i : ℕ => !(decide (N ≤ i))) = (fun i : ℕ => decide (i < N)) := by
      funext i; by_cases hi : N ≤ i
      · simp [hi,Nat.not_lt_of_ge hi]
      · simp [hi,Nat.lt_of_not_ge hi]
    delta IsSingleRead doubleReread; simp [x,y,h]) large (by
    intro e he j hp hd; by_contra! big; exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨(mem_sdiff.mp he).1,j,hp,big,hd⟩))
  have count := card_sdiff_add_card_eq_card (show B ⊆ E from filter_subset _ _)
  omega
