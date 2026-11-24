import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Compile away uncounted AND gates, then test the canonical OR instructions on the 52 flags. -/
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_4949_271
    (compile :
let R:=Fin 26→Bool;let I:=Fin 52;let B:=List (Set R)
  ∀ (p : I→R) (C : Circuit),(∀ i,∃ a b : Fin 26,∀ k,p i k=true → k=a ∨ k=b) → Monotone2 C → (∀ i,C.eval (List.ofFn (p i))=true) →
  let H : B→Set I→Set R:=fun b s => {x | ∀ f∈b,(∀ i∈s,p i∈f) → x∈f}
  let a : B:=∅::List.ofFn (fun i : Fin 26 => {x : R|x i=true})
  ∃ s : List (Set I × Set I),s.length={j : Fin C.gates.length | (C.gates.get j).op=.or}.ncard ∧ (∀ t∈s,∀ i∈t.1,i∉t.2) ∧
    (∀ j : Fin s.length, (s.get j).1.ncard ≤ j.val+3 ∧ (s.get j).2.ncard ≤ j.val+3) ∧
    ∀ x : R,C.eval (List.ofFn x)=false → ∃ f∈s.foldl (fun b t => (H b t.1 ∪ H b t.2)::b) a,(∀ i,p i∈f) ∧ x∉f)
    (collision :
let R:=Fin 26→Bool;let I:=Fin 52;let B:=List (Set R)
  let p:=fun (i : I) (w : Fin 26) => decide (w.val=13+i.val/4 ∨ w.val=(i.val/4+[0,1,3,9].getD (i.val%4) 0)%13)
  let H : B→Set I→Set R:=fun b s => {x | ∀ f∈b,(∀ i∈s,p i∈f) → x∈f}
  let a : B:=∅::List.ofFn (fun i : Fin 26 => {x : R|x i=true})
  ∀ s : List (Set I × Set I),s.length≤50 → (∀ t∈s,∀ i∈t.1,i∉t.2) →
    (∀ j : Fin s.length,(s.get j).1.ncard ≤ j.val+3 ∧ (s.get j).2.ncard ≤ j.val+3) →
    ∃ j : Fin 36, ∃ k : Fin 13,
    let m:=((1259886254397126488781191988044141515605159741757169136265957107063160921435871760439256437543488169396155399 : ℕ) >>> (10*j.val))%1024
    let v:=fun t : Fin 13 => m.testBit (t-k).val
    let x : R:=fun w => Fin.addCases (m:=13) (n:=13) (motive:=fun _ => Bool) v (fun l => !(v l || v (l+1) || v (l+3) || v (l+9))) w
    ∀ f∈s.foldl (fun b t => (H b t.1 ∪ H b t.2)::b) a,(∀ i,p i∈f) → x∈f) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) →       (∀ (x4 : ℕ) (x5 : Fin (13 : ℕ)),           (x4 ∈               have x6 : List ℕ :=                 have x6 : List ℕ :=                   have x6 : List ℕ := [(281 : ℕ), (297 : ℕ), (329 : ℕ), (337 : ℕ), (549 : ℕ)];                   (201 : ℕ) :: (265 : ℕ) :: (273 : ℕ) :: (275 : ℕ) :: x6;                 have x7 : List ℕ := (133 : ℕ) :: (135 : ℕ) :: (137 : ℕ) :: (141 : ℕ) :: (195 : ℕ) :: x6;                 (97 : ℕ) :: (101 : ℕ) :: (105 : ℕ) :: (131 : ℕ) :: x7;               have x7 : List ℕ :=                 have x7 : List ℕ := (73 : ℕ) :: (77 : ℕ) :: (81 : ℕ) :: (83 : ℕ) :: (85 : ℕ) :: x6;                 (41 : ℕ) :: (67 : ℕ) :: (69 : ℕ) :: (71 : ℕ) :: x7;               have x8 : List ℕ := (25 : ℕ) :: (29 : ℕ) :: (35 : ℕ) :: (37 : ℕ) :: (39 : ℕ) :: x7;               (7 : ℕ) :: (13 : ℕ) :: (19 : ℕ) :: (21 : ℕ) :: x8) →             have x7 : Finset (Fin (13 : ℕ)) := {x7 : Fin (13 : ℕ) | x4.testBit ↑(x7 - x5) = Bool.true};             (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ ∀ x10 ∈ x7, ¬(x10 = x9 ∨ x10 = x9 + (1 : Fin (13 : ℕ)) ∨ x10 = x9 + (3 : Fin (13 : ℕ)) ∨ x10 = x9 + (9 : Fin (13 : ℕ))))) = Bool.false) →         (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C mono hp hn
  let pos:=fun (i : Fin 52) (w : Fin 26) => decide (w.val=13+i.val/4 ∨ w.val=(i.val/4+[0,1,3,9].getD (i.val%4) 0)%13)
  let inc:=fun (p l : Fin 13) => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  let flag:=fun (p l : Fin 13) (w : Fin 26) => decide (w=Fin.castAdd 13 p ∨ w=Fin.natAdd 13 l)
  let lidx:=fun (i : Fin 52) => Fin.ofNat 13 (i.val/4)
  let pidx:=fun (i : Fin 52) => Fin.ofNat 13 (i.val/4+[0,1,3,9].getD (i.val%4) 0)
  have rows : ∀ i,inc (pidx i) (lidx i) ∧ ∀ w,pos i w=flag (pidx i) (lidx i) w := by decide +kernel
  have flags : ∀ i,∃ p l,inc p l ∧ ∀ w,pos i w=flag p l w := fun i => ⟨_,_,rows i⟩
  have accept (i : Fin 52) : C.eval (List.ofFn (pos i))=true := by
    obtain ⟨p,l,on,e⟩:=flags i;rw [funext e];exact hp p l on
  have sparse : ∀ i,∃ a b : Fin 26,∀ w,pos i w=true → w=a ∨ w=b := by
    intro i;obtain ⟨p,l,_,e⟩:=flags i;refine ⟨Fin.castAdd 13 p,Fin.natAdd 13 l,?_⟩
    intro w;rw [e w];exact decide_eq_true_eq.mp
  obtain ⟨s,count,disjoint,width,cover⟩:=compile pos C sparse mono accept
  by_contra! small
  obtain ⟨j,k,live⟩:=collision s (by omega) disjoint width
  -- Consecutive ten-bit slots store the desk's point masks in their printed order.
  let mask:=fun (i : Fin 36) => ((1259886254397126488781191988044141515605159741757169136265957107063160921435871760439256437543488169396155399 : ℕ) >>> (10*i.val))%1024
  let m:=mask j
  have masks : ∀ i : Fin 36,mask i ∈ ([7,13,19,21,25,29,35,37,39,41,67,69,71,73,77,81,83,85,97,101,105,131,133,135,137,141,195,201,265,273,275,281,297,329,337,549] : List Nat) := by decide +kernel
  have hm:=masks j
  let v:=fun t : Fin 13 => m.testBit (t-k).val
  let x : Fin 26→Bool:=fun w => Fin.addCases (m:=13) (n:=13) (motive:=fun _ => Bool) v (fun l => !(v l || v (l+1) || v (l+3) || v (l+9))) w
  let P:=Finset.univ.filter (fun t : Fin 13 => v t)
  let row:=fun w : Fin 26 => decide ((∃ p∈P,w=Fin.castAdd 13 p) ∨ ∃ l : Fin 13,w=Fin.natAdd 13 l ∧ ∀ p∈P,¬inc p l)
  have pp : ∀ a b : Fin 13, Fin.castAdd 13 a=Fin.castAdd 13 b ↔ a=b := by decide +kernel
  have ll : ∀ a b : Fin 13, Fin.natAdd 13 a=Fin.natAdd 13 b ↔ a=b := by decide +kernel
  have pl : ∀ a b : Fin 13, Fin.castAdd 13 a≠Fin.natAdd 13 b := by decide +kernel
  have eq : x=row := by
    funext w;refine Fin.addCases (m:=13) (n:=13) (fun p => ?_) (fun l => ?_) w
    · dsimp only [x];rw [Fin.addCases_left];apply Bool.eq_iff_iff.mpr
      simp only [row,P,decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and,pp,pl]
      constructor
      · intro h;exact Or.inl ⟨p,h,rfl⟩
      · rintro (⟨q,h,rfl⟩|⟨l,e,_⟩);exact h;exact e.elim
    · dsimp only [x];rw [Fin.addCases_right];apply Bool.eq_iff_iff.mpr
      simp only [row,P,decide_eq_true_eq,Finset.mem_filter,Finset.mem_univ,true_and,ll,fun a b => Ne.symm (pl a b)]
      have test : ∀ (a : Fin 13→Bool) (t : Fin 13), (!(a t || a (t+1) || a (t+3) || a (t+9)))=true ↔ ∀ p,a p=true → ¬inc p t := by
        intro a t;simp only [Bool.not_eq_true',Bool.or_eq_false_iff,inc]
        constructor
        · rintro ⟨⟨⟨h,i⟩,j⟩,k⟩ p eq (rfl|rfl|rfl|rfl)
          · exact Bool.noConfusion (eq.symm.trans h)
          · exact Bool.noConfusion (eq.symm.trans i)
          · exact Bool.noConfusion (eq.symm.trans j)
          · exact Bool.noConfusion (eq.symm.trans k)
        · intro h;repeat' apply And.intro
          all_goals apply Bool.eq_false_iff.mpr;intro e;apply h _ e
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
      rw [test];constructor
      · intro h;exact Or.inr ⟨l,rfl,h⟩
      · rintro (⟨p,_,e⟩|⟨l',rfl,h⟩);exact e.elim;exact h
  have rejected : C.eval (List.ofFn x)=false := by rw [eq];exact hn m k hm
  obtain ⟨f,mem,full,absent⟩:=cover x rejected
  exact absent (live f mem full)
