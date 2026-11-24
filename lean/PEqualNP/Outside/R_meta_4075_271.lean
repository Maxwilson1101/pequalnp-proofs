import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4075_271
    (transfer : ∀ (n : ℕ) (C : Circuit) (i j : ℕ), FanInTwo C → n ≤ i → i < j → j < n+C.size →
      let good := fun (g : Gate) => (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2;
      ∃ (K : Circuit) (U V : Gate), FanInTwo K ∧ K.size+2≤C.size ∧ good U ∧ good V ∧
        ∀ x : List Bool,x.length=n → let z := C.wires x; let r := fun (b : Bool) (g : Gate) => g.op.eval (g.inputs.map fun k => (K.wires (b::x)).getD k false);
          (∀ b, r b U=z.getD i false) ∧ r (z.getD i false) V=z.getD j false)
    (remaining : ∀ (d : Bool) (K : Circuit) (U V : Gate), FanInTwo K → K.size≤15 →
      let good := fun (g : Gate) => (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2; good U → good V →
      let edge := fun (x : Fin 10 → Bool) => ∃ i : Fin 5,
        (x (Fin.castAdd 5 i)=true ∧ (x (Fin.castAdd 5 (i+1))=true ∨ x (Fin.natAdd 5 i)=true)) ∨ (x (Fin.natAdd 5 i)=true ∧ x (Fin.natAdd 5 (i+2))=true);
      let r := fun (x : Fin 10 → Bool) (b : Bool) (g : Gate) => let xs := b :: (List.ofFn x ++ [x 0 && (if d then x 1 else x 2)]);
        g.op.eval (g.inputs.map fun k => (K.wires xs).getD k false);
      (∀ x, r x true U=r x false U) → (∃ x,r x true U=true ∧ r x true V=false) →
      (∃ x,r x false U=false ∧ r x false V=true) → (∀ x,edge x → r x true U=true ∧ r x true V=true) →
      ∃ x,¬edge x ∧ r x true U=true ∧ r x true V=true) :
    ∀ (x1 : Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (17 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ));       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8 ++ [x8 (0 : Fin (10 : ℕ)) && if x1 = Bool.true then x8 (1 : Fin (10 : ℕ)) else x8 (2 : Fin (10 : ℕ))])).getD x9 Bool.false;       (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 x3 = Bool.true ∧ x8 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 x3 = Bool.false ∧ x8 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x7 x11 = Bool.true → x8 x11 x3 = Bool.true ∧ x8 x11 x4 = Bool.true) → ∃ (x12 : Fin (10 : ℕ) → Bool), x7 x12 = Bool.false ∧ x8 x12 x3 = Bool.true ∧ x8 x12 x4 = Bool.true := by
  intro d C i j fan size F W one two hot
  let inp := fun (x : Fin 10 → Bool) => List.ofFn x ++ [x 0 && (if d then x 1 else x 2)]
  let edge := fun (x : Fin 10 → Bool) => ∃ k : Fin 5,
    (x (Fin.castAdd 5 k)=true ∧ (x (Fin.castAdd 5 (k+1))=true ∨ x (Fin.natAdd 5 k)=true)) ∨ (x (Fin.natAdd 5 k)=true ∧ x (Fin.natAdd 5 (k+2))=true)
  have coincide : ∀ x,F x=true ↔ edge x := by dsimp only [F,edge]; decide +kernel
  have len (x) : (inp x).length=11 := by simp [inp]
  have pref (x) : ∃ t,C.wires (inp x)=inp x++t ∧ t.length=C.size := by
    have aux (gs : List Gate) (w : List Bool) : ∃ t,gs.foldl (fun z g => z++[g.op.eval (g.inputs.map fun k=>z.getD k false)]) w=w++t ∧ t.length=gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[],by simp,rfl⟩
      | cons g gs ih => obtain ⟨t,eq,n⟩ := ih (w++[g.op.eval (g.inputs.map fun k=>w.getD k false)]); exact ⟨_::t,by simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using eq,by simp [n]⟩
    exact aux C.gates (inp x)
  let sample := fun (b : Bool) (t : Fin 10) => if b then decide (t=3 ∨ t=4) else decide (t=7 ∨ t=9)
  have raw : ∀ k : Fin 11,∃ b : Bool,F (sample b)=true ∧ (inp (sample b)).getD k.val false=false := by
    cases d <;> dsimp only [F,inp,sample] <;> decide +kernel
  have gateRange (k : ℕ) (yes : ∀ x,F x=true → W x k=true) : 11 ≤ k ∧ k<11+C.size := by
    constructor
    · by_contra! small; obtain ⟨b,on,off⟩ := raw ⟨k,small⟩; obtain ⟨t,eq,_⟩ := pref (sample b); have hit := yes _ on; change (C.wires (inp (sample b))).getD k false=true at hit
      rw [eq,List.getD_append _ _ _ _ (by rw [len];exact small),off] at hit; contradiction
    · by_contra! big; obtain ⟨b,on,_⟩ := raw 0; obtain ⟨t,eq,sz⟩ := pref (sample b); have hit := yes _ on; change (C.wires (inp (sample b))).getD k false=true at hit
      rw [List.getD_eq_default _ _ (by simp [eq,sz,len];omega)] at hit; contradiction
  have ordered (a b : ℕ) (ab : a<b) (h1 : ∃ x,W x a=true ∧ W x b=false) (h2 : ∃ x,W x a=false ∧ W x b=true) (acc : ∀ x,F x=true → W x a=true ∧ W x b=true) : ∃ x,F x=false ∧ W x a=true ∧ W x b=true := by
    have ha := gateRange a (fun x h=>(acc x h).1); have hb := gateRange b (fun x h=>(acc x h).2)
    obtain ⟨K,U,V,ok,cap,gu,gv,run⟩ := transfer 11 C a b fan ha.1 ab hb.2
    let r := fun (x : Fin 10 → Bool) (s : Bool) (g : Gate) => g.op.eval (g.inputs.map fun k=>(K.wires (s::inp x)).getD k false)
    have u (x) (s) : r x s U=W x a := (run (inp x) (len x)).1 s
    have v (x) : r x (W x a) V=W x b := (run (inp x) (len x)).2
    have cc : ∀ x,r x true U=r x false U := fun x=>(u x true).trans (u x false).symm
    have ex1 : ∃ x,r x true U=true ∧ r x true V=false := by obtain ⟨x,y,z⟩:=h1; exact ⟨x,(u x true).trans y,by simpa only [y] using (v x).trans z⟩
    have ex2 : ∃ x,r x false U=false ∧ r x false V=true := by obtain ⟨x,y,z⟩:=h2; exact ⟨x,(u x false).trans y,by simpa only [y] using (v x).trans z⟩
    have pos (x) (e : edge x) : r x true U=true ∧ r x true V=true := by obtain ⟨y,z⟩:=acc x ((coincide x).mpr e); exact ⟨(u x true).trans y,by simpa only [y] using (v x).trans z⟩
    obtain ⟨x,non,hi,hj⟩ := remaining d K U V ok (by omega) gu gv cc ex1 ex2 pos
    have y : W x a=true := (u x true).symm.trans hi
    exact ⟨x,Bool.eq_false_iff.mpr (fun on=>non ((coincide x).mp on)),y,(v x).symm.trans (by simpa only [y] using hj)⟩
  rcases lt_trichotomy i j with lt|eq|gt
  · exact ordered i j lt one two hot
  · subst j; obtain ⟨x,a,b⟩ := one; simp [a] at b
  · obtain ⟨x,no,b,a⟩ := ordered j i gt (by simpa only [and_comm] using two) (by simpa only [and_comm] using one) (fun x on=>(hot x on).symm); exact ⟨x,no,a,b⟩
