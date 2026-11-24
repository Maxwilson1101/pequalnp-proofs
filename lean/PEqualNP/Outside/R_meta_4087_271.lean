import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4087_271
    (geometry : let D : Finset (Fin 13) := {0,1,3,9}; ∀ (P L : Finset (Fin 13)),
      (∀ p∈P,∀ l∈L,p-l∉D) → (∀ i, (P.filter fun p=>p-i∈D).card≤2) → (∀ i, (L.filter fun l=>i-l∈D).card≤2) →
      ∃ A B : Finset (Fin 13), P⊆A ∧ L⊆B ∧ A.card+B.card=7 ∧ 3≤min A.card B.card ∧ ∀ p∈A,∀ l∈B,p-l∉D)
    (search : let I := Fin 13; let S := Finset I; let idx := Fin.ofNat 13; let D : S := {0,1,3,9};
      let row := fun (P L : S) (b : Bool) => List.ofFn fun k : Fin 70 =>
        let n := k.val; if n<13 then decide (idx n∈P) else if n<26 then decide (idx n∈L) else
        let h := (n-25)/5; let i := idx h; let j := n-(26+(5*h-1));
        let u := decide (i∈P ∨ i+1∈P); let v := decide (i+3∈P ∨ i+9∈P);
        if j=0 then u else if j=1 then v else if j=2 then u || v else b;
      ∃ C : Circuit, Monotone2 C ∧ C.size≤18 ∧ (∀ p l : I, 9≤l.val → p-l∈D → C.eval (row {p} {l} false)=true) ∧
        ∀ A B : S, A.card+B.card=7 → 3≤min A.card B.card → (∀ p∈A,∀ l∈B,p-l∉D) → C.eval (row A B true)=false) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool → Prop := fun (x2 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : List Bool) =>   x5.length = (70 : ℕ) ∧     (∀ (x6 : Fin (13 : ℕ)), x5.getD (↑x6) Bool.false = Decidable.decide (x6 ∈ x3) ∧ x5.getD ((13 : ℕ) + ↑x6) Bool.false = Decidable.decide (x6 ∈ x4)) ∧       ∀ (x6 : Fin (9 : ℕ)),         have x7 : Fin (13 : ℕ) := (x2 x6).2.1;         have x8 : Fin (13 : ℕ) := if (x2 x6).2.2 = (0 : Fin (3 : ℕ)) then (1 : Fin (13 : ℕ)) else if (x2 x6).2.2 = (1 : Fin (3 : ℕ)) then (3 : Fin (13 : ℕ)) else (9 : Fin (13 : ℕ));         let x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => if (x2 x6).1 = Bool.true then x7 + x9 ∈ x3 else x7 - x9 ∈ x4;         have x10 : ℕ := (26 : ℕ) + ((5 : ℕ) * ↑x6 - (1 : ℕ));         x5.getD x10 Bool.false = Decidable.decide (x9 (0 : Fin (13 : ℕ)) ∨ x9 x8) ∧ x5.getD (x10 + (1 : ℕ)) Bool.false = Decidable.decide (x9 ((3 : Fin (13 : ℕ)) * x8) ∨ x9 ((9 : Fin (13 : ℕ)) * x8)) ∧ x5.getD (x10 + (2 : ℕ)) Bool.false = (x5.getD x10 Bool.false || x5.getD (x10 + (1 : ℕ)) Bool.false); ∃ (x3 : Fin (9 : ℕ) → Bool × Fin (13 : ℕ) × Fin (3 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (18 : ℕ) ∧ ∀ (x5 x6 : Finset (Fin (13 : ℕ))) (x7 : List Bool), x2 x3 x5 x6 x7 → ((∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x5 = {x9} ∧ x6 = {x10} ∧ x9 - x10 ∈ x1 ∧ ¬∃ (x11 : Fin (9 : ℕ)), if (x3 x11).1 = Bool.true then (x3 x11).2.1 = x10 else (x3 x11).2.1 = x9) → x4.eval x7 = Bool.true) ∧ ((∀ x9 ∈ x5, ∀ x11 ∈ x6, x9 - x11 ∉ x1) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x5 | x11 - x10 ∈ x1}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x6 | x11 - x12 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval x7 = Bool.false) := by
  let start (i : Nat) := 26+(5*i-1)
  let idx (n : Nat) := Fin.ofNat 13 n
  let left (P : (Finset (Fin 13))) (n : Nat) := let i := idx n; decide (i∈P ∨ i+1∈P)
  let right (P : (Finset (Fin 13))) (n : Nat) := let i := idx n; decide (i+3∈P ∨ i+9∈P)
  let slot (P : (Finset (Fin 13))) (b : Bool) (i t : Nat) := if t=0 then left P i else if t=1 then right P i else if t=2 then left P i || right P i else b
  let value (P L : (Finset (Fin 13))) (b : Bool) (k : Nat) := if k<13 then decide (idx k∈P) else if k<26 then decide (idx k∈L) else let i := (k-25)/5; slot P b i (k-start i)
  let row (P L : (Finset (Fin 13))) (b : Bool) := List.ofFn fun k : Fin 70 => value P L b k.val
  let read (w : List Bool) (P L : (Finset (Fin 13))) := (∀ p : (Fin 13), w.getD p.val false=decide (p∈P) ∧ w.getD (13+p.val) false=decide (p∈L)) ∧ ∀ i : Fin 9, let j:=start i.val; w.getD j false=left P i.val ∧ w.getD (j+1) false=right P i.val ∧ w.getD (j+2) false=(w.getD j false || w.getD (j+1) false)
  have sandwich (P L A B : (Finset (Fin 13))) (hp : P⊆A) (hl : L⊆B) (w : List Bool) (r : read w P L) (k : Fin 70) :
      ((row P L false).getD k.val false=true → w.getD k.val false=true) ∧ (w.getD k.val false=true → (row A B true).getD k.val false=true) := by
    simp only [row,List.getD_eq_getElem _ _ (show k.val < (List.ofFn fun j : Fin 70 => value P L false j.val).length by simp),List.getD_eq_getElem _ _ (show k.val < (List.ofFn fun j : Fin 70 => value A B true j.val).length by simp),List.getElem_ofFn]
    let n := k.val
    by_cases s : n<13
    · let p : (Fin 13) := ⟨n,s⟩
      have e : idx n=p := Fin.ext (Nat.mod_eq_of_lt s)
      have h := (r.1 p).1
      change (value P L false n=true → w.getD n false=true) ∧ (w.getD n false=true → value A B true n=true)
      change w.getD n false=_ at h
      simp only [value,ite_eq_left s,e,h,decide_eq_true_eq,imp_self,true_and]; exact @hp p
    by_cases t : n<26
    · let l : (Fin 13) := ⟨n-13,by omega⟩; have u : 13+l.val=k.val := by change 13+(n-13)=n; omega
      have e : idx n=l := Fin.ext (by change n%13=n-13; omega)
      have h := (r.1 l).2
      rw [u] at h
      change (value P L false n=true → w.getD n false=true) ∧ (w.getD n false=true → value A B true n=true)
      change w.getD n false=_ at h
      simp only [value,ite_eq_right s,ite_eq_left t,e,h,decide_eq_true_eq,imp_self,true_and]; exact @hl l
    let i := (n-25)/5; have hi : i<9 := by have := k.isLt; dsimp [n,i] at *; omega
    let j := start i; have up : j≤n := by dsimp [j,start,i]; omega
    have h := r.2 ⟨i,hi⟩; change w.getD j false=left P i ∧ w.getD (j+1) false=right P i ∧ w.getD (j+2) false=(w.getD j false || w.getD (j+1) false) at h
    have u : left P i=true → left A i=true := by simp only [left,decide_eq_true_eq]; rintro (a|a); exact Or.inl (hp a); exact Or.inr (hp a)
    have v : right P i=true → right A i=true := by simp only [right,decide_eq_true_eq]; rintro (a|a); exact Or.inl (hp a); exact Or.inr (hp a)
    change (value P L false n=true → w.getD n false=true) ∧ (w.getD n false=true → value A B true n=true)
    simp only [value,ite_eq_right s,ite_eq_right t]
    change (slot P false i (n-j)=true → _) ∧ (_ → slot A true i (n-j)=true)
    by_cases z : n-j=0
    · have e : n=j := by omega
      rw [z]; change (left P i=true → _) ∧ (_ → left A i=true); rw [e,h.1]; exact ⟨id,u⟩
    by_cases a : n-j=1
    · have e : n=j+1 := by omega
      rw [a]; change (right P i=true → _) ∧ (_ → right A i=true); rw [e,h.2.1]; exact ⟨id,v⟩
    by_cases b : n-j=2
    · have e : n=j+2 := by omega
      rw [b]; change ((left P i || right P i)=true → _) ∧ (_ → (left A i || right A i)=true); rw [e,h.2.2,h.1,h.2.1]; refine ⟨id,?_⟩; simpa only [Bool.or_eq_true] using Or.imp u v
    · simp [slot,z,a,b]
  have eval_mono (C : Circuit) (hc : Monotone2 C) (x y : List Bool) (len : x.length=y.length) (le : ∀ i<x.length,x.getD i false=true → y.getD i false=true) : C.eval x=true → C.eval y=true := by
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have run (gs : List Gate) (hs : ∀ g∈gs,g.op=.and ∨ g.op=.or) (a b : List Bool) (sz : a.length=b.length) (h : ∀ i,a.getD i false=true → b.getD i false=true) : ∀ i,(gs.foldl step a).getD i false=true → (gs.foldl step b).getD i false=true := by
      induction gs generalizing a b with
      | nil => exact h
      | cons g gs ih => apply ih (fun q hq => hs q (List.mem_cons_of_mem _ hq)) (step a g) (step b g) (by simp [step,sz]); intro i
                        by_cases lo : i<a.length
                        · simpa only [step,List.getD_append _ _ _ _ lo,List.getD_append _ _ _ _ (sz ▸ lo)] using h i
                        by_cases eq : i=a.length
                        · have birth (v : List Bool) : (step v g).getD v.length false=g.op.eval (g.inputs.map fun i => v.getD i false) := by simp [step]
                          subst i; rw [birth,sz,birth]; rcases hs g List.mem_cons_self with u|u
                          · rw [u]; change (g.inputs.map fun k => a.getD k false).all id = true → (g.inputs.map fun k => b.getD k false).all id = true
                            simp only [List.all_eq_true,List.mem_map,id]; intro all v hv; obtain ⟨k,hk,rfl⟩ := hv; exact h k (all _ ⟨k,hk,rfl⟩)
                          · rw [u]; change (g.inputs.map fun k => a.getD k false).any id = true → (g.inputs.map fun k => b.getD k false).any id = true
                            simp only [List.any_eq_true,List.mem_map,id]; rintro ⟨_,⟨k,hk,rfl⟩,yes⟩; exact ⟨_,⟨k,hk,rfl⟩,h k yes⟩
                        · rw [List.getD_eq_default _ _ (by simp [step];omega)]; simp
    apply run C.gates (fun g hg => (hc g hg).1) x y len _ C.output; intro i; by_cases hi : i<x.length; exact le i hi; rw [List.getD_eq_default _ _ (by omega)]; simp
  let cfg : Fin 9 → Bool × Fin 13 × Fin 3 := fun i => (true,idx i.val,0)
  obtain ⟨C,mono,size,pos,neg⟩ := search
  refine ⟨cfg,C,mono,size,?_⟩
  intro P L w word
  obtain ⟨length,raw,packet⟩ := word
  have synced : read w P L := by
    refine ⟨raw,?_⟩; intro i
    have dor (a b : Prop) [Decidable a] [Decidable b] [Decidable (a∨b)] : decide (a∨b)=(decide a || decide b) := by by_cases x : a <;> by_cases y : b <;> simp [x,y]
    simpa [cfg,start,left,right,idx,dor] using packet i
  constructor
  · rintro ⟨p,l,rfl,rfl,inc,miss⟩
    have outside : 9≤l.val := by
      by_contra! small; apply miss; refine ⟨⟨l.val,small⟩,?_⟩; change idx l.val=l; exact Fin.ext (Nat.mod_eq_of_lt l.isLt)
    apply eval_mono C mono (row {p} {l} false) w (by simpa [row] using length.symm) _ (pos p l outside inc)
    intro n hn; exact (sandwich {p} {l} {p} {l} (fun _ h=>h) (fun _ h=>h) w synced ⟨n,by simpa [row] using hn⟩).1
  · intro ind pc lc
    obtain ⟨A,B,hp,hl,total,small,free⟩ := geometry P L ind pc lc
    apply Bool.eq_false_iff.mpr; intro hot
    have warm := eval_mono C mono w (row A B true) (by simpa [row] using length) (by
      intro n hn; exact (sandwich P L A B hp hl w synced ⟨n,by rwa [length] at hn⟩).2) hot
    have cold : C.eval (row A B true)=false := neg A B total small free
    rw [cold] at warm; contradiction
