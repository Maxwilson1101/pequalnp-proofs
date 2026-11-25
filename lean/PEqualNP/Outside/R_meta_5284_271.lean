import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.PairShadow

-- Zeroing all vertices of an isolated star must pay for putting the star back.
-- A nonempty residual graph needs the joining OR. An empty residual graph does not.
set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_5284_271
    (pin : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (S : Finset (Fin n)),
      (∀ u v,H.Adj u v ↔ u∉S ∧ v∉S ∧ G.Adj u v) → (∀ v∈S,∃ u,G.Adj v u) →
      let one := fun (C : Circuit) => ∀ j g,C.gates[j]?=some g → g.op=GateOp.and → ∀ T : Finset (Fin n),T.card≤1 →
        gateVal n C j (fun i=>decide (i∈T))=false
      ∀ C : Circuit, Monotone2 C → circuitFun n C=graphFun G ∅ → one C →
      ∃ D : Circuit,Monotone2 D ∧ circuitFun n D=graphFun H ∅ ∧ one D ∧ D.size+S.card≤C.size+(if ∃ a b,H.Adj a b then 0 else 1))
    (irreducible : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
      (∀ a b,G.Adj a b → ∃ u v,G.Adj a u ∧ G.Adj u v ∧ v≠a) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C=graphFun G ∅ →
      (∀ j g,C.gates[j]?=some g → g.op=GateOp.and → ∀ T : Finset (Fin n),T.card≤1 → gateVal n C j (fun i=>decide (i∈T))=false) →
      ∃ D : Circuit, Monotone2 D ∧ D.size≤C.size ∧ (∀ u v,G.Adj u v → circuitFun n D (pairInput u v)=true) ∧
      (∀ u : Fin n,circuitFun n D (unitInput u)=false) ∧
      ∀ j g,D.gates[j]?=some g → g.op=GateOp.and → ∀ T : Finset (Fin n),T.card≤2 →
        gateVal n D j (fun i=>decide (i∈T))=true → ∃ a∈T,∃ b∈T,G.Adj a b) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22 := by
  classical
  intro n G inst postedFun postedRow postedOne trig sqg C M E O
  let X (k : ℕ) := Fin k→Bool
  let rd (w : List Bool) (i : ℕ) := w.getD i false
  let app (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (rd w))]
  let run (p : List Gate) (x : X n) := p.foldl app (List.ofFn x)
  let get (p : List Gate) (x : X n) (i : ℕ) := (run p x).getD i false
  have fold_prefix (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl app w = w ++ t := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih => obtain ⟨t,h⟩:=ih (app w g);exact ⟨_::t,by simpa [app,List.append_assoc] using h⟩
  have raw (p : List Gate) (x : X n) (i : Fin n) : get p x i=x i := by
    obtain ⟨t,e⟩:=fold_prefix p (List.ofFn x);change (p.foldl app (List.ofFn x)).getD i false=_
    rw [e,List.getD_append _ _ _ _ (by simp)];simp [List.getD_eq_getElem?_getD,i.isLt]
  have len (p : List Gate) (x : X n) : (run p x).length=n+p.length := by
    have ln (l : List Gate) (w : List Bool) : (l.foldl app w).length=w.length+l.length := by
      induction l generalizing w with
      | nil => simp
      | cons g l ih => simp [List.foldl_cons,ih,app,Nat.add_assoc,Nat.add_comm 1]
    simp [run,ln]
  have snoc (p : List Gate) (x : X n) (g : Gate) : run (p++[g]) x=run p x++[g.op.eval (g.inputs.map (get p x))] := by
    simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil];rfl
  have fresh (p : List Gate) (x : X n) (g : Gate) : get (p++[g]) x (n+p.length)=g.op.eval (g.inputs.map (get p x)) := by
    change (run (p++[g]) x).getD _ false=_;rw [snoc,←len p x];simp
  let on (s : Finset (Fin n)) (i : Fin n) := decide (i∈s)
  let hit (H : SimpleGraph (Fin n)) (x : X n) := ∃ a b,H.Adj a b ∧ x a=true ∧ x b=true
  let fits (H : SimpleGraph (Fin n)) (D : Circuit) := ∀ x,D.eval (List.ofFn x)=true ↔ hit H x
  let one (D : Circuit) := ∀ j g,D.gates[j]?=some g → g.op=GateOp.and → ∀ s : Finset (Fin n),s.card≤1 → get D.gates (on s) (n+j)=false
  have fun_bool (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (x : X n) : graphFun H ∅ x = decide (∃ a b,H.Adj a b ∧ x a=true ∧ x b=true) := by
    change (decide (∃ a∈(∅:Finset (Fin n)),x a=true) || _) = _;simp
  have fun_iff (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (D : Circuit) : circuitFun n D=graphFun H ∅ ↔ fits H D := by
    constructor
    · intro e x;change circuitFun n D x = true ↔ _;rw [e,fun_bool];exact decide_eq_true_iff
    · intro e;funext x;rw [fun_bool];apply Bool.eq_iff_iff.mpr;rw [decide_eq_true_iff];exact e x
  let safe2 (G : SimpleGraph (Fin n)) (C : Circuit) := ∀ j g,C.gates[j]?=some g → g.op=.and → ∀ T : Finset (Fin n),T.card≤2 → get C.gates (on T) (n+j)=true → ∃ a∈T,∃ b∈T,G.Adj a b
  let result (G : SimpleGraph (Fin n)) (C : Circuit) := Monotone2 C ∧ (∀ u v,G.Adj u v → C.eval (List.ofFn (on {u,v}))=true) ∧ (∀ u : Fin n,C.eval (List.ofFn (on {u}))=false) ∧ safe2 G C
  have beforeTail (p tail : List Gate) (x:X n) (i : ℕ) (hi:i<n+p.length) : get (p++tail) x i=get p x i := by
    obtain ⟨t,e⟩:=fold_prefix tail (run p x);change ((p++tail).foldl app (List.ofFn x)).getD i false=_
    rw [List.foldl_append];change (tail.foldl app (run p x)).getD i false=_;rw [e];apply List.getD_append;simpa [len] using hi
  have builder (p : List Gate) (b : Fin n) (L : List (Fin n)) : ∃ t : List Gate, ∃ r : ℕ,t.length=L.length ∧ r<n+(p++t).length ∧ (∀ g∈t, g.op=.or ∧ g.inputs.length≤2) ∧
      ∀ x : X n,get (p++t) x r=true ↔ ∃ v∈b::L,x v=true := by
    induction L using List.reverseRecOn with
    | nil => exact ⟨[],b,rfl,by simp;omega,by simp,by intro x;rw [List.append_nil,show get p x b=x b from raw ..];simp⟩
    | append_singleton L v ih =>
      obtain ⟨t,r,sz,valid,all,funct⟩:=ih;let q:Gate:=⟨.or,[r,v.val]⟩
      refine ⟨t++[q],n+(p++t).length,by simp [sz],by simp,?_,?_⟩
      · intro k hk;rcases List.mem_append.mp hk with h|h;exact all k h;obtain rfl:=List.mem_singleton.mp h;exact ⟨rfl,Nat.le_refl 2⟩
      · intro x;rw [←List.append_assoc,fresh];change ([get (p++t) x r,get (p++t) x v].any id=true) ↔ _
        have raw : get (p++t) x v=x v := raw ..
        simp [raw,funct x,or_assoc]
  have starJoin (G H : SimpleGraph (Fin n)) (a : Fin n) (U : Finset (Fin n)) (non : U.Nonempty) (out : a∉U)
      (edges : ∀ u v,G.Adj u v ↔ H.Adj u v ∨ (u=a ∧ v∈U) ∨ (v=a ∧ u∈U)) (base : Circuit) (ok : result H base) (use : Bool)
      (baseOK : use=true → base.output<n+base.size) (empty : use=false → ∀ u v,¬H.Adj u v) :
      ∃ D : Circuit,result G D ∧ D.size=base.size+U.card+(if use then 1 else 0) := by
    classical
    let l:=U.toList
    obtain ⟨b,L,bl⟩ : ∃ b L,l=b::L := by
      cases e:l with
      | nil =>
        obtain ⟨i,hi⟩:=non
        have h:i∈l:=by simpa [l] using hi
        rw [e] at h;cases h
      | cons b L => exact ⟨b,L,rfl⟩
    have members (i : Fin n) : i∈b::L ↔ i∈U := by rw [←bl];simp [l]
    have sz:U.card=L.length+1 := by rw [←Finset.length_toList];change l.length=_;rw [bl];rfl
    obtain ⟨t,r,tlen,valid,orOnly,read⟩:=builder base.gates b L
    let p:=base.gates++t;let h:Gate:=⟨.and,[a.val,r]⟩;let w:=n+p.length;let c:=p++[h];let top:Gate:=⟨.or,[base.output,w]⟩
    let tail:=if use then [top] else [];let D:Circuit:=⟨c++tail,if use then n+c.length else w⟩
    have atH (x:X n) : get c x w=true ↔ x a=true ∧ ∃ v∈U,x v=true := by
      rw [show c=p++[h] by rfl,show w=n+p.length by rfl,fresh];change ([get p x a,get p x r].all id=true) ↔ _
      have raw:get p x a=x a:=raw ..
      rw [raw];simp [show p=base.gates++t by rfl,read x,members]
    have evalD (x:X n) : D.eval (List.ofFn x)=true ↔ (use=true ∧ base.eval (List.ofFn x)=true) ∨ (x a=true ∧ ∃ v∈U,x v=true) := by
      cases u:use with
      | false =>
        change get (c++tail) x (if use then n+c.length else w)=true ↔ _
        simpa [tail,u] using atH x
      | true =>
        change get (c++tail) x (if use then n+c.length else w)=true ↔ _;rw [u];simp only [tail,u,if_true,Bool.true_and,true_and];rw [fresh]
        change [get c x base.output,get c x w].any id=true ↔ _
        have old:get c x base.output=base.eval (List.ofFn x) := by change get ((base.gates++t)++[h]) x _=_;rw [List.append_assoc];exact beforeTail _ _ _ _ (baseOK u)
        simp [old,atH x]
    refine ⟨D,⟨?_,?_,?_,?_⟩,?_⟩
    · intro k hk;change k∈(base.gates++t++[h])++tail at hk
      simp only [List.mem_append,List.mem_singleton] at hk;rcases hk with ((hb|ht)|rfl)|ht
      · exact ok.1 k hb
      · exact ⟨Or.inr (orOnly k ht).1,(orOnly k ht).2⟩
      · exact ⟨Or.inl rfl,Nat.le_refl 2⟩
      · cases u:use <;> simp [tail,u] at ht;subst k;exact ⟨Or.inr rfl,Nat.le_refl 2⟩
    · intro u v uv;apply (evalD _).mpr;rcases (edges _ _).mp uv with old|⟨rfl,hv⟩|⟨rfl,hu⟩
      · left;refine ⟨?_,ok.2.1 _ _ old⟩
        cases bit:use with
        | false => exact (empty bit u v old).elim
        | true => rfl
      · right;exact ⟨by simp [on],v,hv,by simp [on]⟩
      · right;exact ⟨by simp [on],u,hu,by simp [on]⟩
    · intro v;apply Bool.eq_false_iff.mpr;intro hit;rcases (evalD _).mp hit with ⟨_,hit⟩|⟨ha,i,hi,vi⟩
      · rw [ok.2.2.1] at hit;contradiction
      · have av:a=v:=by simpa [on] using ha
        have iv:i=v:=by simpa [on] using vi
        exact out (av.symm ▸ iv ▸ hi)
    · intro j k loc tag T two lit
      by_cases hj:j<base.gates.length
      · have pos:n+j<n+base.gates.length:=by omega
        have lookup:base.gates[j]?=some k:=by simpa [D,c,p,List.append_assoc,List.getElem?_append_left hj] using loc
        have keep : get D.gates (on T) (n+j)=get base.gates (on T) (n+j) := by change get ((base.gates++t++[h])++tail) _ _=_;simp only [List.append_assoc];exact beforeTail _ _ _ _ pos
        obtain ⟨u,hu,v,hv,uv⟩:=ok.2.2.2 _ _ lookup tag T two (keep ▸ lit);exact ⟨u,hu,v,hv,(edges _ _).mpr (Or.inl uv)⟩
      · have find : j=p.length := by
          by_cases lt:j<p.length
          · have hp:p[j]?=some k := by simpa [D,c,List.append_assoc,List.getElem?_append_left lt] using loc
            have ht:k∈t := by change (base.gates++t)[j]?=some k at hp;rw [List.getElem?_append_right (by omega)] at hp;exact List.mem_of_getElem? hp
            have := (orOnly k ht).1;rw [tag] at this;contradiction
          · by_contra ne;have hc:c.length≤j:=by simp [c];omega
            have ht:k∈tail := by change (c++tail)[j]?=some k at loc;rw [List.getElem?_append_right hc] at loc;exact List.mem_of_getElem? loc
            cases u:use <;> simp [tail,u] at ht;subst k;cases tag
        subst j;have pos:w<n+c.length:=by simp [w,c]
        have keep:get D.gates (on T) w=get c (on T) w:=beforeTail _ _ _ _ pos
        obtain ⟨ha,v,hv,onv⟩:=(atH _).mp (keep ▸ lit)
        exact ⟨a,of_decide_eq_true ha,v,of_decide_eq_true onv,(edges _ _).mpr (Or.inr (Or.inl ⟨rfl,hv⟩))⟩
    · change (c++tail).length=base.gates.length+U.card+(if use then 1 else 0)
      cases u:use <;> simp [c,p,tail,u,tlen,sz,Nat.add_assoc]
  let triangle (G : SimpleGraph (Fin n)) := ∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a
  let square (G : SimpleGraph (Fin n)) := ∀ a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d
  let core (G : SimpleGraph (Fin n)) := ∀ a b,G.Adj a b → ∃ u v,G.Adj a u ∧ G.Adj u v ∧ v≠a
  have peel (pin : ∀ (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (S : Finset (Fin n)),
      (∀ u v,H.Adj u v ↔ u∉S ∧ v∉S ∧ G.Adj u v) → (∀ v∈S,∃ u,G.Adj v u) → ∀ C : Circuit,Monotone2 C → fits G C → one C →
      ∃ D : Circuit,Monotone2 D ∧ fits H D ∧ one D ∧ D.size+S.card≤C.size+(if ∃ a b,H.Adj a b then 0 else 1))
      (solve : ∀ G : SimpleGraph (Fin n), triangle G → square G → core G → ∀ C : Circuit,Monotone2 C → fits G C → one C → ∃ D : Circuit,result G D ∧ D.size≤C.size)
      (G : SimpleGraph (Fin n)) (tri : triangle G) (sq : square G) (C : Circuit) (M : Monotone2 C) (E : fits G C) (O : one C) : ∃ D : Circuit,result G D ∧ D.size≤C.size := by
    classical
    generalize hc:C.size=k
    induction k using Nat.strong_induction_on generalizing G C with
    | ind k ih =>
      by_cases done:core G
      · obtain ⟨D,res,le⟩:=solve G tri sq done C M E O;exact ⟨D,res,hc ▸ le⟩
      · unfold core at done;push Not at done;obtain ⟨a,b,ab,leaf⟩:=done
        let U:=Finset.univ.filter (G.Adj a);let S:=insert a U
        have mem (i : Fin n) : i∈U ↔ G.Adj a i := by simp [U]
        have non:U.Nonempty:=⟨b,(mem b).mpr ab⟩;have out:a∉U:=fun h=>G.loopless.irrefl a ((mem a).mp h)
        have size:S.card=U.card+1:=Finset.card_insert_of_notMem out
        let H : SimpleGraph (Fin n) := {Adj:=fun u v=>u∉S ∧ v∉S ∧ G.Adj u v,symm:=⟨fun _ _ h=>⟨h.2.1,h.1,h.2.2.symm⟩⟩,loopless:=⟨fun _ h=>h.2.2.ne rfl⟩}
        have rest (i j) : H.Adj i j ↔ i∉S ∧ j∉S ∧ G.Adj i j:=Iff.rfl
        have active (i) (hi:i∈S) : ∃ u,G.Adj i u := by rcases Finset.mem_insert.mp hi with rfl|h;exact ⟨b,ab⟩;exact ⟨a,((mem i).mp h).symm⟩
        obtain ⟨D,dm,de,du,budget⟩:=pin G H S rest active C M E O
        have ht:triangle H:=fun u v w uv vw wu=>tri _ _ _ uv.2.2 vw.2.2 wu.2.2
        have hs:square H:=fun u v w r uv vw wr ru=>sq _ _ _ _ uv.2.2 vw.2.2 wr.2.2 ru.2.2
        have pos:=Finset.card_pos.mpr non
        have small:D.size<k := by split at budget <;> omega
        obtain ⟨T,tok,ts⟩:=ih D.size small H ht hs D dm de du rfl
        have edges (u v) : G.Adj u v ↔ H.Adj u v ∨ u=a ∧ v∈U ∨ v=a ∧ u∈U := by
          constructor
          · intro uv;by_cases ua:u=a
            · subst u;exact Or.inr (Or.inl ⟨rfl,(mem _).mpr uv⟩)
            by_cases va:v=a
            · subst v;exact Or.inr (Or.inr ⟨rfl,(mem _).mpr uv.symm⟩)
            left;apply (rest _ _).mpr;refine ⟨?_,?_,uv⟩
            · intro m;rcases Finset.mem_insert.mp m with m|m;exact ua m;exact va (leaf u v ((mem _).mp m) uv)
            · intro m;rcases Finset.mem_insert.mp m with m|m;exact va m;exact ua (leaf v u ((mem _).mp m) uv.symm)
          · rintro (uv|⟨rfl,hv⟩|⟨rfl,hu⟩);exact uv.2.2;exact (mem _).mp hv;exact ((mem _).mp hu).symm
        let use:=decide (∃ u v,H.Adj u v)
        have wire (h:use=true) : T.output<n+T.size := by
          obtain ⟨u,v,uv⟩:=of_decide_eq_true h;have yes:=tok.2.1 u v uv
          by_contra! invalid
          change (run T.gates (on {u,v})).getD T.output false=true at yes
          rw [List.getD_eq_default _ _ (by rw [len];exact invalid)] at yes;contradiction
        have absent (h:use=false) (u v) (uv:H.Adj u v) : False := (of_decide_eq_false h) ⟨u,v,uv⟩
        obtain ⟨F,ok,count⟩:=starJoin G H a U non out edges T tok use wire absent
        refine ⟨F,ok,?_⟩;by_cases more:∃ u v,H.Adj u v <;> simp [use,more] at budget count <;> omega
  have pair (u v : Fin n) : on {u,v}=pairInput u v := by funext i;change decide (i∈({u,v}:Finset (Fin n)))=decide (i=u ∨ i=v);simp
  have unit (u : Fin n) : on {u}=unitInput u := by funext i;change decide (i∈({u}:Finset (Fin n)))=decide (i=u);simp
  have init : fits G C := by intro x;rw [E];exact decide_eq_true_iff
  obtain ⟨D,ok,le⟩:=peel (by
    intro J H decH S rel act K km ke ko
    obtain ⟨T,tm,te,to_,budget⟩:=pin n J H S rel act K km ((fun_iff J K).mpr ke) ko
    exact ⟨T,tm,(fun_iff H T).mp te,to_,budget⟩) (by
    intro H tri sq cf K km ke ko
    obtain ⟨T,tm,ts,tp,tu,ta⟩:=irreducible n H tri sq cf K km ((fun_iff H K).mpr ke) ko
    refine ⟨T,⟨tm,?_,?_,ta⟩,ts⟩
    · intro u v uv;rw [pair];exact tp u v uv
    · intro u;rw [unit];exact tu u) G trig sqg C M init O
  exact ⟨D,ok.1,le,ok.2.1,ok.2.2.1,ok.2.2.2⟩
