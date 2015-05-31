header {* Solutions to Chapter 3 of "Concrete Semantics" *}

theory Chap_three imports Main begin

declare [[names_short]]

(* 3.1 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N a) = N a" |
"asimp_const (V x) = V x" |
"asimp_const (Plus p q) = 
 (case (asimp_const p, asimp_const q) of 
  (N a, N b) \<Rightarrow> N (a+b) |
  (x, y) \<Rightarrow> Plus x y)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N a) (N b) = N (a+b)" |
"plus p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus (N i) p = (if i = 0 then p else Plus (N i) p)" |
"plus p q = (Plus p q)"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N a) = N a" |
"asimp (V x) = V x" |
"asimp (Plus p q) = plus (asimp p) (asimp q)"

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N a) = True" |
"optimal (V x) = True" |
"optimal (Plus (N a) (N b)) = False" | 
"optimal (Plus x y) = ((optimal x) \<and> (optimal y))"

theorem asimp_const_optimal: "optimal (asimp_const a)"
apply (induction a)
apply (auto split: aexp.split)
done

(* 3.2 *)

fun plus_ex :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus_ex (N a) (N b) = N (a+b)" |
"plus_ex (Plus p (N a)) (N b) = Plus p (N (a+b))" |
"plus_ex (N b) (Plus p (N a)) = Plus p (N (a+b))" |
"plus_ex (Plus p (N a)) q = Plus (Plus p q) (N a)" |
"plus_ex q (Plus p (N a)) = Plus (Plus p q) (N a)" |
"plus_ex p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus_ex (N i) p = (if i = 0 then p else Plus p (N i))" |
"plus_ex p q = (Plus p q)"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N a) = N a" |
"full_asimp (V x) = V x" |
"full_asimp (Plus p q) = plus_ex (full_asimp p) (full_asimp q)"

value "full_asimp (Plus (Plus ((Plus (V ''x'') (N 7))) (V ''x'')) (N 5))" 

lemma aval_plus_ex: "aval (plus_ex p q) s = aval p s + aval q s"
apply (induction rule:plus_ex.induct)
apply (auto)
done

theorem "aval (full_asimp p) s = aval p s"
apply (induction p)
apply (auto simp add:aval_plus_ex)
done

(* 3.3 *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N k) = (N k)" |
"subst x a (V y) = (if x = y then a else (V y))" |
"subst x a (Plus p q) = Plus (subst x a p) (subst x a q)"

theorem aval_subst[simp]:  "aval (subst x a e) s = aval e (s(x:=aval a s))"
apply (induction e)
apply (auto)
done 

theorem "aval a s = aval b s \<Longrightarrow> aval (subst x a e) s = aval (subst x b e) s"
apply (auto)
done

(* 3.4 *)

datatype aexpm = Nm int | Vm vname | Plusm aexpm aexpm | Timesm aexpm aexpm

fun avalm :: "aexpm \<Rightarrow> state \<Rightarrow> val" where
"avalm (Nm a) s = a" |
"avalm (Vm x) s = s x" |
"avalm (Plusm a b) s = avalm a s + avalm b s" |
"avalm (Timesm a b) s = avalm a s * avalm b s"

fun plusm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"plusm (Nm a) (Nm b) = Nm (a+b)" |
"plusm p (Nm i) = (if i = 0 then p else Plusm p (Nm i))" |
"plusm (Nm i) p = (if i = 0 then p else Plusm (Nm i) p)" |
"plusm p q = (Plusm p q)"

fun timesm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"timesm (Nm a) (Nm b) = Nm (a*b)" |
"timesm p (Nm i) = (if i = 0 then (Nm 0) else if i = 1 then p else Timesm p (Nm i))" |
"timesm (Nm i) p = (if i = 0 then (Nm 0) else if i = 1 then p else Timesm p (Nm i))" |
"timesm p q = (Timesm p q)"

fun asimpm :: "aexpm \<Rightarrow> aexpm" where
"asimpm (Nm a) = Nm a" |
"asimpm (Vm x) = Vm x" |
"asimpm (Plusm p q) = plusm (asimpm p) (asimpm q)" |
"asimpm (Timesm p q) = timesm (asimpm p) (asimpm q)"

lemma avalm_plus[simp]: "avalm (plusm p q) s = avalm p s + avalm q s"
apply (induction rule:plusm.induct)
apply (auto)
done

lemma avalm_times[simp]: "avalm (timesm p q) s = avalm p s * avalm q s"
apply (induction rule:timesm.induct)
apply (auto)
done

theorem "avalm (asimpm p) s = avalm p s"
apply (induction p)
apply (auto)
done 

(*  3.5 *)

datatype aexp2 = N2 int | V2 vname | PlusPlus2 vname | Plus2 aexp2 aexp2 | 
 Times2 aexp2 aexp2 | Div2 aexp2 aexp2 

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N2 a) s = Some (a, s)" |
"aval2 (V2 x) s = Some (s x, s)" |
"aval2 (PlusPlus2 x) s = Some (s x, s(x:= 1 + (s x)))" |
"aval2 (Plus2 a b) s = 
 (case (aval2 a s, aval2 b s) of 
  (None, Some q) \<Rightarrow> None |
  (Some p, None) \<Rightarrow> None |
  (Some p, Some q) \<Rightarrow> Some ((fst p + fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
"aval2 (Times2 a b) s = 
 (case (aval2 a s, aval2 b s) of 
  (None, Some q) \<Rightarrow> None |
  (Some p, None) \<Rightarrow> None |
  (Some p, Some q) \<Rightarrow> Some ((fst p * fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
"aval2 (Div2 a b) s =
 (case (aval2 a s, aval2 b s) of 
  (None, Some q) \<Rightarrow> None |
  (Some p, None) \<Rightarrow> None |
  (Some p, Some q) \<Rightarrow> 
   (if fst q = 0 then 
    None 
   else Some ((fst p div fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x)))))"

(* 3.6 *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl a) s = a" |
"lval (Vl x) s = s x" |
"lval (Plusl p q) s = lval p s + lval q s" |
"lval (LET x a e) s = lval e (s(x:=lval a s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl a) = (N a)" |
"inline (Vl x) = (V x)" |
"inline (Plusl p q) = Plus (inline p) (inline q)" |
"inline (LET x a e) = subst x (inline a) (inline e)"  

theorem "aval (inline e) s = lval e s"
apply (induction e arbitrary:s)
apply (auto)
done

(* 3.7 *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And a b) s = (bval a s \<and> bval b s)" |
"bval (Less a b) s = (aval a s < aval b s)"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n) (N m) = Bc(n < m)" |
"less a b = Less a b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and a b = And a b"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And a b) = and (bsimp a) (bsimp b)" |
"bsimp (Less a b) = less (asimp a) (asimp b)"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq p q = And (Not (Less p q)) (Not (Less q p))"

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le p q = Not (Less q p)"

theorem "bval (Eq p q) s = (aval p s = aval q s)"
apply (auto simp add:Eq_def)
done

theorem "bval (Le p q) s = (aval p s \<le> aval q s)"
apply (auto simp add:Le_def)
done

(* 3.8 *)

definition or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"or p q = Not (And (Not p) (Not q))"

definition implies :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"implies p q = or (Not p) q"

definition bIf :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"bIf a b c = And (implies a b) (implies (Not a) c)"

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp
 
fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) s = b" |
"ifval (If a b c) s = (if (ifval a s) then (ifval b s) else (ifval c s))" |
"ifval (Less2 x y) s = (aval x s < aval y s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b) = Bc2 b" |
"b2ifexp (Not b) = (If (b2ifexp b) (Bc2 False) (Bc2 True))" |
"b2ifexp (And a b) = (If (b2ifexp a) (b2ifexp b) (Bc2 False))" |
"b2ifexp (Less x y) = (Less2 x y)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = Bc b" |
"if2bexp (If a b c) = bIf (if2bexp a) (if2bexp b) (if2bexp c)" |
"if2bexp (Less2 x y) = (Less x y)"

theorem "bval (if2bexp p) s = ifval p s"
apply (induction p)
apply (auto simp add:bIf_def implies_def or_def)
done

theorem "ifval (b2ifexp p) s = bval p s"
apply (induction p)
apply (auto)
done

(* 3.9 *)

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NOT a) s = (\<not>pbval a s)" |
"pbval (AND a b) s = (pbval a s \<and> pbval b s)" |
"pbval (OR a b) s = (pbval a s \<or> pbval b s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR x)) = True" |
"is_nnf (NOT p) = False" |
"is_nnf (AND p q) = (is_nnf p \<and> is_nnf q)" |
"is_nnf (OR p q) = (is_nnf p \<and> is_nnf q)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = (VAR x)" |
"nnf (NOT (VAR p)) = (NOT (VAR p))" |
"nnf (NOT (NOT p)) = nnf p" |
"nnf (NOT (AND p q)) = OR (nnf (NOT p)) (nnf (NOT q))" |
"nnf (NOT (OR p q)) = AND (nnf (NOT p)) (nnf (NOT q))" |
"nnf (AND p q) = AND (nnf p) (nnf q)" |
"nnf (OR p q) = OR (nnf p) (nnf q)"

lemma not_nnf[simp]: "pbval (nnf (NOT p)) s = (\<not> (pbval (nnf p) s))"
apply (induction p)
apply (auto)
done

theorem "pbval (nnf p) s = pbval p s"
apply (induction p)
apply (auto)
done

lemma nnf_n: "is_nnf (nnf p)"
apply (induction p rule:nnf.induct)
apply (auto)
done

fun andb :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"andb p (OR h t) = OR (andb p h) (andb p t)" |
"andb (OR h t) p = OR (andb h p) (andb t p)" |
"andb p q = AND p q"

lemma pbval_andb: "pbval (andb a b) s = pbval (AND a b) s"
apply (induction a b rule:andb.induct)
apply (auto)
done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NOT p) = NOT p" |
"dnf_of_nnf (OR p q) = OR (dnf_of_nnf p) (dnf_of_nnf q)" |
"dnf_of_nnf (AND p q) = andb (dnf_of_nnf p) (dnf_of_nnf q)"

theorem "pbval (dnf_of_nnf p) s = pbval p s"
apply (induction p)
apply (auto simp add: pbval_andb)
done

fun is_no_or :: "pbexp \<Rightarrow> bool" where
"is_no_or (VAR x) = True" |
"is_no_or (NOT p) = True" |
"is_no_or (AND p q) = ((is_no_or p) \<and> (is_no_or q))" |
"is_no_or (OR p q) = False"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NOT p) = True" |
"is_dnf (AND p q) = ((is_no_or p) \<and> (is_no_or q))" |
"is_dnf (OR p q) = ((is_dnf p) \<and> (is_dnf q))"

lemma isdnf_andb: "is_dnf p \<Longrightarrow> is_dnf q \<Longrightarrow> is_dnf (andb p q)"
apply (induction p q rule:andb.induct)
apply (auto)
done 

theorem "is_nnf p \<Longrightarrow> is_dnf (dnf_of_nnf p)"
apply (induction p)
apply (auto simp add: isdnf_andb)
done

(* 3.10 *)

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

abbreviation hd2 where 
"hd2 xs \<equiv> hd (tl xs)"

abbreviation tl2 where 
"tl2 xs \<equiv> tl (tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n # stk)" |
"exec1 (LOAD x) s stk = Some (s(x) # stk)" |
"exec1 ADD _ stk = 
 (case stk of 
  (x # y # xs) \<Rightarrow> Some ((hd2 stk + hd stk) # tl2 stk) |
  (xs) \<Rightarrow> None)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = 
 (case (exec1 i s stk) of 
  Some res \<Rightarrow> exec is s res |
  None \<Rightarrow> None)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_append: "exec is1 s stk = Some new_stk \<Longrightarrow> exec (is1 @ is2) s stk = exec is2 s new_stk"
apply (induction is1 arbitrary:stk)
apply (auto split:option.split)
done

lemma "exec (comp a) s stk = Some (aval a s # stk)"
apply (induction a arbitrary:stk)
apply (auto simp add: exec_append)
done

(* 3.11 *)

type_synonym reg = nat 

datatype rinstr = LDI val reg | LD vname reg | ADD reg reg

fun rexec1 :: "rinstr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec1 (LDI n r) s rs = rs(r:=n)" |
"rexec1 (LD v r) s rs = rs(r:=(s v))" |
"rexec1 (ADD r q) s rs = rs(r:=(rs r)+(rs q))"

fun rexec :: "rinstr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"rexec [] s rs = rs" |
"rexec (x # xs) s rs = rexec xs s (rexec1 x s rs)"

fun rcomp :: "aexp \<Rightarrow> reg \<Rightarrow> rinstr list" where
"rcomp (N n) r = [LDI n r]" |
"rcomp (V x) r = [LD x r]" |
"rcomp (Plus p q) r = (rcomp p r) @ (rcomp q (r+1)) @ ([ADD r (r+1)])"

lemma rexec_app[simp]: "rexec (xs @ ys) s rs = rexec ys s (rexec xs s rs)"
apply (induction xs arbitrary: rs)
apply (auto)
done

lemma rcomp_respects: "r < q \<Longrightarrow> rexec (rcomp a q) s rs r = rs r"
apply (induction a arbitrary: rs r q)
apply (auto)
done

theorem "rexec (rcomp a r) s rs r = aval a s"
apply (induction a arbitrary:rs r)
apply (auto simp add: rcomp_respects)
done

(* 3.12 *)

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg 

fun exec10 :: "instr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec10 (LDI0 n) s rs = rs(0:=n)" |
"exec10 (LD0 v) s rs = rs(0:=(s v))" |
"exec10 (MV0 r) s rs = rs(r:=(rs 0))" |
"exec10 (ADD0 r) s rs = rs(0:=(rs 0)+(rs r))"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
"exec0 [] s rs = rs" |
"exec0 (x # xs) s rs = exec0 xs s (exec10 x s rs)"

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp0 (N n) r = [LDI0 n]" |
"comp0 (V x) r = [LD0 x]" |
"comp0 (Plus p q) r = (comp0 p (r+1)) @ [MV0 (r+1)] @ (comp0 q (r+2)) @ [ADD0 (r+1)]"

lemma exec0_app[simp]: "exec0 (xs @ ys) s rs = exec0 ys s (exec0 xs s rs)"
apply (induction xs arbitrary: rs)
apply (auto)
done

lemma comp0_respects: "(0 < r) \<and> (r \<le> q) \<Longrightarrow> exec0 (comp0 a q) s rs r = rs r"
apply (induction a arbitrary: rs r q)
apply (auto)
done

theorem "exec0 (comp0 a r) s rs 0 = aval a s"
apply (induction a arbitrary:rs r)
apply (auto simp add:comp0_respects)
done

end
