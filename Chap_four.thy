header {* Solutions to Chapter 4 of "Concrete Semantics" *}

theory Chap_four imports Main begin

declare [[names_short]]

(* 4.1 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l x r) =  {x} \<union> set l \<union> set r"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l x r) = ((\<forall> y \<in> set l. x \<ge> y) \<and> (\<forall> y \<in> set r. y \<ge> x) \<and> ord l \<and> ord r)"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins a Tip = Node Tip a Tip" |
"ins a (Node r x l) = 
 (if a = x then 
  Node r x l 
 else if x > a then 
  Node (ins a r) x l 
 else Node r x (ins a l))"

theorem set_ins[simp]: "set (ins x t) = {x} \<union> set t"
apply (induction t)
apply (auto)
done

theorem "ord t \<Longrightarrow> ord (ins i t)"
apply (induction t)
apply (auto)
done

(* 4.2 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
pal0: "palindrome []" |
pal1: "palindrome [x]" |
pal_SS: "palindrome l \<Longrightarrow> palindrome (a # (l @ [a]))"

theorem rev_pal: "palindrome l \<Longrightarrow> rev l = l"
apply (induction rule:palindrome.induct)
apply (auto)
done

(* 4.3 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>  bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z  \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>  bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_star': "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
apply (induction rule:star.induct)
apply (auto intro: refl step)
done

lemma star'_star: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"

apply (induction rule:star'.induct)
apply (auto intro: refl' step')
done

theorem "star r x y \<Longrightarrow> star' r x y"
apply (induction rule:star.induct)
apply (auto simp add: refl' intro:  star'_star)
done

theorem "star' r x y \<Longrightarrow> star r x y"
apply (induction rule:star'.induct)
apply (auto simp add: refl intro: star_star')
done

(* 4.4 *)

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
it0: "iter r 0 x x" |
it_SS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

theorem "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
apply (induction rule:star.induct)
apply (auto intro: it0 it_SS)
done

(* 4.5 *)

datatype alpha = alef | bet | gimel

type_synonym str = "alpha list"

inductive S :: "str \<Rightarrow> bool" where
S_0: "S []" |
S_wrp: "S w \<Longrightarrow> S (a # w @ [b])" |
S_cc: "S w \<Longrightarrow> S u \<Longrightarrow> S (w @ u)"

inductive T :: "str \<Rightarrow> bool" where
T_0: "T []" |
T_intr: "T w \<Longrightarrow> T u \<Longrightarrow> T (w @ [a] @ u @ [b])" 

lemma T_comm: "T u \<Longrightarrow> T w \<Longrightarrow> T (w @ u)"
apply (induction  rule:T.induct)
apply (simp)
apply (metis T_intr append_assoc)
done

theorem T_S: "T w \<Longrightarrow> S w"
apply (induction rule:T.induct)
apply (auto intro: S_0 S_cc S_wrp)
done

theorem S_T: "S w \<Longrightarrow> T w"
apply (induction rule:S.induct)
apply (simp add: T_0)
apply (metis T_0 T_intr append_Cons append_Nil)
apply (auto intro: T_comm)
done

theorem "S w = T w"
apply (auto simp add: S_T T_S)
done

(* 4.6 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

inductive rel_aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
ar_N: "rel_aval (N a) s a" |
ar_V: "rel_aval (V x) s (s x)" |
ar_Plus: "rel_aval p s p_v \<Longrightarrow> rel_aval q s q_v \<Longrightarrow> rel_aval (Plus p q) s (p_v + q_v)" 

theorem rel_aval_aval: "rel_aval a s v \<Longrightarrow> aval a s = v"
apply (induction rule: rel_aval.induct)
apply (auto)
done

theorem aval_rel_aval: "aval a s = v \<Longrightarrow> rel_aval a s v"
apply (induction a arbitrary: v)
apply (auto intro: ar_N ar_V ar_Plus)
done

theorem "rel_aval a s v \<longleftrightarrow> aval a s = v"
apply (rule iffI)
apply (auto intro: aval_rel_aval rel_aval_aval)
done 

(* 4.7 *)

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

abbreviation hd2 where 
"hd2 xs \<equiv> hd (tl xs)"

abbreviation tl2 where 
"tl2 xs \<equiv> tl (tl xs)"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec1 (LOADI n) _ stk = (n # stk)" |
"exec1 (LOAD x) s stk = (s(x) # stk)" |
"exec1 ADD _ stk = (hd2 stk + hd stk) # tl2 stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
"exec [] _ stk = stk" |
"exec (i#is) s stk = exec is s (exec1 i s stk)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
ok_0: "ok n [] n" |
ok_LI: "ok n is n' \<Longrightarrow> ok n (is @ [LOADI k]) (Suc n')" |
ok_L: "ok n is n' \<Longrightarrow> ok n (is @ [LOAD x]) (Suc n')" |
ok_A: "ok n is (Suc (Suc n')) \<Longrightarrow> ok n (is @ [ADD]) (Suc n')"

lemma exec_append: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
apply (induction is1 arbitrary:stk)
apply (auto split:option.split)
done

theorem "ok n is n' \<Longrightarrow> length stk = n \<Longrightarrow> length (exec is s stk) = n'"
apply (induction arbitrary: stk rule:ok.induct)
apply (auto simp add: exec_append)
done

lemma ok_append: "ok n' b n'' \<Longrightarrow> ok n a n' \<Longrightarrow> ok n (a @ b) n''"
apply (induction  rule: ok.induct)
apply (simp)
apply (metis append_assoc ok_LI)
apply (metis append_assoc ok_L)
apply (metis append_assoc ok_A)
done

theorem "ok n (comp a) (Suc n)"
apply (induction a arbitrary: n)
apply (simp, metis List.append.simps(1) ok_0 ok_LI)
apply (simp, metis List.append.simps(1) ok_0 ok_L)
apply (auto intro: ok_append ok_A)
done


end
