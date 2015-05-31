header {* Solutions to Chapter 7 of "Concrete Semantics" *}
  
theory Chap_seven imports Big_step Small_step begin

declare [[names_short]]

(* 7.1 *)

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (c1;;c2) = assigned c1 \<union> assigned c2" |
"assigned (x ::= a) = {x}" |
"assigned (IF b THEN c1 ELSE c2) = assigned c1 \<union> assigned c2" |
"assigned (WHILE b DO c) = assigned c" 

lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
apply (induction rule: big_step_induct)
apply (auto)
done

(* 7.2 *)

fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True" |
"skip (c1;;c2) = (skip c1 \<and> skip c2)" |
"skip (x::=a) = False" |
"skip (IF b THEN c1 ELSE c2) = (skip c1 \<and> skip c2)" |
"skip (WHILE b DO c) = False" 

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
proof (induction c)
  case (Seq c1 c2)
  hence "c1 \<sim> SKIP" and "c2 \<sim> SKIP" by auto
  hence "(c1;;c2) \<sim> (SKIP;;SKIP)" by blast
  thus "(c1;;c2) \<sim> SKIP" by blast
next
  case (If b c1 c2)
  hence "c1 \<sim> SKIP" and "c2 \<sim> SKIP" by auto
  thus "IF b THEN c1 ELSE c2 \<sim> SKIP" by blast    
qed auto+

(* 7.3 *)

fun deskip :: "com \<Rightarrow> com" where
"deskip (c1;;c2) = (case (deskip c1, deskip c2) of
 (SKIP, SKIP) \<Rightarrow> SKIP |
 (SKIP, q) \<Rightarrow> q |
 (p, SKIP) \<Rightarrow> p |
 (p, q) \<Rightarrow> (p;;q))" |
"deskip (WHILE b DO c) = WHILE b DO (deskip c)" |
"deskip (IF b THEN c1 ELSE c2) = IF b THEN (deskip c1) ELSE (deskip c2)" |
"deskip c = c"
 
lemma "deskip c \<sim> c"
proof (induction c)
 case (Seq c1 c2)
 hence "c1;; c2 \<sim> (deskip c1);; (deskip c2)" by auto 
 moreover have "(deskip c1);; (deskip c2) \<sim> deskip (c1;; c2)" 
  by (auto split: com.split)
 ultimately show ?case by auto
qed (auto simp add: sim_while_cong)+

(* 7.4 *)

inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x , s) \<leadsto> N (s x)" |
"(Plus (N i) (N j), s) \<leadsto> N (i + j)"  |
"(p, s) \<leadsto> (N p') \<Longrightarrow> (Plus (N p') q, s) \<leadsto> r \<Longrightarrow> (Plus p q, s) \<leadsto> r" |
"(q, s) \<leadsto> (N q') \<Longrightarrow> (Plus (N i) q, s) \<leadsto> N (i + q')"

code_pred astep .

values "{c' |c'.
   (Plus (Plus (V ''x'') (V ''z'')) (V ''y''),
    <''x'' := 1, ''y'' := 7, ''z'' := 15>) \<leadsto> c'}"

lemmas astep_induct = astep.induct[split_format(complete)]

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
 by (induction rule: astep_induct, auto)

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep_induct)
 fix x s
 show "aval (V x) s = aval (N (s x)) s" by simp
next 
 fix i j s
 show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" by simp
next
 fix p s p' q r
 assume a: "(p, s) \<leadsto> N p'"
 assume b: "aval p s = aval (N p') s"
 assume c: "(Plus (N p') q, s) \<leadsto> r" 
 assume d: "aval (Plus (N p') q) s = aval r s"
 show "aval (Plus p q) s = aval r s" using a b c d by simp
next
 fix q s q' i
 assume a: "(q, s) \<leadsto> N q'"
 assume b: "aval q s = aval (N q') s"
 show "aval (Plus (N i) q) s = aval (N (i + q')) s" using a b by simp
qed

(* 7.5 *)

lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2" (is "?P \<sim> ?Q")
proof -
  { fix s t
    assume "(?P, s) \<Rightarrow> t"
    { assume b: "(bval b1 s) \<and> (bval b2 s)"
      with `(?P, s) \<Rightarrow> t` have "(c1, s) \<Rightarrow> t" by auto
      hence "(?Q, s) \<Rightarrow> t" using b by auto
    }
    moreover
    { assume b: "\<not> ((bval b1 s) \<and> (bval b2 s))"
      hence "\<not> bval (And b1 b2) s" by auto
      with `(?P, s) \<Rightarrow> t` have "(c2, s) \<Rightarrow> t" by auto
      hence "(?Q, s) \<Rightarrow> t" using b by auto
    }
    ultimately have "(?Q, s) \<Rightarrow> t" by auto
  }
  moreover
  { fix s t
    assume "(?Q, s) \<Rightarrow> t"
    { assume b: "(bval b1 s) \<and> (bval b2 s)"
      with `(?Q, s) \<Rightarrow> t` have "(c1, s) \<Rightarrow> t" by auto
      hence "(?P, s) \<Rightarrow> t" using b by auto
    }
    moreover
    { assume b: "\<not> ((bval b1 s) \<and> (bval b2 s))"
      with `(?Q, s) \<Rightarrow> t` have "(c2, s) \<Rightarrow> t" by auto
      from b have "\<not> bval (And b1 b2) s" by auto
      hence "(?P, s) \<Rightarrow> t" using `(c2, s) \<Rightarrow> t` by auto
    }
    ultimately have "(?P, s) \<Rightarrow> t" by auto    
  }
  ultimately show ?thesis by auto
qed

lemma "\<not> (\<forall> b1 b2 c. WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)" (is "\<not> ?P")
proof
  assume "?P"
  then obtain l p t where
   vars: 
    "l = Bc True" 
    "t = Bc False"  
    "p = SKIP"
   and "bval (And l t) s = False" 
   and a: "WHILE And l t DO p \<sim> WHILE l DO WHILE t DO p" by auto
   then have "(WHILE And l t DO p, s) \<Rightarrow> s" by blast  
   with a have "(WHILE l DO WHILE t DO p, s) \<Rightarrow> s" by auto
   thus False 
    by (induction "WHILE l DO WHILE t DO p" s s rule: big_step_induct, auto simp add: vars)
qed    

abbreviation Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
 "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"
 
lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c;; WHILE b1 DO c" (is "?P \<sim> ?P ;; ?Q")
proof -
  { fix b c' s t have "(WHILE b DO c', s) \<Rightarrow> t \<Longrightarrow> \<not> bval b t"
    by (induction "WHILE b DO c'" s t rule: big_step_induct)
  } note while_false = this

  { fix s t assume a: "(?P, s) \<Rightarrow> t"
    with while_false have "\<not> bval (Or b1 b2) t" by blast 
    hence "(?Q, t) \<Rightarrow> t" by auto
    with a have "(?P ;; ?Q, s) \<Rightarrow> t" by auto
  }
  moreover
  { fix s t assume a: "(?P ;; ?Q, s) \<Rightarrow> t"
    then obtain s' where a1: "(?P, s) \<Rightarrow> s'" and a2: "(?Q, s') \<Rightarrow> t" by auto
    with while_false have "\<not> bval (Or b1 b2) s'" by blast
    hence "(?Q, s') \<Rightarrow> s'" by auto
    with a2 big_step_determ have "s' = t" by auto
    with a1 have "(?P, s) \<Rightarrow> t" by auto
  }
  ultimately show ?thesis by blast
qed

(* 7.6 *)

abbreviation DoWhile :: "com \<Rightarrow> bexp \<Rightarrow> com" ("(DO _/ WHILE _)"  [0, 61] 61) where
"DO c WHILE b \<equiv> (c ;; WHILE b DO c)" 

fun dewhile :: "com \<Rightarrow> com" where
"dewhile (WHILE b DO c) = IF b THEN DO (dewhile c) WHILE b ELSE SKIP" | 
"dewhile (c1;; c2) = (dewhile c1);; dewhile c2" |
"dewhile (IF b THEN c1 ELSE c2) = (IF b THEN (dewhile c1) ELSE (dewhile c2))" |
"dewhile c = c"

lemma "dewhile c \<sim> c"
proof (induction c)
  case (While b c)
  hence "WHILE b DO c \<sim> WHILE b DO dewhile c" using sim_while_cong by auto
  moreover have 
   "WHILE b DO dewhile c \<sim> IF b THEN DO (dewhile c) WHILE b ELSE SKIP" using while_unfold by auto
  ultimately have 
   "WHILE b DO c \<sim> IF b THEN DO (dewhile c) WHILE b ELSE SKIP" using sim_trans by blast
  thus ?case by auto
qed auto+

(* 7.7 *)

lemma 
 fixes 
  C :: "nat \<Rightarrow> com" and
  S :: "nat \<Rightarrow> state"
 assumes 
  "C 0 = c;; d" 
  "\<forall> n. (C n, S n) \<rightarrow> (C (Suc n), S (Suc n))" 
 shows 
 "(\<forall> n. \<exists> c1 c2. 
   C n = c1;; d \<and> 
   C (Suc n) = c2;; d \<and> 
   (c1, S n) \<rightarrow> (c2, S (Suc n))) \<or>
 (\<exists> k. C k = SKIP;; d)" (is "?P \<or> ?Q")
proof cases
  assume "?Q"
  thus ?thesis by auto
next 
  assume "\<not> ?Q"
  { fix n c1 assume cn: "C n = c1;; d"
    hence "\<exists> c2. C (Suc n) = c2;; d \<and> (c1, S n) \<rightarrow> (c2, S (Suc n))"
    proof -
      from assms have "(C n, S n) \<rightarrow> (C (Suc n), S (Suc n))" by blast      
      with cn have cc: "(c1;; d, S n) \<rightarrow> (C (Suc n), S (Suc n))" by auto
      then obtain c2 where "C (Suc n) = c2;; d" 
        "(c1, S n) \<rightarrow> (c2, S (Suc n))" using  `\<not> ?Q` cn by blast
      then show ?thesis by auto
    qed
  } note Cn_induction = this

  { fix n 
    have "\<exists>c1 c2. C n = c1;; d \<and> C (Suc n) = c2;; d \<and> (c1, S n) \<rightarrow> (c2, S (Suc n))" 
    proof (induction n)
      case 0
      from assms obtain c1 where c1: "C 0 = c1;; d" by auto
      with Cn_induction obtain c2  where "C (Suc 0) = c2;; d" 
        "(c1, S 0) \<rightarrow> (c2, S (Suc 0))" by blast
      with c1 show ?case by auto
    next
      case (Suc n)
      from this obtain c1 where c1: "C (Suc n) = c1;; d" by blast
      with Cn_induction obtain c2 where "C (Suc (Suc n)) = c2;; d" 
        "(c1, S (Suc n)) \<rightarrow> (c2, S (Suc (Suc n)))" by blast
      with c1 show ?case by auto
    qed
  }
  thus ?thesis by auto
qed
