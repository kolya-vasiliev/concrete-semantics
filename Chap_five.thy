header {* Solutions to Chapter 5 of "Concrete Semantics" *}
  
theory Chap_five imports Main begin

declare [[names_short]]

(* 5.1 *)

lemma assumes T: "\<forall> x y. T x y \<or> T y x"
 and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
 and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
 shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  from this and T have "T y x" by (blast)
  from this and TA have "A y x" by (blast)
  from this and `A x y` and A have "x = y" by (blast)
  from this and `\<not> T x y` and `T y x` show "False" by (blast)
qed

(* 5.2 *)

lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs) \<or>
 (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)" (is "?T \<or> ?S")
proof cases
 assume "2 dvd (length xs)"
 then obtain k where xsk: "(length xs) = 2*k" by (auto simp add: dvd_def) 
 obtain ys where ys:"ys = take k xs" by auto
 obtain zs where zzs:"zs = drop k xs" by auto
 have "length ys = k" using ys and xsk by auto
 then have "xs = ys @ zs" using ys and zzs by (metis append_eq_conv_conj)
 moreover have "length ys = length zs" using zzs and ys and xsk by auto
 ultimately show ?thesis by auto
next 
 assume "\<not> 2 dvd (length xs)"
 hence "\<exists> k. length xs = 2 * k + 1" by arith
 then obtain k where xsk: "length xs = 2 * k + 1" by blast
 obtain ys where yys:"ys = take (Suc k) xs" by auto
 obtain zs where zzs:"zs = drop (Suc k) xs" by auto
 have "length ys = Suc k" using yys and xsk by auto 
 hence "xs = ys @ zs" using yys and zzs by (metis append_eq_conv_conj)
 moreover have "length ys = length zs + 1" using zzs and yys and xsk by auto
 ultimately show ?thesis by auto   
qed

(* 5.3 *)

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

lemma assumes a: "ev (Suc (Suc n))" shows "ev n"
proof -
 show ?thesis using a
 proof cases
  case evSS
  thus ?thesis by auto
 qed
qed

(* 5.4 *)

lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not> ?P")
proof 
 assume "?P"
 hence "ev (Suc 0)" by cases
 thus False by cases 
qed

(* 5.5 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>  bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z  \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
it0: "iter r 0 x x" |
it_SS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
 case it0
 show ?case by (rule star.refl)
next 
 case it_SS
 thus ?case by (auto intro: star.step)
qed

(* 4.6 *)

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (a # xs) = {a} \<union> elems xs"

lemma fixes x :: 'a shows "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
 case Nil
 thus ?case by auto
next
 case (Cons a xs) 
 show ?case 
 proof cases
  assume "a = x"
  obtain ys where ys: "(ys :: 'a list) = []" by auto
  obtain zs where zs: "zs = xs" by auto
  have "a \<notin> elems ys" using ys by auto 
  thus ?thesis using ys zs `a = x` by blast
 next
  assume "a \<noteq> x"
  hence "x \<in> elems xs" using Cons.prems by auto
  then obtain old_ys ys zs where 
   "ys = a # old_ys" "xs = old_ys @ x # zs \<and> x \<notin> elems old_ys" using Cons.IH by auto
  hence "a # xs = ys @ x # zs \<and> x \<notin> elems ys" using `a \<noteq> x` by auto
  thus ?thesis by auto
 qed
qed
