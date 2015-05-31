header {* Solutions to Chapter 2 of "Concrete Semantics" *}

theory Chap_two imports Main begin

declare [[names_short]]

(* 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma nSm_Snm[simp]: "add n (Suc m) = add (Suc n) m"
apply (induction n)
apply (auto)
done 

theorem double_add: "add n n = double n"
apply(induction n)
apply(auto)
done

(* 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count y [] = 0" |
"count y (x # xs) = (if x = y then Suc(count y xs) else count y xs)"

lemma count_less: "count y xs \<le> length xs"
apply(induction xs)
apply(auto)
done

(* 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a => 'a list" where
"snoc [] y = [y]" |
"snoc (x # xs) y = x # (snoc xs y)" 

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc[simp]: "reverse (snoc xs y) = y # reverse xs"
apply(induction xs)
apply(auto)
done

lemma reverse_reverse: "reverse (reverse xs) = xs"
apply(induction xs)
apply(auto)
done

(* 2.5 *)

fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = (Suc n) + (sum n)"

lemma sum_is: "sum n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
done

(* 2.6 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l x r) = x # ((contents l) @ (contents r))"

fun treesum :: "nat tree \<Rightarrow> nat" where
"treesum Tip = 0" |
"treesum (Node l x r) = x + (treesum l) + (treesum r)"

theorem listsumcontents_treesum: "listsum (contents t) = treesum t"
apply (induction t)
apply (auto)
done

(* 2.7 *)

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip a) = Tip a" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip x) = [x]" |
"pre_order (Node l x r) = (x # (pre_order l)) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip x) = [x]" |
"post_order (Node l x r) = (post_order l) @ (post_order r) @ [x]"

theorem pre_mirror_rev_post: "pre_order (mirror xs) = rev (post_order xs)"
apply (induction xs)
apply (auto)
done

(* 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a (x # y # xs) = x # a # (intersperse a (y # xs))" |
"intersperse a xs = []"

theorem map_intersperse: "map f (intersperse a l) = intersperse (f a) (map f l)"
apply (induction l rule:intersperse.induct)
apply (auto)
done

(* 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem add_itadd: "itadd m n = add m n"
apply (induction m arbitrary: n)
apply (auto)
done

(* 2.10 *)

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

theorem explode_exponential: "nodes (explode n t) = 2^n * nodes t + 2^n - 1"
apply (induction n arbitrary:t)
apply (auto simp add:algebra_simps)
done

(* 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const k) x = k" |
"eval (Add p q) x = eval p x + eval q x" |
"eval (Mult p q) x = eval p x * eval q x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] y = 0" |
"evalp (x # xs) y = x + y * evalp xs y"

fun vsum :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"vsum [] xs = xs" |
"vsum xs [] = xs" |
"vsum (x # xs) (y # ys) = (x + y) # vsum xs ys"

fun scalar_mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"scalar_mult k [] = []" |
"scalar_mult k (x # xs) = k * x # scalar_mult k xs"

fun vmult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"vmult [] xs = []" |
"vmult (x # xs) ys = vsum (scalar_mult x ys) (0 # vmult xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const k) = [k]" |
"coeffs (Add p q) = vsum (coeffs p) (coeffs q)" |
"coeffs (Mult p q) = vmult (coeffs p) (coeffs q)"

lemma evalp_additive[simp]: "evalp (vsum xs ys) a = evalp xs a + evalp ys a"
apply (induction rule:vsum.induct)
apply (auto simp add:Int.int_distrib)
done

lemma eval_preserves_mult[simp]: "evalp (scalar_mult x ys) a = x * evalp ys a"
apply (induction ys)
apply (auto simp add:Int.int_distrib)
done 

lemma evalp_multiplicative[simp]: "evalp (vmult xs ys) a = evalp xs a * evalp ys a"
apply (induction xs)
apply (auto simp add:Int.int_distrib)
done 

theorem evalp_eval: "evalp (coeffs e) x = eval e x"
apply (induction e)
apply (auto)
done

end
