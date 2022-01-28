(* Title: Matrix_Vector_Extras 
   Author: Chelsea Edmonds
*)

theory Matrix_Vector_Extras imports Set_Multiset_Extras Jordan_Normal_Form.Matrix 
Design_Theory.Multisets_Extras "Groebner_Bases.Macaulay_Matrix"
begin


section \<open>Vector Extras\<close>
text \<open>For ease of use, a number of additions to the existing vector library as initially developed
in the JNF AFP Entry, are given below\<close>

(* Sum Vec *)

definition (in comm_monoid_add) sum_vec :: "'a vec \<Rightarrow> 'a" where
"sum_vec v \<equiv> sum (\<lambda> i . v $ i) {0..<dim_vec v}"

lemma sum_vec_vNil[simp]: "sum_vec vNil = 0"
  by (simp add: sum_vec_def)

lemma sum_vec_vCons: "sum_vec (vCons a v) = a + sum_vec v"
proof -
  have 0: "a = (vCons a v) $ 0"
    by simp 
  have "sum_vec v = sum (\<lambda> i . v $ i) {0..<dim_vec v}" by (simp add: sum_vec_def)
  also have "... = sum (\<lambda> i . (vCons a v) $ Suc i) {0..< dim_vec v}"
    by force
  also have "... = sum (\<lambda> i . (vCons a v) $ i) {Suc 0..< (Suc (dim_vec v))}"
    by (metis sum.shift_bounds_Suc_ivl)  
  finally have sum: "sum_vec v = sum (\<lambda> i . (vCons a v) $ i) {Suc 0..< dim_vec (vCons a v)}" by simp
  have "sum_vec (vCons a v) = sum (\<lambda> i . (vCons a v) $ i){0..< dim_vec (vCons a v)}" by (simp add: sum_vec_def)
  then have "sum_vec (vCons a v) = (vCons a v) $ 0 + sum (\<lambda> i . (vCons a v) $ i){Suc 0..< dim_vec (vCons a v)}"
    by (metis dim_vec_vCons sum.atLeast_Suc_lessThan zero_less_Suc) 
  thus ?thesis using sum 0 by simp
qed

lemma sum_vec_list: "sum_list (list_of_vec v) = sum_vec v"
  by (induct v)(simp_all add: sum_vec_vCons)

lemma sum_vec_mset: "sum_vec v = (\<Sum> x \<in># (mset (list_of_vec v)) . x)"
  by (simp add: sum_vec_list)

lemma dim_vec_vCons_ne_0: "dim_vec (vCons a v) > 0"
  by (cases v) simp_all

lemma sum_vec_vCons_lt: 
  assumes "\<And> i. i < dim_vec (vCons a v) \<Longrightarrow> (vCons a v) $ i \<le> (n ::int)"
  assumes "sum_vec v \<le> m"
  shows "sum_vec (vCons a v) \<le> n + m"
proof -
  have split: "sum_vec (vCons a v) = a + sum_vec v" by (simp add: sum_vec_vCons)
  have a: "(vCons a v) $ 0 = a" by simp
  then have "0 < dim_vec (vCons a v)" using dim_vec_vCons_ne_0 by simp
  then have "a \<le> n" using assms by (metis a) 
  thus ?thesis using split assms
    by (simp add: add_mono) 
qed

lemma sum_vec_one_zero: 
  assumes "\<And> i. i < dim_vec (v :: int vec) \<Longrightarrow> v $ i \<le> (1 ::int)"
  shows "sum_vec v \<le> dim_vec v"
  using assms 
proof (induct v)
  case vNil
  then show ?case by simp
next
  case (vCons a v)
  then have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i \<le> (1 ::int))"
    using vCons.prems by force
  then have lt: "sum_vec v \<le> int (dim_vec v)" by (simp add: vCons.hyps)  
  then show ?case using sum_vec_vCons_lt lt vCons.prems by simp
qed

(* Vec Mset *)

definition vec_mset:: "'a vec \<Rightarrow> 'a multiset" where
"vec_mset v \<equiv> image_mset (vec_index v) (mset_set {..<dim_vec v})"

lemma vec_elem_exists_mset: "(\<exists> i \<in> {..<dim_vec v}. v $ i = x) \<longleftrightarrow> x \<in># vec_mset v"
  by (auto simp add: vec_mset_def)

lemma mset_vec_same_size: "dim_vec v = size (vec_mset v)"
  by (simp add: vec_mset_def)

lemma mset_vec_eq_mset_list: "vec_mset v = mset (list_of_vec v)"
  by (auto simp add: vec_mset_def)
  (metis list_of_vec_map mset_map mset_set_upto_eq_mset_upto)

lemma vec_mset_img_map: "image_mset f (mset (xs)) = vec_mset (map_vec f (vec_of_list xs))"
  by (metis list_vec mset_map mset_vec_eq_mset_list vec_of_list_map)

lemma vec_mset_vNil: "vec_mset vNil = {#}" 
  by (simp add: vec_mset_def)

lemma vec_mset_vCons: "vec_mset (vCons x v) = add_mset x (vec_mset v)"
proof -
  have "vec_mset (vCons x v) = mset (list_of_vec (vCons x v))"
    by (simp add: mset_vec_eq_mset_list)
  then have "mset (list_of_vec (vCons x v)) = add_mset x (mset (list_of_vec v))"
    by simp 
  thus ?thesis
    by (metis mset_vec_eq_mset_list) 
qed

lemma vec_mset_set: "vec_set v = set_mset (vec_mset v)"
  by (simp add: mset_vec_eq_mset_list set_list_of_vec)


(* Count Vec *)

abbreviation "count_vec v a \<equiv> count (vec_mset v) a"

lemma vec_count_lt_dim: "count_vec v a \<le> dim_vec v"
  by (metis mset_vec_same_size order_refl set_count_size_min)

lemma count_vec_empty: "dim_vec v = 0 \<Longrightarrow> count_vec v a = 0"
  by (simp add: mset_vec_same_size)

lemma count_vec_vNil: "count_vec vNil a = 0"
  by (simp add: vec_mset_def)

lemma count_vec_vCons: "count_vec (vCons aa v) a = (if (aa = a) then count_vec v a + 1 else count_vec v a)"
  by(simp add: vec_mset_vCons)

lemma elem_exists_count_min: "\<exists> i \<in>{..<dim_vec v}. v $ i = x \<Longrightarrow> count_vec v x \<ge> 1"
  by (simp add: vec_elem_exists_mset)


lemma count_vec_count_mset:
  assumes "vec_mset v = image_mset f A"
  shows "count_vec v a = count (image_mset f A) a"
  by (simp add: assms)

lemma count_vec_alt_list: "count_vec v a = length (filter (\<lambda>y. a = y) (list_of_vec v))"
proof -
  have "count_vec v a = count (mset (list_of_vec v)) a" by (simp add: mset_vec_eq_mset_list)
  thus ?thesis by (metis count_mset) 
qed

lemma count_vec_alt: "count_vec v x = card { i. v $ i = x \<and> i< dim_vec v}"
proof -
  have "count_vec v x = count (image_mset (($) v) (mset_set {..<dim_vec v})) x" by (simp add: vec_mset_def)
  also have "... = size {#a \<in># (image_mset (($) v) (mset_set {..<dim_vec v})) . x = a#}"
    by (simp add: filter_mset_eq)
  also have "... = size {#a \<in># (mset_set {..<dim_vec v}) . x = (v $ a) #}"
    by (simp add: filter_mset_image_mset)
  finally have "count_vec v x = card {a \<in> {..<dim_vec v} . x = (v $ a)}" by simp
  thus ?thesis by (smt (verit) Collect_cong lessThan_iff) 
qed

lemma count_vec_sum_ones: 
  assumes "\<And> i. i < dim_vec (v :: int vec) \<Longrightarrow> v $ i = 1 \<or> v $ i = 0"
  shows "count_vec v 1 = sum_vec v"
  using assms 
proof (induct v)
  case vNil 
  then show ?case
     by (simp add: vec_mset_vNil)  
 next
  case (vCons a v)
  then have lim: "dim_vec (vCons a v) \<ge> 1"
    by simp 
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v$ i = 0)"
    using vCons.prems by force
  then have hyp: "count_vec v 1 = sum_vec v"
    by (simp add: vCons.hyps) 
  have "sum (($) (vCons a v)) {0..<dim_vec (vCons a v)} = sum_vec (vCons a v)" by (simp add: sum_vec_def)
  then have sv: "sum (($) (vCons a v)) {0..<dim_vec (vCons a v)} = sum_vec (v) + a" by (simp add: sum_vec_vCons)
  then show ?case
    by (metis add.commute add.left_neutral count_vec_vCons dim_vec_vCons_ne_0 hyp of_nat_1 of_nat_add sum_vec_vCons vCons.prems vec_index_vCons_0)
qed

lemma count_vec_two_elems: 
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = (1 ::int) \<or> v $ i = 0"
  shows "count_vec v 1 + count_vec v 0 = dim_vec v"
proof -
  have ss: "vec_set v \<subseteq> {0, 1}" using assms by (auto simp add: vec_set_def)
  have "dim_vec v = size (vec_mset v)"
    by (simp add: mset_vec_same_size) 
  have "size (vec_mset v) = (\<Sum> x \<in> (vec_set v) . count (vec_mset v) x)"
    by (simp add: vec_mset_set size_multiset_overloaded_eq) 
  also have  "... = (\<Sum> x \<in> {0, 1} . count (vec_mset v) x)"
    using size_count_mset_ss ss
    by (metis calculation finite.emptyI finite.insertI vec_mset_set)
  finally have "size (vec_mset v) = count (vec_mset v) 0 + count (vec_mset v) 1" by simp
  thus ?thesis
    by (simp add: \<open>dim_vec v = size (vec_mset v)\<close>) 
qed

lemma count_vec_sum_zeros: 
  assumes "\<And> i. i < dim_vec (v :: int vec) \<Longrightarrow> v $ i = 1 \<or> v $ i = 0"
  shows "count_vec v 0 = dim_vec v - sum_vec v"
  using count_vec_two_elems assms count_vec_sum_ones
  by force 

lemma count_vec_sum_ones_alt: 
  assumes "vec_set v \<subseteq> {0::int, 1}"
  shows "count_vec v 1 = sum_vec v"
proof -
  have "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0" using assms
    by (meson insertE singletonD subsetD vec_setI) 
  thus ?thesis by (simp add: count_vec_sum_ones)
qed

(* Vec contains *)

abbreviation vec_contains :: "'a \<Rightarrow> 'a vec \<Rightarrow> bool" (infix "\<in>$" 50)where 
"a \<in>$ v \<equiv> a \<in> set\<^sub>v v"

lemma vec_set_mset_contains_iff: "a \<in>$ v \<longleftrightarrow> a \<in># vec_mset v"
  by (simp add: vec_mset_def vec_set_def)

lemma vec_contains_count_gt1_iff: "a \<in>$ v \<longleftrightarrow> count_vec v a \<ge> 1"
  by (simp add: vec_set_mset_contains_iff)

lemma vec_contains_obtains_index: 
  assumes "a \<in>$ v"
  obtains i where "i < dim_vec v" and "v $ i = a"
  by (metis assms vec_setE)

lemma vec_count_eq_list_count: "count (mset xs) a = count_vec (vec_of_list xs) a"
  by (simp add: list_vec mset_vec_eq_mset_list) 

lemma vec_contains_col_elements_mat: 
  assumes "j < dim_col M"
  assumes "a \<in>$ col M j"
  shows "a \<in> elements_mat M"
proof -
  have "dim_vec (col M j) = dim_row M" by simp
  then obtain i where ilt: "i < dim_row M" and "(col M j) $ i = a" using vec_setE
    by (metis assms(2))
  then have "M $$ (i, j) = a"
    by (simp add: assms(1)) 
  thus ?thesis using assms(1) ilt
    by blast
qed

lemma vec_contains_row_elements_mat: 
  assumes "i < dim_row M"
  assumes "a \<in>$ row M i"
  shows "a \<in> elements_mat M"
proof -
  have "dim_vec (row M i) = dim_col M" by simp
  then obtain j where jlt: "j < dim_col M" and "(row M i) $ j = a" using vec_setE
    by (metis assms(2))
  then have "M $$ (i, j) = a"
    by (simp add: assms(1)) 
  thus ?thesis using assms(1) jlt
    by blast
qed

(* All ones vector *)

definition all_ones_vec ::  "nat \<Rightarrow> 'a :: {zero,one} vec" ("u\<^sub>v") where
  "u\<^sub>v n \<equiv> vec n (\<lambda> i. 1)"

lemma dim_vec_all_ones[simp]: "dim_vec (u\<^sub>v n) = n"
  by (simp add: all_ones_vec_def)

lemma all_ones_index [simp]: "i < n \<Longrightarrow> u\<^sub>v n $ i = 1"
  by (simp add: all_ones_vec_def)

lemma dim_vec_mult_vec_mat [simp]: "dim_vec (v \<^sub>v* A) = dim_col A"
  unfolding mult_vec_mat_def by simp

lemma all_ones_vec_smult[simp]: "i < n \<Longrightarrow> ((k :: ('a :: {one, zero, monoid_mult})) \<cdot>\<^sub>v (u\<^sub>v n)) $ i = k"
  by (simp add: smult_vec_def)

section \<open>Matrix Extras\<close>

(* All ones Matrix *)

definition all_ones_mat :: "nat \<Rightarrow> 'a :: {zero,one} mat" ("J\<^sub>m") where
  "J\<^sub>m n \<equiv> mat n n (\<lambda> (i,j). 1)"

lemma all_ones_mat_index[simp]: "i < dim_row (J\<^sub>m n) \<Longrightarrow> j < dim_col (J\<^sub>m n) \<Longrightarrow> J\<^sub>m n $$ (i, j)= 1"
  by (simp add: all_ones_mat_def)

lemma all_ones_mat_dim_row[simp]: "dim_row (J\<^sub>m n) = n"
  by (simp add: all_ones_mat_def)

lemma all_ones_mat_dim_col[simp]: "dim_col (J\<^sub>m n) = n"
  by (simp add: all_ones_mat_def)

(* Index mult vec *)
lemma index_mult_vec_mat[simp]: "j < dim_col A \<Longrightarrow> (v \<^sub>v* A) $ j = v \<bullet> col A j"
  by (auto simp: mult_vec_mat_def)

(* Transpose *)
lemma transpose_mat_mult_entries: 
  assumes "i < dim_row A" and "j < dim_row A"
  shows "(A * A\<^sup>T) $$ (i, j) = (\<Sum>k\<in> {0..<(dim_col A)}. (A $$ (i, k)) * (A $$ (j, k)))"
  using assms by (simp add: times_mat_def scalar_prod_def)

lemma transpose_mat_elems: "elements_mat A = elements_mat A\<^sup>T"
  apply (auto simp add: transpose_mat_def)
   apply (metis elements_matD elements_matI index_transpose_mat(1) mat_carrier transpose_mat_def)
  by fastforce

(* Elements Mat *)

lemma row_elems_subset_mat: "i < dim_row N \<Longrightarrow> vec_set (row N i) \<subseteq> elements_mat N"
  by (auto simp add: vec_set_def elements_matI)

lemma col_elems_subset_mat: "i < dim_col N \<Longrightarrow> vec_set (col N i) \<subseteq> elements_mat N"
  by (auto simp add: vec_set_def elements_matI)

end