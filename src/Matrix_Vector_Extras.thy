(* Title: Matrix_Vector_Extras 
   Author: Chelsea Edmonds
*)

theory Matrix_Vector_Extras imports Set_Multiset_Extras Jordan_Normal_Form.Matrix 
Design_Theory.Multisets_Extras "Groebner_Bases.Macaulay_Matrix" "Polynomial_Factorization.Missing_List"
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


lemma vCons_set_contains_in: "a \<in> set\<^sub>v v \<Longrightarrow> set\<^sub>v (vCons a v) = set\<^sub>v v"
  by (metis remdups_mset_singleton_sum set_mset_remdups_mset vec_mset_set vec_mset_vCons)

lemma vCons_set_contains_add: "a \<notin> set\<^sub>v v \<Longrightarrow> set\<^sub>v (vCons a v) = set\<^sub>v v \<union> {a}"
  using vec_mset_set vec_mset_vCons
  by (metis Un_insert_right set_mset_add_mset_insert sup_bot_right) 

lemma setv_vec_mset_not_in_iff: "a \<notin> set\<^sub>v v \<longleftrightarrow> a \<notin># vec_mset v"
  by (simp add: vec_mset_set)

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

lemma setv_not_in_count0_iff: "a \<notin> set\<^sub>v v \<longleftrightarrow> count_vec v a = 0"
  using setv_vec_mset_not_in_iff
  by (metis count_eq_zero_iff) 

lemma sum_count_vec: 
  assumes "finite (set\<^sub>v v)"
  shows "(\<Sum> i \<in> set\<^sub>v v. count_vec v i) = dim_vec v"
using assms proof (induct "v")
  case vNil
  then show ?case
    by (simp add: count_vec_empty) 
next
  case (vCons a v)
  then show ?case proof (cases "a \<in> set\<^sub>v v")
    case True
    have cv: "\<And> x. x \<in>(set\<^sub>v v) - {a} \<Longrightarrow> count_vec (vCons a v) x = count_vec v x" using count_vec_vCons
      by (metis DiffD2 singletonI)
    then have "sum (count_vec (vCons a v)) (set\<^sub>v (vCons a v)) =  sum (count_vec (vCons a v)) (set\<^sub>v v)" using vCons_set_contains_in
      True by metis
    also have "... = count_vec (vCons a v) a + sum (count_vec (vCons a v)) ((set\<^sub>v v) - {a})" using sum.remove True vCons.prems(1)
      by (metis vCons_set_contains_in) 
    also have "... = count_vec v a + 1 + sum (count_vec v) ((set\<^sub>v v) - {a})" using cv count_vec_vCons
      by (metis sum.cong) 
    also have "... = 1 + sum (count_vec v) ((set\<^sub>v v))"
      by (metis (no_types, opaque_lifting) True ab_semigroup_add_class.add_ac(1) add.commute sum.remove vCons.prems vCons_set_contains_in)
    also have "... = 1 + dim_vec v" using vCons.hyps
      by (metis True vCons.prems vCons_set_contains_in) 
    finally show ?thesis by simp
  next
    case False
    then have cv: "\<And> x. x \<in>(set\<^sub>v v) \<Longrightarrow> count_vec (vCons a v) x = count_vec v x" using count_vec_vCons
      by (metis) 
    have f: "finite (set\<^sub>v v)" using vCons.prems False vCons_set_contains_add
      by (metis Un_infinite) 
    have "sum (count_vec (vCons a v)) (set\<^sub>v (vCons a v)) = count_vec (vCons a v) a + sum (count_vec (vCons a v)) (set\<^sub>v v)" 
      using False by (metis Un_insert_right finite_Un sum.insert sup_bot_right vCons.prems vCons_set_contains_add) 
    also have "... = count_vec v a + 1 + sum (count_vec v) ((set\<^sub>v v) )" using cv count_vec_vCons 
      by (metis sum.cong) 
    also have "... = 1 + sum (count_vec v) ((set\<^sub>v v))" using False setv_not_in_count0_iff
      by (metis add_0) 
    also have "... = 1 + dim_vec v" using vCons.hyps f by simp
    finally show ?thesis by simp
  qed
qed

lemma sum_setv_subset_eq: 
  assumes "finite A"
  assumes "set\<^sub>v v \<subseteq> A"
  shows "(\<Sum> i \<in> set\<^sub>v v. count_vec v i) = (\<Sum> i \<in> A. count_vec v i)"
proof -
  have ni: "\<And> x. x \<notin> set\<^sub>v v \<Longrightarrow> count_vec v x = 0"
    by (simp add: setv_not_in_count0_iff) 
  have "(\<Sum> i \<in> A. count_vec v i) = (\<Sum> i \<in> A - (set\<^sub>v v). count_vec v i) + (\<Sum> i \<in> (set\<^sub>v v). count_vec v i)" 
    using sum.subset_diff assms by auto
  then show ?thesis using ni
    by simp 
qed

lemma sum_count_vec_subset: 
  assumes "finite A"
  assumes "set\<^sub>v v \<subseteq> A"
  shows "(\<Sum> i \<in> A. count_vec v i) = dim_vec v"
  using sum_setv_subset_eq sum_count_vec finite_subset assms
  by metis 

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

(* Vector Operations *)

lemma smult_scalar_prod_sum: 
  fixes x :: "'a :: {comm_ring_1}" 
  assumes "vx \<in> carrier_vec n"
  assumes "vy \<in> carrier_vec n"
  shows "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = x * y * (vx \<bullet> vy)"
proof -
  have "\<And> i . i < n \<Longrightarrow> ((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i) = x * y * (vx $ i) * (vy $ i)" using assms  by simp
  then have "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = (\<Sum> i \<in> {0..<n} .x * y * (vx $ i) * (vy $ i))" by simp
  also have "... = x * y * (\<Sum> i \<in> {0..<n} . (vx $ i) * (vy $ i))"
    using sum_distrib_left[of "x * y" "(\<lambda> i. (vx $ i) * (vy $ i))" "{0..<n}"]
    by (metis (no_types, lifting) mult.assoc sum.cong) 
  finally have "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = x * y * (vx \<bullet> vy)" using scalar_prod_def assms
    by (metis carrier_vecD) 
  thus ?thesis by simp
qed

lemma vec_prod_zero: "(0\<^sub>v n) \<bullet> (0\<^sub>v n) = 0"
  by simp

lemma map_vec_compose: "map_vec f (map_vec g v) = map_vec (f \<circ> g) v"
  by auto

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

(* Map Mat *)

lemma row_map_mat[simp]:
  assumes "i < dim_row A" shows "row (map_mat f A) i = map_vec f (row A i)"
  unfolding map_mat_def map_vec_def using assms by auto

lemma map_vec_mat_rows: "map (map_vec f) (rows M) = rows ((map_mat f) M)"
  by (simp add: map_nth_eq_conv) 

lemma map_vec_mat_cols: "map (map_vec f) (cols M) = cols ((map_mat f) M)"
  by (simp add: map_nth_eq_conv)

lemma map_mat_compose: "map_mat f (map_mat g A) = map_mat (f \<circ> g) A"
  by (auto)

lemma map_mat_elements: "elements_mat (map_mat f A) = f ` (elements_mat A)"
proof (auto)
  fix x assume "x \<in> elements_mat (map_mat f A)"
  then obtain i j where "i < dim_row (map_mat f A)" and "j < dim_col (map_mat f A)" and "(map_mat f A) $$ (i, j) = x"
    by auto
  then show "x \<in> f ` elements_mat A" by auto
next
  fix xa assume "xa \<in> elements_mat A" 
  then obtain i j where "i < dim_row A" and "j < dim_col A" and "A $$ (i, j) = xa" by auto
  then show "f xa \<in> elements_mat (map_mat f A)" by auto
qed

section \<open> Vector and Matrix Homomorphism \<close>

(* Vector Homomorphism *)

context semiring_hom
begin

lemma  vec_hom_smult: 
  assumes "dim_vec v2 \<le> dim_vec v1"
  shows "hom (v1 \<bullet> v2) = vec\<^sub>h v1 \<bullet> vec\<^sub>h v2"
  unfolding scalar_prod_def using index_map_vec assms by (auto simp add: hom_distribs)

end

lemma map_vec_vCons: "vCons (f a) (map_vec f v) = map_vec f (vCons a v)"
  by (intro eq_vecI, simp_all add: vec_index_vCons)

context inj_zero_hom
begin

lemma  vec_hom_zero_iff[simp]: "(map_vec hom x = 0\<^sub>v n) = (x = 0\<^sub>v n)"
proof -
  {
    fix i
    assume i: "i < n" "dim_vec x = n"
    hence "map_vec hom x $ i = 0 \<longleftrightarrow> x $ i = 0"
      using index_map_vec(1)[of i x] by simp
  } note main = this
  show ?thesis unfolding vec_eq_iff by (simp, insert main, auto)
qed

lemma  mat_hom_inj: "map_mat hom A = map_mat hom B \<Longrightarrow> A = B"
  unfolding mat_eq_iff by auto

lemma  vec_hom_inj: "map_vec hom v = map_vec hom w \<Longrightarrow> v = w"
  unfolding vec_eq_iff by auto

lemma  vec_hom_set_distinct_iff: 
  fixes xs :: "'a vec list"
  shows "distinct xs \<longleftrightarrow> distinct (map (map_vec hom) xs)"
  using vec_hom_inj by (induct xs) (auto)

lemma vec_hom_mset: "image_mset hom (vec_mset v) = vec_mset (map_vec hom v)"
  apply (induction v)
   apply (metis mset.simps(1) vec_mset_img_map vec_mset_vNil vec_of_list_Nil)
  by (metis mset_vec_eq_mset_list vec_list vec_mset_img_map)

lemma vec_hom_set: "hom ` set\<^sub>v v = set\<^sub>v (map_vec hom v)"
proof (induct v)
  case vNil
  then show ?case by (metis image_mset_empty set_image_mset vec_hom_zero_iff vec_mset_set vec_mset_vNil zero_vec_zero)
next
  case (vCons a v)
  have "hom ` set\<^sub>v (vCons a v) = hom ` ({a} \<union> set\<^sub>v v)"
    by (metis Un_commute insert_absorb insert_is_Un vCons_set_contains_add vCons_set_contains_in) 
  also have "... = {hom a} \<union> (hom ` (set\<^sub>v v))" by simp
  also have "... = {hom a} \<union> (set\<^sub>v (map_vec hom v))" using vCons.hyps by simp
  also have "... = set\<^sub>v (vCons (hom a) (map_vec hom v))"
    by (metis Un_commute insert_absorb insert_is_Un vCons_set_contains_add vCons_set_contains_in) 
  finally show ?case using map_vec_vCons
    by metis 
qed

end

end