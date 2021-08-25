theory Incidence_Matrices imports BIBD Jordan_Normal_Form.Matrix "List-Index.List_Index"
"HOL-Library.Multiset_Permutations"
begin


(* Extra design theories *)
lemma (in incidence_system) block_size_alt:
  assumes "bl \<in># \<B>"
  shows "card bl = card {x \<in> \<V> . x \<in> bl}" 
proof -
  have "\<And> x. x \<in> bl \<Longrightarrow> x \<in> \<V>" using wellformed assms by auto
  thus ?thesis
    by (metis (no_types, lifting) Collect_cong Collect_mem_eq) 
qed

lemma (in incidence_system) complement_image: "\<B>\<^sup>C = image_mset block_complement \<B>"
  by (simp add: complement_blocks_def)

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
  then have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i \<le> 1)"
    using vCons.prems by force
  then have lt: "sum_vec v \<le> int (dim_vec v)" by (simp add: vCons.hyps)  
  then show ?case using sum_vec_vCons_lt lt vCons.prems by auto 
qed

lemma eq_count: "A = B \<Longrightarrow> count A x = count B x"
  by simp


definition vec_mset:: "'a vec \<Rightarrow> 'a multiset" where
"vec_mset v \<equiv> image_mset (vec_index v) (mset_set {..<dim_vec v})"

lemma vec_elem_exists_mset: "(\<exists> i \<in> {..<dim_vec v}. v $ i = x) \<longleftrightarrow> x \<in># vec_mset v"
  by (auto simp add: vec_mset_def)

lemma mset_vec_same_size: "dim_vec v = size (vec_mset v)"
  by (simp add: vec_mset_def)

lemma mset_vec_eq_mset_list: "vec_mset v = mset (list_of_vec v)"
  apply (auto simp add: vec_mset_def)
  by (metis list_of_vec_map mset_map mset_set_upto_eq_mset_upto)

lemma vec_mset_img_map: "image_mset f (mset (xs)) = vec_mset (map_vec f (vec_of_list xs))"
  by (metis list_vec mset_map mset_vec_eq_mset_list vec_of_list_map)

abbreviation "count_vec v a \<equiv> count (vec_mset v) a"

lemma vec_count_lt_dim: "count_vec v a \<le> dim_vec v"
  by (metis mset_vec_same_size order_refl set_count_size_min)

lemma elem_exists_count_min: "\<exists> i \<in>{..<dim_vec v}. v $ i = x \<Longrightarrow> count_vec v x \<ge> 1"
  by (simp add: vec_elem_exists_mset)

lemma mset_list_by_index: "mset (xs) = image_mset (\<lambda> i . (xs ! i)) (mset_set {..<length xs})"
  by (metis dim_vec_of_list image_mset_cong list_vec mset_vec_eq_mset_list vec_mset_def vec_of_list_index)

lemma count_vec_count_mset:
  assumes "vec_mset v = image_mset f A"
  shows "count_vec v a = count (image_mset f A) a"
  by (simp add: assms)

lemma count_mset_split_image_filter: 
  assumes "\<And> x. x \<in>#A \<Longrightarrow> a \<noteq> g x"
  shows "count (image_mset (\<lambda>x. if P x then a else g x) A ) a = size (filter_mset P A)"
using image_mset_If by (smt (verit) assms count_size_set_repr filter_mset_cong image_mset_filter_swap size_image_mset) 

lemma count_mset_split_image_filter_not: 
  assumes "\<And> x. x \<in>#A \<Longrightarrow> b \<noteq> f x"
  shows "count (image_mset (\<lambda>x. if P x then f x else b) A ) b = size (filter_mset (\<lambda> x. \<not> P x) A)"
  using image_mset_If by (smt (verit) assms count_size_set_repr filter_mset_cong image_mset_filter_swap size_image_mset) 

abbreviation vec_contains :: "'a \<Rightarrow> 'a vec \<Rightarrow> bool" (infix "\<in>$" 50)where 
"a \<in>$ v \<equiv> a \<in> set\<^sub>v v"

lemma vec_set_mset_contains_iff: "a \<in>$ v \<longleftrightarrow> a \<in># vec_mset v"
  by (simp add: vec_mset_def vec_set_def)

lemma vec_contains_count_gt1_iff: "a \<in>$ v \<longleftrightarrow> count_vec v a \<ge> 1"
  by (simp add: vec_set_mset_contains_iff) 

lemma vec_count_eq_list_count: "count (mset xs) a = count_vec (vec_of_list xs) a"
  by (simp add: list_vec mset_vec_eq_mset_list) 

(* Permutations of Sets Extras *)

lemma elem_permutation_of_set_empty_iff: "finite A \<Longrightarrow> xs \<in> permutations_of_set A \<Longrightarrow> 
    xs = [] \<longleftrightarrow> A = {}"
  using permutations_of_setD(1) by fastforce

lemma elem_permutation_of_mset_empty_iff: "xs \<in> permutations_of_multiset A \<Longrightarrow> xs = [] \<longleftrightarrow> A = {#}"
  using permutations_of_multisetD by fastforce

context finite_incidence_system
begin

definition indexes:: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"indexes f \<equiv> bij_betw f {0..< \<v>} \<V>"

end

locale incidence_matrix = 
  fixes matrix :: "'b :: {zero_neq_one} mat" ("N")
  and index_map :: "nat \<Rightarrow> 'a" ("\<rightarrow>\<^sub>i")
  assumes elems01: "elements_mat N \<subseteq> {0 :: 'b, 1}"
    and index_map_inj: "inj_on index_map {0..<dim_row N}"
begin

definition map_to_points:: "'a set" where
"map_to_points \<equiv> \<rightarrow>\<^sub>i ` {0..<dim_row N}"

definition map_col_to_block :: "'b :: {zero_neq_one} vec  \<Rightarrow> 'a set" where
"map_col_to_block c \<equiv> \<rightarrow>\<^sub>i ` { i \<in> {..<dim_vec c} . c $ i = 1}"

definition map_to_blocks :: "'a set multiset" where
"map_to_blocks \<equiv> {# map_col_to_block (col N j). j \<in># mset_set {0..<(dim_col N)} #}"

lemma map_to_blocks_alt: "map_to_blocks \<equiv> {# map_col_to_block c. c \<in># mset (cols N) #}"
  by (simp add: cols_def map_to_blocks_def)

definition map_to_points_ordered:: "'a list" where 
"map_to_points_ordered \<equiv>  map (\<lambda> x . \<rightarrow>\<^sub>i x) [0..<dim_row N]"

definition map_to_blocks_ordered:: "'a set list" where
"map_to_blocks_ordered \<equiv> map (\<lambda> c . map_col_to_block c) (cols N)"

lemma map_to_points_ordered_set: "set (map_to_points_ordered) = map_to_points"
  by (simp add: map_to_points_ordered_def map_to_points_def)

lemma map_to_blocks_ordered_set: "mset (map_to_blocks_ordered) = map_to_blocks"
  by (simp add: map_to_blocks_ordered_def map_to_blocks_alt)

lemma map_to_points_ordered_distinct: "distinct map_to_points_ordered"
  using distinct_map index_map_inj
  by (metis atLeastLessThan_upt distinct_upt map_to_points_ordered_def) 

end

locale indexed_incidence_system = finite_incidence_system + 
  fixes \<V>s :: "'a list" and \<B>s :: "'a set list"
  assumes points_indexing: "\<V>s \<in> permutations_of_set \<V>"
  assumes blocks_indexing: "\<B>s \<in> permutations_of_multiset \<B>"
begin 

definition N :: "'b :: {zero_neq_one} mat" where
"N \<equiv> mat \<v> \<b> (\<lambda> (i,j) . if (\<V>s ! i) \<in> (\<B>s ! j) then 1 else 0)"

lemma N_carrier_mat: "N \<in> carrier_mat \<v> \<b>" 
  by (simp add: N_def)

lemma points_list_empty_iff: "\<V>s = [] \<longleftrightarrow> \<V> = {}"
  using finite_sets points_indexing
  by (simp add: elem_permutation_of_set_empty_iff) 

lemma distinct_points_index: "distinct \<V>s"
  using permutations_of_setD(2) points_indexing by auto

lemma points_indexing_inj: "\<forall> i \<in> I . i < length \<V>s \<Longrightarrow> inj_on ((!) \<V>s) I"
  by (simp add: distinct_points_index inj_on_nth)

lemma blocks_list_empty_iff: "\<B>s = [] \<longleftrightarrow> \<B> = {#}"
  using blocks_indexing
  by (simp add: elem_permutation_of_mset_empty_iff) 

lemma blocks_list_nempty: "proper_design \<V> \<B> \<Longrightarrow> \<B>s \<noteq> []"
  by (simp add: proper_design.design_blocks_nempty blocks_list_empty_iff)

lemma points_list_nempty: "proper_design \<V> \<B> \<Longrightarrow> \<V>s \<noteq> []"
  by (simp add: proper_design.design_points_nempty points_list_empty_iff)

lemma points_list_length: "length \<V>s = \<v>"
  using points_indexing
  by (simp add: length_finite_permutations_of_set) 

lemma blocks_list_length: "length \<B>s = \<b>"
  using blocks_indexing by (simp add: length_finite_permutations_of_multiset)

lemma points_set_list: "\<V> = set (\<V>s)"
  using points_indexing by (simp add: permutations_of_set_def)

lemma blocks_mset_list: "\<B> = mset (\<B>s)"
  using blocks_indexing by (simp add: permutations_of_multiset_def)

lemma valid_points_index: "i < \<v> \<Longrightarrow> \<V>s ! i \<in> \<V>"
  using points_list_length by (auto simp add: points_set_list)

lemma valid_points_index_cons: "x \<in> \<V> \<Longrightarrow> \<exists> i. \<V>s ! i = x \<and> i < \<v>"
  apply (simp add: points_set_list in_set_conv_nth)
  using points_list_length points_set_list by auto

lemma valid_blocks_index: "j < \<b> \<Longrightarrow> \<B>s ! j \<in># \<B>"
  using blocks_list_length blocks_mset_list
  by (metis nth_mem_mset)

lemma valid_blocks_index_cons: "bl \<in># \<B> \<Longrightarrow> \<exists> j . \<B>s ! j = bl \<and> j < \<b>"
  by (auto simp add: blocks_mset_list in_set_conv_nth)

lemma points_set_image: "\<V> = image(\<lambda> i . (\<V>s ! i)) ({..<\<v>})"
  using valid_points_index_cons valid_points_index by auto

lemma blocks_mset_image: "\<B> = image_mset (\<lambda> i . (\<B>s ! i)) (mset_set {..<\<b>})"
  using blocks_mset_list by (simp add: mset_list_by_index)

(* Basic Incidence Matrix lemmas *)
lemma matrix_one_zero_elems: "elements_mat N \<subseteq> {0 :: ('b :: {zero_neq_one}), 1}"
  by (auto simp add: N_def elements_mat_def)

lemma fin_incidence_mat_elems: "finite (elements_mat N)"
  using finite_subset matrix_one_zero_elems by auto 

lemma matrix_elems_max_two: "card (elements_mat N) \<le> 2"
proof -
  have "card {0 :: ('b :: {zero_neq_one}), 1} = 2"
    by auto  
  thus ?thesis using card_mono matrix_one_zero_elems
    by (metis finite.emptyI finite.insertI) 
qed

lemma dim_row_is_v: "dim_row N = \<v>"
  by (simp add: N_def)

lemma dim_vec_row: "dim_vec (row N i) = \<b>"
  by (simp add: N_def)

lemma dim_col_is_b: "dim_col N = \<b>"
  by (simp add: N_def)

lemma dim_col_b_lt_iff: "j < \<b> \<longleftrightarrow> j < dim_col N"
  by (simp add: dim_col_is_b)

lemma dim_row_v_lt_iff: "i < \<v> \<longleftrightarrow> i < dim_row N"
  by (simp add: dim_row_is_v)

lemma dim_vec_col: "dim_vec (col N i) = \<v>"
  by (simp add: N_def)

lemma matrix_point_in_block_one:
  assumes "i < \<v>"
  assumes "j < \<b>"
  assumes "\<V>s ! i \<in> \<B>s ! j"
  shows  "N $$ (i, j) = 1"
  by (simp add: assms N_def)   

lemma matrix_point_not_in_block_zero: 
  assumes "i < \<v>"
  assumes "j < \<b>"
  assumes "\<V>s ! i \<notin> \<B>s ! j"
  shows "N $$ (i, j) = 0"
  by(simp add: assms N_def)

lemma matrix_point_in_block:
  assumes "i < \<v>"
  assumes "j < \<b>"
  assumes "N $$ (i, j) = 1"
  shows "\<V>s ! i \<in> \<B>s ! j"
proof (rule ccontr)
  assume a: " \<V>s ! i \<notin> \<B>s ! j"
  have "N$$ (i, j) =  (if (\<V>s ! i) \<in> (\<B>s ! j) then 1 else 0)" using N_def assms
    using matrix_point_in_block_one matrix_point_not_in_block_zero by auto
  then have "N$$ (i, j) = 0" using a by simp
  thus False using assms(3)
    by (smt (verit, del_insts) zero_neq_one) 
qed

lemma matrix_point_not_in_block: 
  assumes "i < \<v>"
  assumes "j < \<b>"
  assumes "N $$ (i, j) = 0"
  shows "\<V>s ! i \<notin> \<B>s ! j"
proof (rule ccontr)
  assume a: "\<not> \<V>s ! i \<notin> \<B>s ! j"
  have "N$$ (i, j) =  (if (\<V>s ! i) \<in> (\<B>s ! j) then 1 else 0)" using N_def assms
    using matrix_point_in_block_one matrix_point_not_in_block_zero by auto
  then have "N$$ (i, j) = 1" using a by simp
  thus False using assms(3) by (smt (verit, del_insts) zero_neq_one) 
qed

lemma matrix_point_not_in_block_iff: 
  assumes "i < \<v>"
  assumes "j < \<b>"
  shows "N $$ (i, j) = 0 \<longleftrightarrow> \<V>s ! i \<notin> \<B>s ! j"
  using assms matrix_point_not_in_block matrix_point_not_in_block_zero by blast

lemma matrix_point_in_block_iff: 
  assumes "i < \<v>"
  assumes "j < \<b>"
  shows "N $$ (i, j) = 1 \<longleftrightarrow> \<V>s ! i \<in> \<B>s ! j"
  using assms matrix_point_in_block matrix_point_in_block_one by blast

lemma matrix_subset_implies_one: 
  assumes "I \<subseteq> {..< \<v>}"
  assumes "j < \<b>"
  assumes "(!) \<V>s ` I \<subseteq> \<B>s ! j"
  assumes "i \<in> I"
  shows "N $$ (i, j) = 1"
proof - 
  have iin: "\<V>s ! i \<in> \<B>s ! j" using assms by auto
  have "i < \<v>" using assms by auto
  thus ?thesis using iin matrix_point_in_block_iff assms(2) by blast  
qed

lemma matrix_one_implies_membership: 
"I \<subseteq> {..< \<v>} \<Longrightarrow> j < size \<B> \<Longrightarrow> \<forall>i\<in>I. N $$ (i, j) = 1 \<Longrightarrow> i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
  using matrix_point_in_block by auto

sublocale inc_matrix: incidence_matrix N "\<lambda> i . \<V>s ! i"
  using matrix_one_zero_elems distinct_points_index 
  by (unfold_locales) (simp_all add: inj_on_nth dim_row_is_v points_list_length)

(* Start of lemmas to prove basic properties *)

lemma N_col_def: 
  assumes "j < \<b>"
  assumes "i < \<v>"
  shows "(col N j) $ i = (if (\<V>s ! i \<in> \<B>s ! j) then 1 else 0)"
  using assms by (simp add: N_def) 

lemma N_col_list_map_elem: 
  assumes "j < \<b>"
  assumes "i < \<v>"
  shows "col N j $ i = map_vec (\<lambda> x . if (x \<in> (\<B>s ! j)) then 1 else 0) (vec_of_list \<V>s) $ i"
  apply (simp add: N_def)
  by (simp add: assms index_vec_of_list points_list_length)

lemma N_col_list_map: 
  assumes "j < \<b>"
  shows "col N j = map_vec (\<lambda> x . if (x \<in> (\<B>s ! j)) then 1 else 0) (vec_of_list \<V>s)"
  apply (intro eq_vecI)
    using N_col_list_map_elem assms points_list_length apply fastforce
  using dim_row_is_v points_list_length by fastforce 

lemma N_col_mset_point_set_img: 
  assumes "j < \<b>"
  shows "vec_mset (col N j) = image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else 0) (mset_set \<V>)"
  using vec_mset_img_map N_col_list_map
  by (metis (no_types, lifting) assms finite_sets image_mset_cong2 permutations_of_multisetD permutations_of_set_altdef points_indexing) 


lemma matrix_col_to_block: 
  assumes "j < \<b>"
  shows "\<B>s ! j = (!) \<V>s ` {i \<in> {..< \<v>} . (col N j) $ i = 1}"
proof (intro subset_antisym subsetI)
  fix x assume assm1: "x \<in> \<B>s ! j"
  then have "x \<in> \<V>" using wellformed assms valid_blocks_index by blast 
  then obtain i where vs: "\<V>s ! i = x" and "i < \<v>"
    using valid_points_index_cons by auto 
  then have inset: "i \<in> {..< \<v>}"
    by fastforce
  then have "col N j $ i = 1" using assm1
    by (simp add: N_col_def assms vs)
  then have "i \<in> {i. i \<in> {..< \<v>} \<and> col N j $ i = 1}"
    using inset by blast
  then show "x \<in> (!) \<V>s ` {i.  i \<in> {..<\<v>} \<and> col N j $ i = 1}" using vs by blast
next
  fix x assume assm2: "x \<in> (!) \<V>s ` {i \<in> {..< \<v>} . col N j $ i = 1}"
  then have  "\<exists> i . i \<in>{i \<in> {..< \<v>} . col N j $ i = 1} \<and> \<V>s ! i = x" 
    sorry 
  then obtain i where "\<V>s ! i = x" and inner: "i \<in>{i.  i \<in> {..<\<v>} \<and> col N j $ i = 1}" by auto
  then have ilt: "i < \<v>" by auto
  then have "N $$ (i, j) = 1" using inner
    by (metis (mono_tags) N_col_def assms matrix_point_in_block_iff matrix_point_not_in_block_zero mem_Collect_eq) 
  then show "x \<in> \<B>s ! j" using ilt
    using \<open>\<V>s ! i = x\<close> assms matrix_point_in_block_iff by blast
qed

lemma matrix_col_in_blocks: 
  assumes "j < \<b>"
  shows "(!) \<V>s ` {i. i < dim_vec (col N j) \<and> (col N j) $ i = 1} \<in># \<B>"
  using matrix_col_to_block
  by (metis (no_types, lifting) Collect_cong assms dim_col dim_row_is_v lessThan_iff valid_blocks_index) 

lemma N_row_def: 
  assumes "j < \<b>"
  assumes "i < \<v>"
  shows "(row N i) $ j = (if (\<V>s ! i \<in> \<B>s ! j) then 1 else 0)"
  using assms by (simp add: N_def)

lemma N_row_list_map_elem: 
  assumes "j < \<b>"
  assumes "i < \<v>"
  shows "row N i $ j = map_vec (\<lambda> bl . if ((\<V>s ! i) \<in> bl) then 1 else 0) (vec_of_list \<B>s) $ j"
  apply (simp add: N_def)
  by (simp add: assms(1) assms(2) blocks_list_length vec_of_list_index)

lemma N_row_list_map: 
  assumes "i < \<v>"
  shows "row N i = map_vec (\<lambda> bl . if ((\<V>s ! i) \<in> bl) then 1 else 0) (vec_of_list \<B>s)"
  apply (intro eq_vecI)
  using N_row_list_map_elem assms blocks_list_length apply fastforce
  using dim_col_is_b blocks_list_length by fastforce 

lemma N_row_mset_blocks_img: 
  assumes "i < \<v>"
  shows "vec_mset (row N i) = image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else 0) \<B>"
  using vec_mset_img_map N_row_list_map by (metis assms blocks_mset_list) 

lemma incomplete_block_col:
  assumes "j < \<b>"
  assumes "incomplete_block (\<B>s ! j)"
  shows "0 \<in>$ (col N j)" 
proof -
  obtain x where "x \<in> \<V>" and "x \<notin> (\<B>s ! j)"
    by (metis Diff_iff assms(2) incomplete_block_proper_subset psubset_imp_ex_mem)
  then obtain i where "\<V>s ! i = x" and "i< \<v>" 
    using valid_points_index_cons by blast 
  then have "N $$ (i, j) = 0"
    using \<open>x \<notin> \<B>s ! j\<close> assms(1) matrix_point_not_in_block_zero by blast 
  then have "col N j $ i = 0"
    using N_col_def \<open>\<V>s ! i = x\<close> \<open>i < \<v>\<close> \<open>x \<notin> \<B>s ! j\<close> assms(1) by fastforce 
  thus ?thesis using vec_setI
    by (smt (z3) \<open>i < \<v>\<close> dim_col dim_row_is_v)
qed

lemma point_rep_mat_row: 
  assumes "i < \<v>"
  shows "count_vec (row N i) 1 = \<B> rep (\<V>s ! i)"
proof -
  have 1: "vec_mset (row N i) = image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else 0) \<B>"
    using N_row_mset_blocks_img assms by auto 
  have "\<And>bl. bl \<in># \<B> \<Longrightarrow> (\<lambda>x .(0 :: 'b)) bl \<noteq> 1" using zero_neq_one
    by simp 
  then have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: 'b )) \<B>) 1 = 
    size (filter_mset (\<lambda> x . (\<V>s ! i) \<in> x) \<B>)"
    using count_mset_split_image_filter[of "\<B>" "1" "\<lambda> x . (0 :: 'b)" "\<lambda> x . (\<V>s ! i) \<in> x"] by simp
  then have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: 'b )) \<B>) 1
    = \<B> rep (\<V>s ! i)" by (simp add: point_rep_number_alt_def)
  thus ?thesis
    by (simp add: "1") 
qed

lemma block_size_mat_rep: 
  assumes "j < \<b>"
  shows "count_vec (col N j) 1 = card (\<B>s ! j)"
proof -
  have 1: "vec_mset (col N j) = image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else 0) (mset_set \<V>)"
    using N_col_mset_point_set_img assms by auto
  have val_b: "\<B>s ! j \<in># \<B>" using assms valid_blocks_index by auto 
  have "\<And> x. x \<in># mset_set \<V> \<Longrightarrow> (\<lambda>x . (0 :: 'b)) x \<noteq> 1" using zero_neq_one by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: 'b)) (mset_set \<V>)) 1 = 
    size (filter_mset (\<lambda> x . x \<in> (\<B>s ! j)) (mset_set \<V>))"
    using count_mset_split_image_filter [of "mset_set \<V>" "1" "(\<lambda> x . (0 :: 'b))" "\<lambda> x . x \<in> \<B>s ! j"] by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: 'b)) (mset_set \<V>)) 1 = card (\<B>s ! j)"
    using val_b block_size_alt by (simp add: finite_sets)
  thus ?thesis by (simp add: 1)
qed

lemma mset_image_eq_filter_eq: "A = image_mset f B \<Longrightarrow> 
  filter_mset P A = (image_mset f (filter_mset (\<lambda> x. P (f x)) B))"
  by (simp add: filter_mset_image_mset)

lemma filter_size_blocks_eq_card_indexes: 
"size {# b \<in># \<B> . P b #} = card {j \<in> {..<(\<b>)}. P (\<B>s ! j)}"
proof -
  have "\<B> = image_mset (\<lambda> j . \<B>s ! j) (mset_set {..<(\<b>)})" using blocks_mset_image by simp
  then have "filter_mset P \<B> = filter_mset P (image_mset (\<lambda> j . \<B>s ! j) (mset_set {..< \<b>}))" by simp
  then have helper: "{# b \<in># \<B> . P b #} = image_mset (\<lambda> j . \<B>s ! j) {# j \<in># (mset_set {..< \<b>}). P (\<B>s ! j) #} "
    by (simp add: filter_mset_image_mset)
  have "card {j \<in> {..<\<b>}. P (\<B>s ! j)} = size {# j \<in># (mset_set {..< \<b>}). P (\<B>s ! j) #}"
    using card_size_filter_eq [of "{..<\<b>}"] by simp
  thus ?thesis using helper by simp
qed

lemma points_index_mat_rep:
  assumes "I \<subseteq> {..<\<v>}"
  shows "card {j \<in> {0..<\<b>} . (\<forall> i \<in> I . N $$(i, j) = 1)} = points_index \<B> ((\<lambda> i. \<V>s ! i) ` I)"
proof - 
  have "\<And> i . i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>" using assms valid_points_index by auto 
  then have eqP: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> ((\<lambda> i. \<V>s ! i) ` I) \<subseteq> (\<B>s ! j) \<longleftrightarrow> (\<forall> i \<in> I . N $$ (i, j) = 1)"
  proof (auto)
    show "\<And>j i. j < size \<B> \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>) \<Longrightarrow> (!) \<V>s ` I \<subseteq> \<B>s ! j \<Longrightarrow> i \<in> I \<Longrightarrow> N $$ (i, j) = 1"
      using matrix_subset_implies_one assms by simp
    show "\<And>j i. j < size \<B> \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>) \<Longrightarrow> \<forall>i\<in>I. N $$ (i, j) = 1 \<Longrightarrow> i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
      using assms matrix_one_implies_membership by blast 
  qed
  have "card {j \<in> {0..<\<b>} . (\<forall> i \<in> I . N $$(i, j) = 1)} = card { j \<in> {0..<\<b>}. ((\<lambda> i . \<V>s ! i) ` I) \<subseteq> \<B>s ! j}"
    using eqP by (metis (mono_tags, lifting))
  also have "... = size {# b \<in># \<B> . ((\<lambda> i . \<V>s ! i) ` I) \<subseteq> b #}"
    using filter_size_blocks_eq_card_indexes by auto
  also have "... = points_index \<B> ((\<lambda> i . \<V>s ! i) ` I)"
    by (simp add: points_index_def)
  finally have "card {j \<in> {0..<\<b>} . (\<forall> i \<in> I . N $$(i, j) = 1)} = points_index \<B> ((\<lambda> i . \<V>s ! i) ` I)"
    by blast
  thus ?thesis by simp
qed

lemma inc_matrix_points: "inc_matrix.map_to_points inc_matrix = \<V>"
  apply (simp add: inc_matrix.map_to_points_def)
  by (metis dim_row_is_v lessThan_atLeast0 points_set_image)

lemma inc_matrix_col_block: assumes "c \<in> set (cols N)"
  shows "inc_matrix.map_col_to_block c \<in># \<B>"
proof (simp add: inc_matrix.map_col_to_block_def)
  obtain j where "c = col N j" and "j < \<b>" using assms
    by (metis cols_length cols_nth in_mset_conv_nth indexed_incidence_system.dim_col_b_lt_iff indexed_incidence_system_axioms set_mset_mset) 
  thus "(!) \<V>s ` {i. i < dim_vec c \<and> c $ i = 1} \<in># \<B> "
    using matrix_col_in_blocks by blast 
qed

lemma inc_matrix_blocks: "inc_matrix.map_to_blocks inc_matrix = \<B>"
proof (simp add: inc_matrix.map_to_blocks_def inc_matrix.map_col_to_block_def)
  have test: "\<And> j . j < size \<B> \<Longrightarrow> \<B>s ! j = ((!) \<V>s ` {i \<in> {..< \<v>} . (col N j) $ i = 1})" using matrix_col_to_block by simp
  have "image_mset (\<lambda> j . (\<B>s ! j)) (mset_set {..<size \<B>}) = \<B>"
    using blocks_mset_image by auto 
  then have "image_mset (\<lambda> j . ((!) \<V>s ` {i \<in> {..< \<v>} . (col N j) $ i = 1})) (mset_set {..<size \<B>}) = \<B>" using test
    by (metis (mono_tags, lifting) count_greater_zero_iff count_mset_set(3) lessThan_iff multiset.map_cong not_gr0) 
  then have "image_mset (\<lambda> j . ((!) \<V>s ` {i \<in> {..< \<v>} . (col N j) $ i = 1})) (mset_set {0..<dim_col N}) = \<B>"
    by (smt (verit, best) N_carrier_mat carrier_matD(2) lessThan_atLeast0 nat_int)
  then have "image_mset (\<lambda> j . ((!) \<V>s ` {i. i < dim_row N \<and> (col N j) $ i = 1})) (mset_set {0..<dim_col N}) = \<B>" 
    by (simp add: dim_row_is_v)
  then have "{# ((!) \<V>s ` {i. i < dim_row N \<and> (col N j) $ i = 1}) . j \<in># (mset_set {0..<dim_col N})#} = \<B>"
    by blast  
  then show "{#(!) \<V>s ` {i. i < dim_row N \<and> col N x $ i = 1}. x \<in># mset_set {0..<dim_col N}#} = \<B>" 
    by auto
qed

(* Complement is flipped matrix *)

lemma map_block_complement_entry: "j < \<b> \<Longrightarrow> (map block_complement \<B>s) ! j = (\<B>s ! j)\<^sup>c"
  by (simp add: blocks_list_length)

lemma complement_mat_entries: 
  assumes "i < \<v>" and "j < \<b>"
  shows "(\<V>s ! i \<notin> \<B>s ! j) \<longleftrightarrow> (\<V>s ! i \<in> (map block_complement \<B>s) ! j)"
  using assms block_complement_def map_block_complement_entry valid_points_index by simp

lemma indexed_complement: "indexed_incidence_system \<V> \<B>\<^sup>C \<V>s (map block_complement \<B>s)"
proof -
  interpret inc: finite_incidence_system \<V> "\<B>\<^sup>C"
    by (simp add: complement_finite)
  show ?thesis proof (unfold_locales)
    show "\<V>s \<in> permutations_of_set \<V>" by (simp add: points_indexing)
    show "map inc.block_complement \<B>s \<in> permutations_of_multiset \<B>\<^sup>C"
      using complement_image blocks_mset_list by (simp add: permutations_of_multiset_def)
  qed
qed

interpretation indexed_comp: indexed_incidence_system "\<V>" "\<B>\<^sup>C" "\<V>s" "(map block_complement \<B>s)"
  using indexed_complement by simp

lemma indexed_complement_mat: "indexed_comp.N = mat \<v> \<b> (\<lambda> (i,j) . if (\<V>s ! i) \<in> (\<B>s ! j) then 0 else 1)"
proof (intro eq_matI)
  have "\<And>i j. i < \<v> \<Longrightarrow>j < \<b> \<Longrightarrow> (\<V>s ! i \<notin> \<B>s ! j) \<longleftrightarrow> (\<V>s ! i \<in> (map block_complement \<B>s) ! j)"
    using complement_mat_entries by simp
  then have "\<And>i j. i < \<v> \<Longrightarrow>j < \<b> \<Longrightarrow> indexed_comp.N $$ (i, j) =
           mat \<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1) $$ (i, j)"
    by (simp add: indexed_comp.N_def)
  then show "\<And>i j. i < dim_row (mat indexed_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1)) \<Longrightarrow>
           j < dim_col (mat indexed_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1)) \<Longrightarrow>
           indexed_comp.N $$ (i, j) =
           mat indexed_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1) $$ (i, j)"
    by fastforce   
  show "dim_row indexed_comp.N = dim_row (mat indexed_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1))"
    by (simp add: indexed_comp.dim_row_is_v)
  show " dim_col indexed_comp.N =
    dim_col (mat indexed_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1)) "
    by (simp add: indexed_comp.dim_col_is_b)
qed

lemma indexed_complement_mat_map: "indexed_comp.N = map_mat (\<lambda>x. if x = 1 then 0 else 1) N"
proof (intro eq_matI)
  show "\<And>i j. i < dim_row (map_mat (\<lambda>x. if x = 1 then 0 else 1) N) \<Longrightarrow>
           j < dim_col (map_mat (\<lambda>x. if x = 1 then 0 else 1) N) \<Longrightarrow>
           indexed_comp.N $$ (i, j) = map_mat (\<lambda>x. if x = 1 then 0 else 1) N $$ (i, j)"
    by (smt (verit, ccfv_SIG) complement_same_b dim_col_is_b dim_row_is_v index_map_mat(1) 
        index_map_mat(2) index_map_mat(3) indexed_complement indexed_incidence_system.complement_mat_entries 
        indexed_incidence_system.matrix_point_in_block_iff indexed_incidence_system.matrix_point_not_in_block_iff
        indexed_incidence_system_axioms)   
  show "dim_row indexed_comp.N = dim_row (map_mat (\<lambda>x. if x = 1 then 0 else 1) N)"
    by (simp add: dim_row_is_v indexed_comp.dim_row_is_v)
  show "dim_col indexed_comp.N = dim_col (map_mat (\<lambda>x. if x = 1 then 0 else 1) N)"
    by (simp add: dim_col_is_b indexed_comp.dim_col_is_b)
qed


end

context incidence_matrix 
begin

lemma mat_to_blocks_wf: "\<And>b. b \<in># map_to_blocks \<Longrightarrow> b \<subseteq> map_to_points"
  by (auto simp add: map_to_blocks_def map_to_points_def map_col_to_block_def)

lemma map_to_points_perm: "map_to_points_ordered \<in> permutations_of_set map_to_points"
  by (auto simp add: permutations_of_set_def map_to_points_ordered_set map_to_points_ordered_distinct)

lemma map_to_blocks_perm: "map_to_blocks_ordered \<in> permutations_of_multiset map_to_blocks"
  by (simp add: map_to_blocks_ordered_set permutations_of_multisetI)

(* Interesting - can't make this a sublocale - causes it to loop? *)
lemma incidence_sys: "indexed_incidence_system map_to_points map_to_blocks map_to_points_ordered map_to_blocks_ordered"
   apply (unfold_locales)
     apply (simp add: mat_to_blocks_wf)
    apply (simp add: finite_image_iff map_to_points_def)
   apply (simp add: map_to_points_perm)
  using map_to_blocks_perm by simp

end
(* Wrong def 
lemma all_matrices_rep_system:
  assumes "elements_mat N \<subseteq> {0 :: ('b :: {zero_neq_one}), 1}"
  shows "\<exists> V B Vs Bs . indexed_incidence_system V B Vs Bs"
*)

locale indexed_design = indexed_incidence_system \<V> \<B> \<V>s \<B>s + design \<V> \<B> 
  for \<V> and \<B> and \<V>s and \<B>s
begin

(* Basics *)

lemma incidence_mat_non_empty_blocks: 
  assumes "j < \<b>"
  shows "1 \<in>$ (col N j)" 
proof -
  obtain bl where isbl: "\<B>s ! j = bl" by simp
  then have "bl \<in># \<B>"
    using assms valid_blocks_index by auto 
  then obtain x where inbl: "x \<in> bl"
    using blocks_nempty by blast
  then obtain i where isx: "\<V>s ! i = x" and vali: "i < \<v>"
    using \<open>bl \<in># \<B>\<close> valid_points_index_cons wf_invalid_point by blast
  then have "N $$ (i, j) = 1"
    using \<open>\<B>s ! j = bl\<close> \<open>x \<in> bl\<close> assms matrix_point_in_block_one by blast
  thus ?thesis using vec_setI
    by (smt (verit, ccfv_SIG) N_col_def isx vali isbl inbl assms dim_vec_col of_nat_less_imp_less) 
qed
end

locale indexed_bibd = indexed_incidence_system \<V> \<B> \<V>s \<B>s + bibd \<V> \<B> \<k> \<Lambda> 
  for \<V> and \<B> and \<V>s and \<B>s and \<k> and \<Lambda>

begin

(* Every col has k ones *)

lemma incidence_mat_block_size:
  assumes "j < \<b>"
  shows "count_vec (col N j) 1 = \<k>"
  using block_size_mat_rep uniform assms valid_blocks_index by fastforce

lemma incidence_mat_rep_num: 
  assumes "i < \<v>"
  shows "count_vec (row N i) 1 = \<r>"
  using point_rep_mat_row rep_number assms valid_points_index by auto 

lemma incidence_mat_incomplete: 
  assumes "j < \<b>"
  shows "0 \<in>$ (col N j)"
  using assms valid_blocks_index incomplete_block_col incomplete_imp_incomp_block by blast 

lemma incidence_mat_index: 
  assumes "i1 < \<v>"
  assumes "i2 < \<v>"
  assumes "i1 \<noteq> i2"
  shows "card {j \<in> {0..<\<b>} . N $$(i1, j) = 1 \<and> N $$ (i2, j) = 1} = \<B> index {\<V>s ! i1, \<V>s ! i2}"
proof -
  let ?I = "{i1, i2}"
  have ss: "{i1, i2} \<subseteq> {..<\<v>}" using assms by blast
  have image: "((\<lambda> i. \<V>s ! i) ` ?I) = {\<V>s ! i1, \<V>s ! i2}" by simp 
  have filter: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> (\<forall> i \<in> ?I . N $$(i, j) = 1) \<longleftrightarrow> N $$(i1, j) = 1 \<and> N $$ (i2, j) = 1"
    by (auto simp add: assms matrix_point_in_block_iff)
  have "?I \<subseteq> {..<(nat \<v>)}" using assms(1) assms(2) by fastforce
  then have "card {j \<in> {0..<\<b>} . (\<forall> i \<in> ?I . N $$(i, j) = 1)} = \<B> index ((\<lambda> i. \<V>s ! i) ` ?I)"
    using points_index_mat_rep ss by blast
  thus ?thesis using image filter 
    by (smt (verit, best) Collect_cong)
qed

end

end