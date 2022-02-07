theory Incidence_Matrices imports "Design_Extras" Matrix_Vector_Extras "List-Index.List_Index"
 "Design_Theory.Design_Isomorphisms"
begin

(* Incidence vectors *)
definition inc_vec_of :: "'a list \<Rightarrow> 'a set \<Rightarrow> int vec" where
"inc_vec_of Vs bl \<equiv> vec (length Vs) (\<lambda> i . if (Vs ! i) \<in> bl then 1 else 0)"

lemma inc_vec_one_zero_elems: "set\<^sub>v (inc_vec_of Vs bl) \<subseteq> {0, 1}"
  by (auto simp add: vec_set_def inc_vec_of_def)

lemma finite_inc_vec_elems: "finite (set\<^sub>v (inc_vec_of Vs bl))"
  using finite_subset inc_vec_one_zero_elems by blast

lemma inc_vec_elems_max_two: "card (set\<^sub>v (inc_vec_of Vs bl)) \<le> 2"
  using card_mono inc_vec_one_zero_elems finite.emptyI finite.insertI
  by (smt (verit) card_2_iff) 

lemma inc_vec_dim: "dim_vec (inc_vec_of Vs bl) = length Vs"
  by (simp add: inc_vec_of_def)

lemma inc_vec_index_one_iff:  "i < length Vs \<Longrightarrow> inc_vec_of Vs bl $ i = 1 \<longleftrightarrow> Vs ! i \<in> bl"
  by (auto simp add: inc_vec_of_def)

lemma inc_vec_index_zero_iff: "i < length Vs \<Longrightarrow> inc_vec_of Vs bl $ i = 0 \<longleftrightarrow> Vs ! i \<notin> bl"
  by (auto simp add: inc_vec_of_def)

(* Function to find incidence matrix *)

definition inc_mat_of :: "'a list \<Rightarrow> 'a set list \<Rightarrow> int mat" where
"inc_mat_of Vs Bs \<equiv> mat (length Vs) (length Bs) (\<lambda> (i,j) . if (Vs ! i) \<in> (Bs ! j) then 1 else 0)"

lemma inc_mat_one_zero_elems: "elements_mat (inc_mat_of Vs Bs) \<subseteq> {0, 1}"
  by (auto simp add: inc_mat_of_def elements_mat_def)

lemma fin_incidence_mat_elems: "finite (elements_mat (inc_mat_of Vs Bs))"
  using finite_subset inc_mat_one_zero_elems by auto 

lemma inc_matrix_elems_max_two: "card (elements_mat (inc_mat_of Vs Bs)) \<le> 2"
proof -
  have "card {0 ::int , 1} = 2" by auto
  thus ?thesis using card_mono inc_mat_one_zero_elems
    by (metis finite.emptyI finite.insertI) 
qed

lemma inc_mat_of_index [simp]: "i < dim_row (inc_mat_of Vs Bs) \<Longrightarrow> j < dim_col (inc_mat_of Vs Bs) \<Longrightarrow> 
  inc_mat_of Vs Bs $$ (i, j) = (if (Vs ! i) \<in> (Bs ! j) then 1 else 0)"
  by (simp add: inc_mat_of_def)

lemma inc_mat_dim_row: "dim_row (inc_mat_of Vs Bs) = length Vs"
  by (simp add: inc_mat_of_def)

lemma inc_mat_dim_vec_row: "dim_vec (row (inc_mat_of Vs Bs) i) = length Bs"
  by (simp add:  inc_mat_of_def)

lemma inc_mat_dim_col: "dim_col (inc_mat_of Vs Bs) = length Bs"
  by (simp add:  inc_mat_of_def)

lemma inc_mat_dim_vec_col: "dim_vec (col (inc_mat_of Vs Bs) i) = length Vs"
  by (simp add:  inc_mat_of_def)

lemma inc_matrix_point_in_block_one:
  assumes "i < length Vs"
  assumes "j < length Bs"
  assumes "Vs ! i \<in> Bs ! j"
  shows  "(inc_mat_of Vs Bs) $$ (i, j) = 1"
  by (simp add: assms inc_mat_of_def)   

lemma inc_matrix_point_not_in_block_zero: 
  assumes "i < length Vs"
  assumes "j < length Bs"
  assumes "Vs ! i \<notin> Bs ! j"
  shows "(inc_mat_of Vs Bs) $$ (i, j) = 0"
  by(simp add: assms inc_mat_of_def)

lemma inc_matrix_point_in_block:
  assumes "i < length Vs"
  assumes "j < length Bs"
  assumes "(inc_mat_of Vs Bs) $$ (i, j) = 1"
  shows "Vs ! i \<in> Bs ! j"
  using assms(1) assms(2) assms(3) inc_matrix_point_not_in_block_zero by fastforce

lemma inc_matrix_point_not_in_block: 
  assumes "i < length Vs"
  assumes "j < length Bs"
  assumes "(inc_mat_of Vs Bs) $$ (i, j) = 0"
  shows "Vs ! i \<notin> Bs ! j"
  using assms(1) assms(2) assms(3) inc_matrix_point_in_block_one by fastforce

lemma inc_matrix_point_not_in_block_iff: 
  assumes "i < length Vs"
  assumes "j < length Bs"
  shows "(inc_mat_of Vs Bs) $$ (i, j) = 0 \<longleftrightarrow> Vs ! i \<notin> Bs ! j"
  using assms inc_matrix_point_not_in_block inc_matrix_point_not_in_block_zero by blast

lemma inc_matrix_point_in_block_iff: 
  assumes "i < length Vs"
  assumes "j < length Bs"
  shows "(inc_mat_of Vs Bs) $$ (i, j) = 1 \<longleftrightarrow> Vs ! i \<in> Bs ! j"
  using assms inc_matrix_point_in_block inc_matrix_point_in_block_one by blast

lemma inc_matrix_subset_implies_one: 
  assumes "I \<subseteq> {..< length Vs}"
  assumes "j < length Bs"
  assumes "(!) Vs ` I \<subseteq> Bs ! j"
  assumes "i \<in> I"
  shows "(inc_mat_of Vs Bs) $$ (i, j) = 1"
proof - 
  have iin: "Vs ! i \<in> Bs ! j" using assms by auto
  have "i < length Vs" using assms by auto
  thus ?thesis using iin inc_matrix_point_in_block_iff assms(2) by blast  
qed

lemma inc_matrix_one_implies_membership: "I \<subseteq> {..< length Vs} \<Longrightarrow> j < length Bs \<Longrightarrow> 
    (\<And> i. i\<in>I \<Longrightarrow> (inc_mat_of Vs Bs) $$ (i, j) = 1) \<Longrightarrow> i \<in> I \<Longrightarrow> Vs ! i \<in> Bs ! j"
  using inc_matrix_point_in_block subset_iff by blast 

lemma inc_matrix_elems_one_zero: "i < length Vs \<Longrightarrow> j < length Bs \<Longrightarrow> (inc_mat_of Vs Bs) $$ (i, j) = 0 
    \<or> (inc_mat_of Vs Bs) $$ (i, j) = 1"
  using inc_matrix_point_in_block_one inc_matrix_point_not_in_block_zero by blast

(* Start of lemmas to prove basic properties *)

lemma inc_mat_col_def: 
  assumes "j < length Bs"
  assumes "i < length Vs"
  shows "(col (inc_mat_of Vs Bs) j) $ i = (if (Vs ! i \<in> Bs ! j) then 1 else 0)"
  using assms by (simp add: inc_mat_of_def) 

lemma inc_mat_col_list_map_elem: 
  assumes "j < length Bs"
  assumes "i < length Vs"
  shows "col (inc_mat_of Vs Bs) j $ i = map_vec (\<lambda> x . if (x \<in> (Bs ! j)) then 1 else 0) (vec_of_list Vs) $ i"
  by (simp add: inc_mat_of_def assms index_vec_of_list)

lemma inc_mat_col_list_map: 
  assumes "j < length Bs"
  shows "col (inc_mat_of Vs Bs) j = map_vec (\<lambda> x . if (x \<in> (Bs ! j)) then 1 else 0) (vec_of_list Vs)"
  by(intro eq_vecI) (simp_all add: inc_mat_dim_row inc_mat_dim_col inc_mat_col_list_map_elem assms index_vec_of_list)

lemma inc_mat_row_def: 
  assumes "j < length Bs"
  assumes "i < length Vs"
  shows "(row (inc_mat_of Vs Bs) i) $ j = (if (Vs ! i \<in> Bs ! j) then 1 else 0)"
  using assms by (simp add: inc_mat_of_def)

lemma inc_mat_row_list_map_elem: 
  assumes "j < length Bs"
  assumes "i < length Vs"
  shows "row (inc_mat_of Vs Bs) i $ j = map_vec (\<lambda> bl . if ((Vs ! i) \<in> bl) then 1 else 0) (vec_of_list Bs) $ j"
  by (simp add: inc_mat_of_def assms(1) assms(2) vec_of_list_index)

lemma inc_mat_row_list_map: 
  assumes "i < length Vs"
  shows "row (inc_mat_of Vs Bs) i = map_vec (\<lambda> bl . if ((Vs ! i) \<in> bl) then 1 else 0) (vec_of_list Bs)"
  by (intro eq_vecI) (simp_all add: inc_mat_dim_row inc_mat_dim_col inc_mat_row_list_map_elem assms index_vec_of_list)


(* Relationship inc_vec and inc_mat *)

lemma inc_mat_col_inc_vec: "j < length Bs \<Longrightarrow> col (inc_mat_of Vs Bs) j = inc_vec_of Vs (Bs ! j)"
  by (auto simp add: inc_mat_of_def inc_vec_of_def)

lemma inc_mat_of_cols_inc_vecs: "cols (inc_mat_of Vs Bs) = map (\<lambda> j . inc_vec_of Vs j) Bs"
proof (intro nth_equalityI)
  have l1: "length (cols (inc_mat_of Vs Bs)) = length Bs"
    using inc_mat_dim_col by simp
  have l2: "length (map (\<lambda> j . inc_vec_of Vs j) Bs) = length Bs"
    using length_map by simp
  then show "length (cols (inc_mat_of Vs Bs)) = length (map (inc_vec_of Vs) Bs)" using l1 l2 by simp
  show "\<And> i. i < length (cols (inc_mat_of Vs Bs)) \<Longrightarrow> 
    (cols (inc_mat_of Vs Bs) ! i) = (map (\<lambda> j . inc_vec_of Vs j) Bs) ! i"
    using inc_mat_col_inc_vec l1 by simp
qed

definition non_empty_col :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> bool" where
"non_empty_col M j \<equiv> \<exists> k. k \<noteq> 0 \<and> k \<in>$ col M j"

definition proper_inc_mat :: "('a :: {ring, one, zero}) mat \<Rightarrow> bool" where
"proper_inc_mat M \<equiv> (dim_row M > 0 \<and> dim_col M > 0)"

definition mat_rep_num :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_rep_num M i \<equiv> count_vec (row M i) 1"

definition mat_point_index :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat set \<Rightarrow> nat" where
"mat_point_index M I \<equiv> card {j . j < dim_col M \<and> (\<forall> i \<in> I. M $$ (i, j) = 1)}"

definition mat_inter_num :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_inter_num M j1 j2 \<equiv> card {i . i < dim_row M \<and> M $$ (i, j1) = 1 \<and>  M $$ (i, j2) = 1}"

abbreviation mat_block_size :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_block_size M j \<equiv> count_vec (col M j) 1"

lemma non_empty_col_obtains: assumes "non_empty_col M j"
  obtains i where "i < dim_row M" and "(col M j) $ i \<noteq> 0"
proof -
  have d: "dim_vec (col M j) = dim_row M" by simp
  from assms obtain k where "k \<noteq> 0" and "k \<in>$ col M j" by (auto simp add: non_empty_col_def)
  thus ?thesis using vec_contains_obtains_index d
    by (metis that) 
qed

lemma non_empty_col_alt_def: 
  assumes "j < dim_col M" 
  shows "non_empty_col M j \<longleftrightarrow> (\<exists> i. i < dim_row M \<and> M $$ (i, j) \<noteq> 0)"
proof (intro iffI)
  show "non_empty_col M j \<Longrightarrow> \<exists>i<dim_row M. M $$ (i, j) \<noteq> 0"
    by(metis assms index_col non_empty_col_obtains)
next 
  assume "\<exists>i<dim_row M. M $$ (i, j) \<noteq> 0"
  then obtain i where ilt: " i < dim_row M" and ne: "M $$ (i, j) \<noteq> 0" by blast
  then have ilt2: " i < dim_vec (col M j)" by simp
  then have "(col M j) $ i \<noteq> 0" using ne by (simp add: assms) 
  then obtain k where "(col M j) $ i = k" and "k \<noteq> 0"
    by simp
  then show "non_empty_col M j " using non_empty_col_def
    by (metis ilt2 vec_setI) 
qed

lemma mat_block_size_alt: "elements_mat M \<subseteq> {0, 1} \<Longrightarrow> j < dim_col M \<Longrightarrow> mat_block_size M j = sum_vec (col M j)"
  using count_vec_sum_ones_alt by (meson col_elems_subset_mat subset_trans) 

context finite_incidence_system
begin

definition indexes:: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"indexes f \<equiv> bij_betw f {0..< \<v>} \<V>"

end

(* Most incidence matrices are 0, 1 representations *)
locale zero_one_matrix = 
  fixes matrix :: "int mat" ("M")
  assumes elems01: "elements_mat M \<subseteq> {0, 1}"
begin

definition map_to_points:: "nat set" where
"map_to_points \<equiv> {0..<dim_row M}"

lemma map_to_points_card: "card (map_to_points) = dim_row M"
  by (simp add: map_to_points_def)

definition map_col_to_block :: "int vec  \<Rightarrow> nat set" where
"map_col_to_block c \<equiv> { i \<in> {..<dim_vec c} . c $ i = 1}"

lemma map_col_to_block_alt: "map_col_to_block c = {i . i < dim_vec c \<and> c$ i = 1}"
  by (simp add: map_col_to_block_def)

lemma map_col_to_block_elem: "i < dim_vec c \<Longrightarrow> i \<in> map_col_to_block c \<longleftrightarrow>  c $ i = 1"
  by (simp add: map_col_to_block_alt)

lemma in_map_col_valid_index: "i \<in> map_col_to_block c \<Longrightarrow> i < dim_vec c"
  by (simp add: map_col_to_block_alt)

lemma map_col_to_block_elem_not: "vec_set c \<subseteq> {0, 1} \<Longrightarrow> i < dim_vec c \<Longrightarrow> i \<notin> map_col_to_block c \<longleftrightarrow> c $ i = 0"
  apply (auto simp add: map_col_to_block_alt)
  by (meson insert_iff singleton_iff subset_iff vec_setI)

definition map_block_to_col :: "nat set \<Rightarrow> int vec" where
"map_block_to_col bl \<equiv> vec (dim_row M) (\<lambda> x . (if x \<in> bl then 1 else 0))"

definition map_to_blocks :: "nat set multiset" where
"map_to_blocks \<equiv> {# map_col_to_block (col M j). j \<in># mset_set {0..<(dim_col M)} #}"

lemma map_to_blocks_alt: "map_to_blocks \<equiv> {# map_col_to_block c. c \<in># mset (cols M) #}"
  by (simp add: cols_def map_to_blocks_def)

lemma map_to_blocks_size: "size (map_to_blocks) = dim_col M"
  by (simp add: map_to_blocks_def)

definition map_to_points_ordered:: "nat list" ("Vs") where 
"map_to_points_ordered \<equiv>  [0..<dim_row M]"

definition map_to_blocks_ordered:: "nat set list" ("Bs") where
"map_to_blocks_ordered \<equiv> map (\<lambda> c . map_col_to_block c) (cols M)"

lemma map_block_to_col_inc_vec: "map_block_to_col bl = inc_vec_of Vs bl"
  by (auto simp add: map_block_to_col_def inc_vec_of_def map_to_points_ordered_def)

lemma map_to_points_ordered_set: "set Vs = map_to_points"
  by (simp add: map_to_points_ordered_def map_to_points_def)

lemma map_to_blocks_ordered_set: "mset Bs = map_to_blocks"
  by (simp add: map_to_blocks_ordered_def map_to_blocks_alt)

lemma map_to_points_ordered_distinct: "distinct Vs"
  by (metis distinct_upt map_to_points_ordered_def) 

lemma dim_row_length: "length Vs = dim_row M"
  by (simp add: map_to_points_ordered_def)

lemma dim_col_length: "length Bs = dim_col M"
  by (simp add: map_to_blocks_ordered_def)

(* Basic incidence properties *)

lemma dim_vec_row: "dim_vec (row M i) = length Bs"
  by (simp add: map_to_blocks_ordered_def)

lemma dim_vec_col: "dim_vec (col M i) = length Vs"
  by (simp add: map_to_points_ordered_def)

lemma row_elems_ss01: 
  assumes "i < length Vs"
  shows "vec_set (row M i) \<subseteq> {0, 1}"
proof -
  have "vec_set (row M i) \<subseteq> elements_mat M" using assms
    using assms row_elems_subset_mat dim_row_length by auto 
  thus ?thesis using elems01 by blast  
qed

lemma col_elems_ss01: 
  assumes "j < dim_col M"
  shows "vec_set (col M j) \<subseteq> {0, 1}"
proof -
  have "vec_set (col M j) \<subseteq> elements_mat M" using assms 
    by (simp add: col_elems_subset_mat assms) 
  thus ?thesis using elems01 by blast
qed

lemma col_nth_0_or_1_iff: 
  assumes "j < dim_col M"
  assumes "i < dim_row M"
  shows "col M j $ i = 0 \<longleftrightarrow> col M j $ i \<noteq> 1"
  using col_elems_ss01 insertE singletonD subsetD vec_setI
  by (smt (verit, best) assms(1) assms(2) dim_col) 

lemma map_col_block_eq: 
  assumes "c \<in> set(cols M)"
  shows "map_block_to_col (map_col_to_block c) = c"
  apply (simp add: map_col_to_block_def map_block_to_col_def)
proof (intro eq_vecI)
  have "dim_row M = dim_vec c" 
    using assms by (metis carrier_vecD cols_dim subset_code(1)) 
  then show 1: "dim_vec (vec (dim_row M) (\<lambda>x. if x < dim_vec c \<and> c $ x = 1 then 1 else 0)) = dim_vec c"
    by simp
  show "\<And>i. i < dim_vec c \<Longrightarrow> vec (dim_row M) (\<lambda>x. if x < dim_vec c \<and> c $ x = 1 then 1 else 0) $ i = c $ i"
  proof -
    fix i 
    assume "i < dim_vec c"
    have "vec (dim_row M) (\<lambda>x. if x < dim_vec c \<and> c $ x = 1 then 1 else 0) $ i = 
      vec (dim_row M) (\<lambda>x. if c $ x = 1 then 1 else 0) $ i" using 1
      by (simp add: \<open>i < dim_vec c\<close>) 
    also have "... = (if c $ i = 1 then 1 else 0)"
      by (simp add: \<open>dim_row M = dim_vec c\<close> \<open>i < dim_vec c\<close>) 
    also have "... = (if c $ i = 1 then c $ i else 0)"
      by simp 
    finally have "vec (dim_row M) (\<lambda>x. if x < dim_vec c \<and> c $ x = 1 then 1 else 0) $ i = c $ i" using col_nth_0_or_1_iff assms
        \<open>dim_row M = dim_vec c\<close> \<open>i < dim_vec c\<close> cols_length cols_nth in_set_conv_nth dim_col_length dim_row_length
      by (metis (no_types, lifting)) 
    then show "vec (dim_row M) (\<lambda>x. if x < dim_vec c \<and> c $ x = 1 then 1 else 0) $ i = c $ i"
      by simp
  qed
qed

lemma map_points_ordered_nth: "i < dim_row M \<Longrightarrow> Vs ! i = i"
  by (simp add: map_to_points_ordered_def)

lemma map_blocks_ordered_nth: "j < dim_col M \<Longrightarrow> Bs ! j = map_col_to_block (col M j)"
  by (simp add: map_to_blocks_ordered_def)

lemma in_map_col_valid_index_M: "j < dim_col M \<Longrightarrow> i \<in> map_col_to_block (col M j) \<Longrightarrow> i < dim_row M"
  using in_map_col_valid_index by (metis dim_col) 

lemma point_in_block_one:
  assumes "i < dim_row M"
  assumes "j < dim_col M"
  assumes "Vs ! i \<in> Bs ! j"
  shows  "M $$ (i, j) = 1"
using assms map_points_ordered_nth map_blocks_ordered_nth by (simp add: map_col_to_block_elem)

lemma point_not_in_block_zero: 
  assumes "i < dim_row M"
  assumes "j < dim_col M"
  assumes "Vs ! i \<notin> Bs ! j"
  shows "M $$ (i, j) = 0"
using assms map_points_ordered_nth map_blocks_ordered_nth map_col_to_block_elem_not
  by (metis col_elems_ss01 dim_row_length dim_vec_col index_col)

lemma M_def_from_lists: 
  assumes "i < dim_row M"
  assumes "j < dim_col M"
  shows "M $$ (i, j) = (if (Vs ! i) \<in> (Bs ! j) then 1 else 0)"
  using point_in_block_one point_not_in_block_zero assms by simp

lemma one_point_in_block:
  assumes "i < dim_row M"
  assumes "j < dim_col M"
  assumes "M $$ (i, j) = 1"
  shows "Vs ! i \<in> Bs ! j"
  using assms(1) assms(2) assms(3) point_not_in_block_zero by fastforce

lemma zero_point_not_in_block: 
  assumes "i < dim_row M"
  assumes "j < dim_col M"
  assumes "M $$ (i, j) = 0"
  shows "Vs ! i \<notin> Bs ! j"
  using M_def_from_lists assms(1) assms(2) assms(3) by force

lemma point_not_in_block_iff: 
  assumes "i < dim_row M"
  assumes "j < dim_col M"
  shows "M $$ (i, j) = 0 \<longleftrightarrow> Vs ! i \<notin> Bs ! j"
  using assms zero_point_not_in_block point_not_in_block_zero by blast

lemma point_in_block_iff: 
  assumes "i < dim_row M"
  assumes "j < dim_col M"
  shows "M $$ (i, j) = 1 \<longleftrightarrow> Vs ! i \<in> Bs ! j"
  using assms one_point_in_block point_in_block_one by blast

lemma subset_block_mem_implies_one: 
  assumes "I \<subseteq> {..< dim_row M}"
  assumes "j < dim_col M"
  assumes "(!) Vs ` I \<subseteq> Bs ! j"
  assumes "i \<in> I"
  shows "M $$ (i, j) = 1"
proof - 
  have iin: "Vs ! i \<in> Bs ! j" using assms by auto
  have "i < dim_row M" using assms by auto
  thus ?thesis using iin point_in_block_iff assms(2) by blast  
qed

lemma one_implies_membership: "I \<subseteq> {..< dim_row M} \<Longrightarrow> j < dim_col M \<Longrightarrow> 
    (\<And> i. i\<in>I \<Longrightarrow> M $$ (i, j) = 1) \<Longrightarrow> i \<in> I \<Longrightarrow> Vs ! i \<in> Bs ! j"
  by (simp add: one_point_in_block subset_iff)

lemma elems_are_one_zero: "i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> M $$ (i, j) = 0 
    \<or> M $$ (i, j) = 1"
  using point_in_block_one point_not_in_block_zero by blast

(* Start of lemmas to prove basic properties *)

lemma col_nth_def: 
  assumes "j < dim_col M"
  assumes "i < dim_row M"
  shows "(col M j) $ i = (if (Vs ! i \<in> Bs ! j) then 1 else 0)"
  using assms by (simp add: M_def_from_lists)

lemma col_list_map_elem: 
  assumes "j < dim_col M"
  assumes "i < dim_row M"
  shows "col M j $ i = map_vec (\<lambda> x . if (x \<in> (Bs ! j)) then 1 else 0) (vec_of_list Vs) $ i"
  using assms  M_def_from_lists vec_of_list_index
  by (simp add: vec_of_list_index dim_row_length) 

lemma col_list_map: 
  assumes "j < dim_col M"
  shows "col M j = map_vec (\<lambda> x . if (x \<in> (Bs ! j)) then 1 else 0) (vec_of_list Vs)"
  using dim_vec_col assms col_list_map_elem
  by (intro eq_vecI) (simp_all)

lemma row_nth_def: 
  assumes "j < dim_col M"
  assumes "i < dim_row M"
  shows "(row M i) $ j = (if (Vs ! i \<in> Bs ! j) then 1 else 0)"
  using assms by (simp add: M_def_from_lists)

lemma row_list_map_elem: 
  assumes "j < dim_col M"
  assumes "i < dim_row M"
  shows "row M i $ j = map_vec (\<lambda> bl . if ((Vs ! i) \<in> bl) then 1 else 0) (vec_of_list Bs) $ j"
  using assms M_def_from_lists vec_of_list_index
  by (simp add: vec_of_list_index dim_col_length) 

lemma row_list_map: 
  assumes "i < dim_row M"
  shows "row M i = map_vec (\<lambda> bl . if ((Vs ! i) \<in> bl) then 1 else 0) (vec_of_list Bs)"
  using dim_vec_row assms row_list_map_elem by (intro eq_vecI) (simp_all)

lemma transpose_entries: "elements_mat (M\<^sup>T) \<subseteq> {0, 1}"
  using elems01 transpose_mat_elems by metis 

lemma non_empty_col_01: 
  assumes "j < dim_col M"
  shows "non_empty_col M j \<longleftrightarrow> 1 \<in>$ col M j"
proof (intro iffI)
  assume "non_empty_col M j"
  then obtain k where kn0: "k \<noteq> 0" and kin: "k \<in>$ col M j" using non_empty_col_def by auto
  then have "k \<in> elements_mat M" using vec_contains_col_elements_mat assms
    by metis 
  then have "k = 1" using kn0
    using elems01 by blast 
  thus "1 \<in>$ col M j" using kin by simp
next
  assume "1 \<in>$ col M j"
  then show "non_empty_col M j" using non_empty_col_def
    by (metis zero_neq_one)
qed

lemma mat_block_size_alt: "j < dim_col M \<Longrightarrow> mat_block_size M j = sum_vec (col M j)"
  using count_vec_sum_ones_alt col_elems_ss01 by auto

lemma mat_rep_num_alt: 
  assumes "i < dim_row M"
  shows "mat_rep_num M i = card {j . j < dim_col M \<and> M $$ (i, j) = 1}"
proof (simp add: mat_rep_num_def)
  have eq: "\<And> j. (j < dim_col M \<and> M $$ (i, j) = 1) = (row M i $ j = 1 \<and> j < dim_vec (row M i))" 
    using assms by auto
  have "count_vec (row M i) 1 = card {j. (row M i) $ j = 1 \<and>  j < dim_vec (row M i)}"
    using count_vec_alt[of "row M i" "1"] by simp
  thus "count_vec (row M i) 1 = card {j. j < dim_col M \<and> M $$ (i, j) = 1}"
    using eq Collect_cong by simp
qed


(* Map Properties *)

lemma mat_to_blocks_wf: "\<And>b. b \<in># map_to_blocks \<Longrightarrow> b \<subseteq> map_to_points"
  by (auto simp add: map_to_blocks_def map_to_points_def map_col_to_block_def)

lemma map_to_points_finite: "finite map_to_points"
  by (metis List.finite_set map_to_points_ordered_set)

lemma map_to_points_perm: "map_to_points_ordered \<in> permutations_of_set map_to_points"
  by (auto simp add: permutations_of_set_def map_to_points_ordered_set map_to_points_ordered_distinct)

lemma map_to_blocks_perm: "map_to_blocks_ordered \<in> permutations_of_multiset map_to_blocks"
  by (simp add: map_to_blocks_ordered_set permutations_of_multisetI)

sublocale incidence_sys: incidence_system "(map_to_points)" "(map_to_blocks)"
  by (unfold_locales) (simp add: mat_to_blocks_wf)

sublocale fin_incidence_sys: finite_incidence_system "map_to_points" "map_to_blocks"
  by (unfold_locales) (simp add: map_to_points_finite)

lemma one_implies_block_nempty: 
  assumes "j < dim_col M"
  assumes "1 \<in>$ (col M j)"
  shows "map_col_to_block (col M j) \<noteq> {}"
  apply (simp add: map_col_to_block_def)
  using assms vec_setE by (metis dim_col)

lemma block_nempty_implies_all_zeros:
  assumes "j < dim_col M"
  assumes "map_col_to_block (col M j) = {}"
  assumes "i < dim_row M"
  shows "col M j $ i = 0"
  by (metis assms(1) assms(2) assms(3) col_nth_0_or_1_iff dim_col one_implies_block_nempty vec_setI)

lemma block_nempty_implies_no_one:
  assumes "j < dim_col M"
  assumes "map_col_to_block (col M j) = {}"
  shows "\<not> (1 \<in>$ (col M j))"
  using assms(1) assms(2) one_implies_block_nempty by blast

lemma obtain_block_index: 
  assumes "bl \<in># map_to_blocks"
  obtains j where "j < dim_col M" and "bl = map_col_to_block (col M j)"
proof -
  have "bl \<in># {# map_col_to_block (col M j). j \<in># mset_set {0..<(dim_col M)} #}"
    using map_to_blocks_def assms by metis 
  then obtain j where map: "bl = map_col_to_block (col M j)" and "j \<in># mset_set {0..<(dim_col M)}"
    by auto
  then have "j < dim_col M" by simp
  thus ?thesis using map that by auto 
qed

lemma mat_is_design:
  assumes "\<And>j. j < dim_col M\<Longrightarrow> 1 \<in>$ (col M j)"
  shows "design map_to_points map_to_blocks"
proof (unfold_locales)
  fix bl 
  assume "bl \<in># map_to_blocks"
  then obtain j where "j < dim_col M" and map: "bl = map_col_to_block (col M j)"
    using obtain_block_index by auto
  thus  "bl \<noteq> {}" using assms one_implies_block_nempty
    by simp 
qed

lemma col_implies_blocks_nempty: 
  assumes "dim_col M > 0" 
  shows "map_to_blocks \<noteq> {#}"
  by (simp add: map_to_blocks_def assms mset_set_empty_iff)

lemma mat_is_proper_design: 
  assumes "\<And>j. j < dim_col M \<Longrightarrow> 1 \<in>$ (col M j)"
  assumes "dim_col M > 0"
  shows "proper_design map_to_points map_to_blocks"
proof -
  interpret des: design "map_to_points" "map_to_blocks"
    using mat_is_design assms by simp
  show ?thesis proof (unfold_locales)
    have "map_to_blocks \<noteq> {#}" using assms(2) col_implies_blocks_nempty
      by simp 
    then show "incidence_sys.\<b> \<noteq> 0" by simp
  qed
qed
  
end


lemma inc_mat_of_01_mat: "zero_one_matrix (inc_mat_of Vs Bs)"
  by (unfold_locales) (simp add: inc_mat_one_zero_elems) 

lemma inc_mat_ordered_points_Vs: "map ((!) Vs) (zero_one_matrix.map_to_points_ordered (inc_mat_of Vs Bs)) = Vs"
proof -
  interpret mat: zero_one_matrix "(inc_mat_of Vs Bs)"
    using inc_mat_of_01_mat
    by auto 
  have "dim_row (inc_mat_of Vs Bs) = length Vs" by (simp add: inc_mat_dim_row) 
  then have "zero_one_matrix.map_to_points_ordered (inc_mat_of Vs Bs) = [0..<length Vs]" 
    by (simp add: mat.map_to_points_ordered_def)
  thus ?thesis using map_nth by auto
qed

lemma (in zero_one_matrix) rev_map_points_blocks: "inc_mat_of (map_to_points_ordered) (map_to_blocks_ordered) = M"
  by(auto simp add: inc_mat_of_def M_def_from_lists dim_col_length dim_row_length)

(* Indexed locale *)

locale ordered_incidence_system =
  fixes \<V>s :: "'a list" and \<B>s :: "'a set list"
  assumes wf_list: "b \<in># (mset \<B>s) \<Longrightarrow> b \<subseteq> set \<V>s"
  assumes distinct: "distinct \<V>s"
(*  assumes points_indexing: "\<V>s \<in> permutations_of_set \<V>"
  assumes blocks_indexing: "\<B>s \<in> permutations_of_multiset \<B>" *)

sublocale ordered_incidence_system \<subseteq> finite_incidence_system "set \<V>s" "mset \<B>s"
  by(unfold_locales) (auto simp add: wf_list)

lemma ordered_incidence_sysI: 
  assumes "finite_incidence_system \<V> \<B>" and "\<V>s \<in> permutations_of_set \<V>" and "\<B>s \<in> permutations_of_multiset \<B>"
  shows "ordered_incidence_system \<V>s \<B>s"
proof -
  have veq: "\<V> = set \<V>s" using assms permutations_of_setD(1) by auto 
  have beq: "\<B> = mset \<B>s" using assms permutations_of_multisetD by auto
  interpret fisys: finite_incidence_system "set \<V>s" "mset \<B>s" using assms(1) veq beq by simp
  show ?thesis proof (unfold_locales)
    show "\<And>b. b \<in># mset \<B>s \<Longrightarrow> b \<subseteq> set \<V>s" using fisys.wellformed
      by simp 
    show "distinct \<V>s" using assms permutations_of_setD(2) by auto
  qed
qed

lemma ordered_incidence_sysII: 
  assumes "finite_incidence_system \<V> \<B>" and "set \<V>s = \<V>" and "distinct \<V>s" and "mset \<B>s = \<B>"
  shows "ordered_incidence_system \<V>s \<B>s"
proof -
  interpret fisys: finite_incidence_system "set \<V>s" "mset \<B>s" using assms by simp
  show ?thesis using fisys.wellformed assms by (unfold_locales) (simp_all)
qed

context ordered_incidence_system 
begin

abbreviation "\<V> \<equiv> set \<V>s"
abbreviation "\<B> \<equiv> mset \<B>s"

lemma points_indexing: "\<V>s \<in> permutations_of_set \<V>"
  by (simp add: permutations_of_set_def distinct)

lemma blocks_indexing: "\<B>s \<in> permutations_of_multiset \<B>"
  by (simp add: permutations_of_multiset_def)

(* Lemmas on ordering *)

lemma points_list_empty_iff: "\<V>s = [] \<longleftrightarrow> \<V> = {}"
  using finite_sets points_indexing
  by (simp add: elem_permutation_of_set_empty_iff) 

lemma points_indexing_inj: "\<forall> i \<in> I . i < length \<V>s \<Longrightarrow> inj_on ((!) \<V>s) I"
  by (simp add: distinct inj_on_nth)

lemma blocks_list_empty_iff: "\<B>s = [] \<longleftrightarrow> \<B> = {#}"
  using blocks_indexing by (simp) 

lemma blocks_list_nempty: "proper_design \<V> \<B> \<Longrightarrow> \<B>s \<noteq> []"
  using mset.simps(1) proper_design.design_blocks_nempty by blast

lemma points_list_nempty: "proper_design \<V> \<B> \<Longrightarrow> \<V>s \<noteq> []"
  using proper_design.design_points_nempty points_list_empty_iff by blast

lemma points_list_length: "length \<V>s = \<v>"
  using points_indexing
  by (simp add: length_finite_permutations_of_set) 

lemma blocks_list_length: "length \<B>s = \<b>"
  using blocks_indexing length_finite_permutations_of_multiset by blast

lemma valid_points_index: "i < \<v> \<Longrightarrow> \<V>s ! i \<in> \<V>"
  using points_list_length by simp 

lemma valid_points_index_cons: "x \<in> \<V> \<Longrightarrow> \<exists> i. \<V>s ! i = x \<and> i < \<v>"
  apply (simp add:  in_set_conv_nth)
  using points_list_length by auto

lemma valid_points_index_obtains: 
  assumes "x \<in> \<V>"
  obtains i where "\<V>s ! i = x \<and> i < \<v>"
  using valid_points_index_cons assms by auto

lemma valid_blocks_index: "j < \<b> \<Longrightarrow> \<B>s ! j \<in># \<B>"
  using blocks_list_length by (metis nth_mem_mset)

lemma valid_blocks_index_cons: "bl \<in># \<B> \<Longrightarrow> \<exists> j . \<B>s ! j = bl \<and> j < \<b>"
  by (auto simp add: in_set_conv_nth)

lemma valid_blocks_index_obtains: assumes "bl \<in># \<B>"
  obtains j where  "\<B>s ! j = bl \<and> j < \<b>"
  using assms valid_blocks_index_cons by auto

lemma block_points_valid_point_index: 
  assumes "bl \<in># \<B>"
  assumes "x \<in> bl"
  obtains i where "i < length \<V>s \<and> \<V>s ! i = x"
  using wellformed valid_points_index_obtains assms
  by (metis points_list_length wf_invalid_point) 

lemma points_set_image: "\<V> = image(\<lambda> i . (\<V>s ! i)) ({..<\<v>})"
  using valid_points_index_cons valid_points_index by auto

lemma blocks_mset_image: "\<B> = image_mset (\<lambda> i . (\<B>s ! i)) (mset_set {..<\<b>})"
  by (simp add: mset_list_by_index)

lemma incidence_cond_indexed[simp]: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> incident (\<V>s ! i) (\<B>s ! j) \<longleftrightarrow> (\<V>s ! i) \<in> (\<B>s ! j)"
  using incidence_alt_def valid_points_index valid_blocks_index by simp

lemma bij_betw_points_index: "bij_betw (\<lambda> i. \<V>s ! i) {0..<\<v>} \<V>"
proof (simp add: bij_betw_def, intro conjI)
  show "inj_on ((!) \<V>s) {0..<\<v>}"
    by (simp add: points_indexing_inj points_list_length) 
  show "(!) \<V>s ` {0..<\<v>} = \<V>" 
  proof (intro subset_antisym subsetI)
    fix x assume "x \<in> (!) \<V>s ` {0..<\<v>}" 
    then obtain i where "x = \<V>s ! i" and "i < \<v>" by auto
    then show "x \<in> \<V>"
      by (simp add: valid_points_index) 
  next 
    fix x assume "x \<in> \<V>"
    then obtain i where "\<V>s ! i = x" and "i <\<v>"
      using valid_points_index_cons by auto 
    then show "x \<in> (!) \<V>s ` {0..<\<v>}" by auto
  qed
qed

lemma obtains_two_diff_index: 
  assumes "j1 < \<b>"
  assumes "j2 < \<b>"
  assumes "j1 \<noteq> j2"
  assumes "\<b> \<ge> 2"
  obtains bl1 bl2 where "bl1 \<in># \<B>" and "\<B>s ! j1 = bl1" and "bl2 \<in># \<B> - {#bl1#}" and "\<B>s ! j2 = bl2"
proof -
  have j1lt: "min j1 (length \<B>s) = j1" using assms by auto
  obtain bl1 where bl1in: "bl1 \<in># \<B>" and bl1eq: "\<B>s ! j1 = bl1"
    using assms(1) valid_blocks_index by blast
  then have split: "\<B>s = take j1 \<B>s @ \<B>s!j1 # drop (Suc j1) \<B>s" 
    using assms id_take_nth_drop by auto
  then have lj1: "length (take j1 \<B>s) = j1" using j1lt by (simp add: length_take[of j1 \<B>s]) 
  have "\<B> = mset (take j1 \<B>s @ \<B>s!j1 # drop (Suc j1) \<B>s)" using split assms(1) by presburger 
  then have bsplit: "\<B> = mset (take j1 \<B>s) + {#bl1#} + mset (drop (Suc j1) \<B>s)" by (simp add: bl1eq)
  then have btake: "\<B> - {#bl1#} = mset (take j1 \<B>s) + mset (drop (Suc j1) \<B>s)" by simp
  thus ?thesis proof (cases "j2 < j1")
    case True
    then have "j2 < length (take j1 \<B>s)" using lj1 by simp
    then obtain bl2 where bl2eq: "bl2 = (take j1 \<B>s) ! j2" by auto
    then have bl2eq2: "bl2 = \<B>s ! j2"
      by (simp add: True) 
    then have "bl2 \<in># \<B> - {#bl1#}" using btake
      by (metis bl2eq \<open>j2 < length (take j1 \<B>s)\<close> nth_mem_mset union_iff) 
    then show ?thesis using bl2eq2 bl1in bl1eq that by auto
  next
    case False
    then have j2gt: "j2 \<ge> Suc j1" using assms by simp
    then obtain i where ieq: "i = j2 - Suc j1"
      by simp 
    then have j2eq: "j2 = (Suc j1) + i" using j2gt by presburger
    have "length (drop (Suc j1) \<B>s) = \<b> - (Suc j1)" using blocks_list_length by auto
    then have "i < length (drop (Suc j1) \<B>s)" using ieq assms blocks_list_length
      using diff_less_mono j2gt by presburger 
    then obtain bl2 where bl2eq: "bl2 = (drop (Suc j1) \<B>s) ! i" by auto
    then have bl2in: "bl2 \<in># \<B> - {#bl1#}" using btake nth_mem_mset union_iff
      by (metis \<open>i < length (drop (Suc j1) \<B>s)\<close>) 
    then have "bl2 = \<B>s ! j2" using bl2eq nth_drop blocks_list_length assms j2eq
      by (metis Suc_leI)
    then show ?thesis using bl1in bl1eq bl2in that by auto
  qed
qed

(* Incidence Matrix *)

abbreviation N :: "int mat" where
"N \<equiv> inc_mat_of \<V>s \<B>s"

sublocale mat: zero_one_matrix "N"
  using inc_mat_of_01_mat .

lemma N_alt_def_dim: "N = mat \<v> \<b> (\<lambda> (i,j) . if (incident (\<V>s ! i) (\<B>s ! j)) then 1 else 0) " 
  using incidence_cond_indexed inc_mat_of_def 
  by (intro eq_matI) (simp_all add: inc_mat_dim_row inc_mat_dim_col inc_matrix_point_in_block_one inc_matrix_point_not_in_block_zero 
      points_list_length)
 
lemma N_carrier_mat: "N \<in> carrier_mat \<v> \<b>" 
  by (simp add: N_alt_def_dim)

(* Basic Incidence Matrix lemmas *)

lemma dim_row_is_v: "dim_row N = \<v>"
  by (simp add: N_alt_def_dim)

lemma dim_vec_row: "dim_vec (row N i) = \<b>"
  by (simp add:  N_alt_def_dim)

lemma dim_col_is_b: "dim_col N = \<b>"
  by (simp add:  N_alt_def_dim)

lemma dim_col_b_lt_iff: "j < \<b> \<longleftrightarrow> j < dim_col N"
  by (simp add: dim_col_is_b)

lemma dim_row_v_lt_iff: "i < \<v> \<longleftrightarrow> i < dim_row N"
  by (simp add: dim_row_is_v)

lemma dim_vec_col: "dim_vec (col N i) = \<v>"
  by (simp add: N_alt_def_dim)

lemma mat_row_elems: "i < \<v> \<Longrightarrow> vec_set (row N i) \<subseteq> {0, 1}"
  using points_list_length
  by (simp add: dim_row_is_v mat.dim_row_length mat.row_elems_ss01) 

lemma mat_col_elems: "j < \<b> \<Longrightarrow> vec_set (col N j) \<subseteq> {0, 1}"
  using blocks_list_length
  by (metis mat.col_elems_ss01 dim_col_is_b)

lemma matrix_point_in_block_one: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> (\<V>s ! i)\<in> (\<B>s ! j) \<Longrightarrow>N $$ (i, j) = 1"
  by (metis inc_matrix_point_in_block_one points_list_length blocks_list_length )   

lemma matrix_point_not_in_block_zero: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> \<V>s ! i \<notin> \<B>s ! j \<Longrightarrow> N $$ (i, j) = 0"
  by(metis inc_matrix_point_not_in_block_zero points_list_length blocks_list_length)

lemma matrix_point_in_block: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 1 \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
  by (metis blocks_list_length points_list_length  inc_matrix_point_in_block)

lemma matrix_point_not_in_block: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 0 \<Longrightarrow> \<V>s ! i \<notin> \<B>s ! j"
  by (metis blocks_list_length points_list_length inc_matrix_point_not_in_block)

lemma matrix_point_not_in_block_iff: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 0 \<longleftrightarrow> \<V>s ! i \<notin> \<B>s ! j"
  by (metis blocks_list_length points_list_length inc_matrix_point_not_in_block_iff)

lemma matrix_point_in_block_iff: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 1 \<longleftrightarrow> \<V>s ! i \<in> \<B>s ! j"
  by (metis blocks_list_length points_list_length inc_matrix_point_in_block_iff)

lemma matrix_subset_implies_one: "I \<subseteq> {..< \<v>} \<Longrightarrow> j < \<b> \<Longrightarrow> (!) \<V>s ` I \<subseteq> \<B>s ! j \<Longrightarrow> i \<in> I \<Longrightarrow> 
  N $$ (i, j) = 1"
  by (metis blocks_list_length points_list_length inc_matrix_subset_implies_one)

lemma matrix_one_implies_membership: 
"I \<subseteq> {..< \<v>} \<Longrightarrow> j < size \<B> \<Longrightarrow> \<forall>i\<in>I. N $$ (i, j) = 1 \<Longrightarrow> i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
  by (simp add: matrix_point_in_block_iff subset_iff)

lemma matrix_elems_one_zero: "i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N $$ (i, j) = 0 \<or> N $$ (i, j) = 1"
  by (metis blocks_list_length inc_matrix_elems_one_zero points_list_length)

(* Inc Vec Of *)

lemma col_inc_vec_of: "j < length \<B>s \<Longrightarrow> inc_vec_of \<V>s (\<B>s ! j) = col N j"
  by (simp add: inc_mat_col_inc_vec) 

lemma inc_vec_eq_iff_blocks: 
  assumes "bl \<in># \<B>"
  assumes "bl' \<in># \<B>"
  shows "inc_vec_of \<V>s bl = inc_vec_of \<V>s bl' \<longleftrightarrow> bl = bl'"
proof (intro iffI eq_vecI)
  assume "inc_vec_of \<V>s bl = inc_vec_of \<V>s bl'"
  then have "\<And> i. i < dim_vec (inc_vec_of \<V>s bl') \<Longrightarrow> inc_vec_of \<V>s bl $ i = inc_vec_of \<V>s bl' $ i" using eq_vecI by simp
  then have "\<And> i. i < length \<V>s \<Longrightarrow> inc_vec_of \<V>s bl $ i = inc_vec_of \<V>s bl' $ i" by (simp add: inc_vec_dim)
  then have "\<And> i. i < length \<V>s \<Longrightarrow> (\<V>s ! i)  \<in> bl \<longleftrightarrow> (\<V>s ! i)  \<in> bl'"
    by (metis inc_vec_index_one_iff) 
  then have "\<And> x. x \<in> \<V> \<Longrightarrow> x \<in> bl \<longleftrightarrow> x \<in> bl'"
    using points_list_length valid_points_index_cons by auto 
  then show "bl = bl'" using wellformed assms
    by (meson subset_antisym subset_eq)
next
  assume "bl = bl'"
  show "dim_vec (inc_vec_of \<V>s bl) = dim_vec (inc_vec_of \<V>s bl')"
    by (simp add: inc_vec_dim)  
next
  fix i assume bleq: "bl = bl'" assume ilt: "i < dim_vec (inc_vec_of \<V>s bl')"
  show "inc_vec_of \<V>s bl $ i = inc_vec_of \<V>s bl' $ i" using inc_vec_index_one_iff
    by (simp add: bleq) 
qed

(* Start of lemmas to prove basic properties *)

lemma N_col_def: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> (col N j) $ i = (if (\<V>s ! i \<in> \<B>s ! j) then 1 else 0)"
  by (metis inc_mat_col_def points_list_length blocks_list_length) 

lemma N_col_def_indiv: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j \<Longrightarrow> (col N j) $ i = 1"
     "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> \<V>s ! i \<notin> \<B>s ! j \<Longrightarrow> (col N j) $ i = 0"
  by (simp_all add: N_col_def)

lemma N_col_list_map_elem: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> 
    col N j $ i = map_vec (\<lambda> x . if (x \<in> (\<B>s ! j)) then 1 else 0) (vec_of_list \<V>s) $ i"
  by (metis inc_mat_col_list_map_elem points_list_length blocks_list_length) 

lemma N_col_list_map: "j < \<b> \<Longrightarrow> col N j = map_vec (\<lambda> x . if (x \<in> (\<B>s ! j)) then 1 else 0) (vec_of_list \<V>s)"
  by (metis inc_mat_col_list_map blocks_list_length) 

lemma N_col_mset_point_set_img: "j < \<b> \<Longrightarrow> 
    vec_mset (col N j) = image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else 0) (mset_set \<V>)"
  using vec_mset_img_map N_col_list_map
  by (metis (no_types, lifting) finite_sets permutations_of_multisetD permutations_of_set_altdef points_indexing) 

lemma matrix_col_to_block: 
  assumes "j < \<b>"
  shows "\<B>s ! j = (\<lambda> k . \<V>s ! k) ` {i \<in> {..< \<v>} . (col N j) $ i = 1}"
proof (intro subset_antisym subsetI)
  fix x assume assm1: "x \<in> \<B>s ! j"
  then have "x \<in> \<V>" using wellformed assms valid_blocks_index by blast 
  then obtain i where vs: "\<V>s ! i = x" and "i < \<v>"
    using valid_points_index_cons by auto 
  then have inset: "i \<in> {..< \<v>}"
    by fastforce
  then have "col N j $ i = 1" using assm1 N_col_def assms vs
    using \<open>i < \<v>\<close> by presburger 
  then have "i \<in> {i. i \<in> {..< \<v>} \<and> col N j $ i = 1}"
    using inset by blast
  then show "x \<in> (!) \<V>s ` {i.  i \<in> {..<\<v>} \<and> col N j $ i = 1}" using vs by blast
next
  fix x assume assm2: "x \<in> ((\<lambda> k . \<V>s ! k) ` {i \<in> {..< \<v>} . col N j $ i = 1})"
  then obtain k where "x = \<V>s !k" and inner: "k \<in>{i \<in> {..< \<v>} . col N j $ i = 1}"
    by blast 
  then have ilt: "k < \<v>" by auto
  then have "N $$ (k, j) = 1" using inner
    by (metis (mono_tags) N_col_def assms matrix_point_in_block_iff matrix_point_not_in_block_zero mem_Collect_eq) 
  then show "x \<in> \<B>s ! j" using ilt
    using \<open>x = \<V>s ! k\<close> assms matrix_point_in_block_iff by blast
qed

lemma matrix_col_to_block_v2: 
  assumes "j < \<b>"
  shows "\<B>s ! j = (\<lambda> k . \<V>s ! k) ` mat.map_col_to_block (col N j)"
  using matrix_col_to_block mat.map_col_to_block_def assms
  by (simp add: dim_row_is_v)

lemma matrix_col_in_blocks: "j < \<b> \<Longrightarrow> (!) \<V>s ` mat.map_col_to_block (col N j) \<in># \<B>"
  using matrix_col_to_block_v2 by (metis (no_types, lifting) valid_blocks_index) 

lemma N_row_def: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> (row N i) $ j = (if (\<V>s ! i \<in> \<B>s ! j) then 1 else 0)"
  by (metis inc_mat_row_def points_list_length blocks_list_length) 

lemma N_row_list_map_elem: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> 
    row N i $ j = map_vec (\<lambda> bl . if ((\<V>s ! i) \<in> bl) then 1 else 0) (vec_of_list \<B>s) $ j"
  by (metis inc_mat_row_list_map_elem points_list_length blocks_list_length) 

lemma N_row_list_map: "i < \<v> \<Longrightarrow> 
    row N i = map_vec (\<lambda> bl . if ((\<V>s ! i) \<in> bl) then 1 else 0) (vec_of_list \<B>s)"
  by (simp add: inc_mat_row_list_map points_list_length blocks_list_length) 

lemma N_row_mset_blocks_img: "i < \<v> \<Longrightarrow> 
    vec_mset (row N i) = image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else 0) \<B>"
  using vec_mset_img_map N_row_list_map by metis

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
  have "\<And>bl. bl \<in># \<B> \<Longrightarrow> (\<lambda>x .0 ::int) bl \<noteq> 1" using zero_neq_one 
    by simp 
  then have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: int )) \<B>) 1 = 
    size (filter_mset (\<lambda> x . (\<V>s ! i) \<in> x) \<B>)"
    using count_mset_split_image_filter[of "\<B>" "1" "\<lambda> x . (0 :: int)" "\<lambda> x . (\<V>s ! i) \<in> x"] by simp
  then have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: int )) \<B>) 1
    = \<B> rep (\<V>s ! i)" by (simp add: point_rep_number_alt_def)
  thus ?thesis
    by (simp add: 1) 
qed

lemma point_rep_mat_row_sum: 
  assumes "i < \<v>"
  shows "sum_vec (row N i) = \<B> rep (\<V>s ! i)"
  using count_vec_sum_ones_alt assms point_rep_mat_row mat_row_elems
  by metis 

lemma block_size_mat_rep: 
  assumes "j < \<b>"
  shows "count_vec (col N j) 1 = card (\<B>s ! j)"
proof -
  have 1: "vec_mset (col N j) = image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else 0) (mset_set \<V>)"
    using N_col_mset_point_set_img assms by auto
  have val_b: "\<B>s ! j \<in># \<B>" using assms valid_blocks_index by auto 
  have "\<And> x. x \<in># mset_set \<V> \<Longrightarrow> (\<lambda>x . (0 :: int)) x \<noteq> 1" using zero_neq_one by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: int)) (mset_set \<V>)) 1 = 
    size (filter_mset (\<lambda> x . x \<in> (\<B>s ! j)) (mset_set \<V>))"
    using count_mset_split_image_filter [of "mset_set \<V>" "1" "(\<lambda> x . (0 :: int))" "\<lambda> x . x \<in> \<B>s ! j"] by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: int)) (mset_set \<V>)) 1 = card (\<B>s ! j)"
    using val_b block_size_alt by (simp add: finite_sets)
  thus ?thesis by (simp add: 1)
qed

lemma block_size_mat_rep_sum: 
  assumes "j < \<b>"
  shows "sum_vec (col N j) = card (\<B>s ! j)"
  using count_vec_sum_ones_alt block_size_mat_rep assms
  by (metis mat_col_elems) 

lemma points_img_index_rep: "\<V> = image (\<lambda> j. \<V>s ! j) {0..<length \<V>s}"
  using lessThan_atLeast0 points_list_length points_set_image by presburger


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
  shows "card {j \<in> {0..<\<b>} . (\<forall> i \<in> I . N $$(i, j) = 1)} = \<B> index ((\<lambda> i. \<V>s ! i) ` I)"
proof - 
  have "\<And> i . i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>" using assms valid_points_index by auto 
  then have eqP: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> ((\<lambda> i. \<V>s ! i) ` I) \<subseteq> (\<B>s ! j) \<longleftrightarrow> (\<forall> i \<in> I . N $$ (i, j) = 1)"
  proof (auto)
    show "\<And>j i. j < length \<B>s \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>) \<Longrightarrow> (!) \<V>s ` I \<subseteq> \<B>s ! j \<Longrightarrow> i \<in> I \<Longrightarrow> N $$ (i, j) = 1"
      using matrix_subset_implies_one assms by simp
    show "\<And>j i. j < length \<B>s \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<V>) \<Longrightarrow> \<forall>i\<in>I. N $$ (i, j) = 1 \<Longrightarrow> i \<in> I \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
      using assms matrix_one_implies_membership
      by (metis blocks_list_length) 
  qed
  have "card {j \<in> {0..<\<b>} . (\<forall> i \<in> I . N $$(i, j) = 1)} = card { j \<in> {0..<\<b>}. ((\<lambda> i . \<V>s ! i) ` I) \<subseteq> \<B>s ! j}"
    using eqP by (metis (mono_tags, lifting))
  also have "... = size {# b \<in># \<B> . ((\<lambda> i . \<V>s ! i) ` I) \<subseteq> b #}"
    using filter_size_blocks_eq_card_indexes by auto
  also have "... = points_index \<B> ((\<lambda> i . \<V>s ! i) ` I)"
    by (simp add: points_index_def)
  finally have "card {j \<in> {0..<\<b>} . (\<forall> i \<in> I . N $$(i, j) = 1)} = \<B> index ((\<lambda> i . \<V>s ! i) ` I)"
    by blast
  thus ?thesis by simp
qed

lemma incidence_mat_two_index: 
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

lemma ones_incidence_mat_block_size: 
  assumes "j < \<b>"
  shows "((u\<^sub>v \<v>) \<^sub>v* N) $ j = card (\<B>s ! j)"
proof - 
  have "dim_vec ((u\<^sub>v \<v>) \<^sub>v* N) = \<b>"
    by (simp add: dim_col_is_b) 
  then have "((u\<^sub>v \<v>) \<^sub>v* N) $ j = (u\<^sub>v \<v>) \<bullet> col N j" using assms by simp 
  also have "... = (\<Sum> i \<in> {0 ..< \<v>}. (u\<^sub>v \<v>) $ i * (col N j) $ i)" 
    by (simp add: scalar_prod_def dim_row_is_v)
  also have "... = sum_vec (col N j)" using dim_row_is_v by (simp add: sum_vec_def)
  finally have "((u\<^sub>v \<v>) \<^sub>v* N) $ j = card (\<B>s ! j)" using block_size_mat_rep_sum assms by simp
  thus ?thesis by simp
qed

lemma mat_block_size_conv: 
  assumes "j < dim_col N"
  shows "card (\<B>s ! j) = mat_block_size N j"
  using assms by (simp add: block_size_mat_rep dim_col_is_b)

lemma mat_inter_num_conv: 
  assumes "j1 < dim_col N" "j2 < dim_col N"
  shows "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = mat_inter_num N j1 j2"
proof -
  have eq_sets: "\<And> P. (\<lambda> i . \<V>s ! i) ` {i \<in> {0..<\<v>}. P (\<V>s ! i)} = {x \<in> \<V> . P x}"
    by (metis Compr_image_eq points_img_index_rep points_list_length) 
  have bin: "\<B>s ! j1 \<in># \<B>" "\<B>s ! j2 \<in># \<B>" using assms dim_col_is_b by simp_all
  have "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = card ((\<B>s ! j1) \<inter> (\<B>s ! j2))" by (simp add: intersection_number_def)
  also have "... = card {x . x \<in> (\<B>s ! j1) \<and> x \<in> (\<B>s ! j2)}"
    by (simp add: Int_def) 
  also have "... = card {x \<in> \<V>. x \<in> (\<B>s ! j1) \<and> x \<in> (\<B>s ! j2)}" using wellformed bin
    by (meson wf_invalid_point) 
  also have "... = card ((\<lambda> i . \<V>s ! i) ` {i \<in> {0..<\<v>}. (\<V>s ! i) \<in> (\<B>s ! j1) \<and> (\<V>s ! i) \<in> (\<B>s ! j2)})" 
    using eq_sets[of "\<lambda> x. x \<in> (\<B>s ! j1) \<and> x \<in> (\<B>s ! j2)"] by simp
  also have "... = card ({i \<in> {0..<\<v>}. (\<V>s ! i) \<in> (\<B>s ! j1) \<and> (\<V>s ! i) \<in> (\<B>s ! j2)})"
    using points_indexing_inj card_image
    by (metis (no_types, lifting) lessThan_atLeast0 lessThan_iff mem_Collect_eq points_list_length) 
  also have "... = card ({i . i < \<v> \<and> (\<V>s ! i) \<in> (\<B>s ! j1) \<and> (\<V>s ! i) \<in> (\<B>s ! j2)})" by auto
  also have "... = card ({i . i < \<v> \<and> N $$ (i, j1) = 1 \<and> N $$ (i, j2) = 1})" using assms
    by (metis (no_types, opaque_lifting) inc_mat_dim_col inc_matrix_point_in_block_iff points_list_length) 
  finally have "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = card {i . i < dim_row N \<and> N $$ (i, j1) = 1 \<and> N $$ (i, j2) = 1}"
    using dim_row_is_v by presburger
  thus ?thesis using assms by (simp add: mat_inter_num_def)
qed

lemma non_empty_col_map_conv: 
  assumes "j < dim_col N"
  shows "non_empty_col N j \<longleftrightarrow> \<B>s ! j \<noteq> {}"
proof (intro iffI)
  assume "non_empty_col N j"
  then obtain i where ilt: "i < dim_row N" and "(col N j) $ i \<noteq> 0"
    using non_empty_col_obtains assms by blast
  then have "(col N j) $ i = 1"
    using assms mat.col_nth_0_or_1_iff by blast
  then have "\<V>s ! i \<in> \<B>s ! j"
    by (smt (verit, best) assms ilt inc_mat_col_def dim_col_is_b inc_mat_dim_col inc_mat_dim_row) 
  thus "\<B>s ! j \<noteq> {}" by blast
next
  assume a: "\<B>s ! j \<noteq> {}"
  have "\<B>s ! j \<in># \<B>" using assms dim_col_is_b by simp
  then obtain x where "x \<in> \<B>s ! j" and "x \<in> \<V>" using wellformed a by auto
  then obtain i where "\<V>s ! i \<in> \<B>s ! j" and "i < dim_row N" using dim_row_is_v
    using valid_points_index_cons by auto 
  then have "N $$ (i, j) = 1"
    using assms by auto 
  then show "non_empty_col N j" using non_empty_col_alt_def
    using \<open>i < dim_row N\<close> assms by fastforce 
qed

lemma mat_rep_num_conv: 
  assumes "i < dim_row N"
  shows "mat_rep_num N i = \<B> rep (\<V>s ! i)"
  using point_rep_mat_row assms  mat_rep_num_def
  by (metis dim_row_is_v) 

lemma mat_point_index_conv: 
  assumes "I \<subseteq> {..<\<v>}"
  shows "mat_point_index N I = \<B> index ((\<lambda> i. \<V>s ! i) ` I)"
  unfolding  mat_point_index_def
  using assms points_index_mat_rep[of I]  dim_col_is_b
  by fastforce 

lemma transpose_N_mult_dim: "dim_row (N * N\<^sup>T) = \<v>" "dim_col (N * N\<^sup>T) = \<v>"
  by (simp_all add: dim_row_is_v)
  
lemma inc_matrix_points: "(\<lambda> x. \<V>s ! x) ` (mat.map_to_points) = \<V>"
  apply (simp add: mat.map_to_points_def dim_row_is_v)
  by (metis lessThan_atLeast0 points_set_image)



lemma dim_vec_N_col: 
  assumes "j < \<b>"
  shows "dim_vec (cols N ! j) = \<v>"
proof -
  have "cols N ! j = col N j" using assms dim_col_is_b by simp
  then have "dim_vec (cols N ! j) = dim_vec (col N j)" by simp
  thus ?thesis using dim_col assms
    by (simp add: dim_row_is_v) 
qed

lemma card_filter_point_indices: 
"card {i \<in> {0..<\<v>}. P (\<V>s ! i)} = card {v \<in> \<V> . P v }"
proof -
  have "{v \<in> \<V> . P v }= (\<lambda> i. \<V>s ! i) ` {i \<in> {0..<\<v>}. P (\<V>s ! i)}"
    by (metis Compr_image_eq points_img_index_rep points_list_length)
  thus ?thesis using inj_on_nth
    by (metis (no_types, lifting) card_image distinct lessThan_atLeast0 lessThan_iff mem_Collect_eq points_list_length)
qed

lemma card_block_points_filter: 
  assumes "j < \<b>"
  shows "card (\<B>s ! j) = card {i \<in> {0..<\<v>} . (\<V>s ! i) \<in> (\<B>s ! j)}"
proof -
  obtain bl where "bl \<in># \<B>" and blis: "bl = \<B>s ! j"
    using assms by auto
  then have cbl: "card bl = card {v \<in> \<V> . v \<in> bl}" using block_size_alt by simp
  have "\<V> = (\<lambda> i. \<V>s ! i) ` {0..<\<v>}" using bij_betw_points_index
    using lessThan_atLeast0 points_set_image by presburger
  then have "Set.filter (\<lambda> v . v \<in> bl) \<V> = Set.filter (\<lambda> v . v \<in> bl) ((\<lambda> i. \<V>s ! i) ` {0..<\<v>})"
    by presburger 
  have "card {i \<in> {0..<\<v>} . (\<V>s ! i) \<in> bl} = card {v \<in> \<V> . v \<in> bl}" 
    using card_filter_point_indices by simp
  thus ?thesis using cbl blis by simp
qed

lemma N_not_zero_simp: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> N $$ (i, j) \<noteq> 0 \<Longrightarrow> N $$ (i, j) = 1"
  using matrix_elems_one_zero by auto

lemma N_not_one_simp: "j < \<b> \<Longrightarrow> i < \<v> \<Longrightarrow> N $$ (i, j) \<noteq> 1 \<Longrightarrow> N $$ (i, j) = 0"
  using matrix_elems_one_zero by auto

lemma N_index_square_itself: 
  assumes "j < \<b>" "i < \<v>"
  shows "(N $$ (i, j))^2 = N $$ (i, j)"
    using N_not_zero_simp assms by (cases "N $$ (i, j) = 0")( simp_all, metis power_one) 

lemma N_col_index_square_itself: 
  assumes "j < \<b>" "i < \<v>"
  shows "((col N j) $ i)^2 = (col N j) $ i"
  using index_col N_index_square_itself[of j i] assms N_carrier_mat by auto

lemma scalar_prod_inc_vec_block_size_mat:
  assumes "j < \<b>"
  shows "(col N j) \<bullet> (col N j) = mat_block_size N j"
proof -
  have "(col N j) \<bullet> (col N j) = (\<Sum> i \<in> {0..<\<v>} . (col N j) $ i * (col N j) $ i)" 
     using assms dim_vec_N_col scalar_prod_def
     by (metis (no_types, lifting) dim_vec_col sum.cong)
  also have "... = (\<Sum> i \<in> {0..<\<v>} . ((col N j) $ i)^2)"
    by (simp add: power2_eq_square ) 
  also have "... = (\<Sum> i \<in> {0..<\<v>} . ((col N j) $ i))"
    using N_col_index_square_itself assms by auto
  finally show ?thesis using sum_vec_def
    by (metis assms dim_col dim_col_is_b dim_row_is_v mat.mat_block_size_alt)
qed


lemma scalar_prod_inc_vec_block_size:
  assumes "j < \<b>"
  shows "(col N j) \<bullet> (col N j) = card (\<B>s ! j)"
  using scalar_prod_inc_vec_block_size_mat assms block_size_mat_rep by presburger 

lemma blocks_index_ne_belong: 
  assumes "i1 < length \<B>s"
  assumes "i2 < length \<B>s"
  assumes "i1 \<noteq> i2"
  shows "\<B>s ! i2 \<in># \<B> - {#(\<B>s ! i1)#}"
proof (cases "\<B>s ! i1 = \<B>s ! i2")
  case True
  then have "count (mset \<B>s) (\<B>s ! i1) \<ge> 2" using count_min_2_indices assms by fastforce
  then have "count ((mset \<B>s) - {#(\<B>s ! i1)#}) (\<B>s ! i1) \<ge> 1"
    by (metis Nat.le_diff_conv2 add_leD2 count_diff count_single nat_1_add_1) 
  then show ?thesis
    by (metis True count_inI not_one_le_zero)
next
  case False
  have "\<B>s ! i2 \<in># \<B>" using assms
    by simp 
  then show ?thesis using False
    by (metis in_remove1_mset_neq)
qed

lemma inter_num_points_filter_def: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "card {x \<in> {0..<\<v>} . ((\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2)) } = (\<B>s ! j1) |\<inter>| (\<B>s ! j2)"
proof - 
  have inter: "\<And> v. v \<in> \<V> \<Longrightarrow> v \<in> (\<B>s ! j1) \<and> v \<in> (\<B>s ! j2) \<longleftrightarrow> v \<in> (\<B>s ! j1) \<inter> (\<B>s ! j2)"
    by simp 
  obtain bl1 bl2 where bl1in: "bl1 \<in># \<B>" and bl1eq: "\<B>s ! j1 = bl1" and bl2in: "bl2 \<in># \<B> - {#bl1#}" and bl2eq: "\<B>s ! j2 = bl2" 
    using assms obtains_two_diff_index
    by (metis blocks_index_ne_belong size_mset valid_blocks_index) 
  have "card {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) } = card {v \<in> \<V> . v \<in> (\<B>s ! j1) \<and> v \<in> (\<B>s ! j2) }" 
    using card_filter_point_indices by simp
  also have "... = card {v \<in> \<V> . v \<in> bl1 \<and> v \<in> bl2 }" using bl1eq bl2eq by simp
  finally show ?thesis using points_inter_num_rep bl1in bl2in
    by (simp add: bl1eq bl2eq) 
qed

lemma scalar_prod_inc_vec_mat_inter_num: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "(col N j1) \<bullet> (col N j2) = mat_inter_num N j1 j2"
proof -
  have split: "{0..<\<v>} = {i \<in> {0..<\<v>} . (N $$ (i, j1) = 1) \<and> (N $$ (i, j2) = 1) } \<union> 
    {i \<in> {0..<\<v>} . N $$ (i, j1) = 0 \<or> N $$ (i, j2) = 0}" using assms N_not_zero_simp by auto
  have inter: "{i \<in> {0..<\<v>} . (N $$ (i, j1) = 1) \<and> (N $$ (i, j2) = 1) } \<inter> 
    {i \<in> {0..<\<v>} . N $$ (i, j1) = 0 \<or> N $$ (i, j2) = 0} = {}" by auto
  have "(col N j1) \<bullet> (col N j2) = (\<Sum> i \<in> {0..<\<v>} . (col N j1) $ i * (col N j2) $ i)" 
    using assms dim_vec_N_col scalar_prod_def by (metis (full_types) dim_vec_col) 
  also have "... = (\<Sum> i \<in> {0..<\<v>} . N $$ (i, j1) * N $$ (i, j2))" 
    using N_carrier_mat assms by simp
  also have "... = (\<Sum> i \<in> {i \<in> {0..<\<v>} . (N $$ (i, j1) = 1) \<and> (N $$ (i, j2) = 1) } . N $$ (i, j1) * N $$ (i, j2)) 
      + (\<Sum> i \<in> {i \<in> {0..<\<v>} . N $$ (i, j1) = 0 \<or> N $$ (i, j2) = 0} . N $$ (i, j1) * N $$ (i, j2))" 
    using split inter sum.union_disjoint[of " {i \<in> {0..<\<v>} . (N $$ (i, j1) = 1) \<and> (N $$ (i, j2) = 1) }" 
        "{i \<in> {0..<\<v>} . N $$ (i, j1) = 0 \<or> N $$ (i, j2) = 0}" "\<lambda> i . N $$ (i, j1) * N $$ (i, j2)"]
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan) 
  also have "... = (\<Sum> i \<in> {i \<in> {0..<\<v>} . (N $$ (i, j1) = 1) \<and> (N $$ (i, j2) = 1) } . 1) 
      + (\<Sum> i \<in> {i \<in> {0..<\<v>} . N $$ (i, j1) = 0 \<or> N $$ (i, j2) = 0} . 0)" 
    using sum.cong  by (smt (z3) mem_Collect_eq mult_cancel_right1 mult_eq_0_iff) 
  finally have "(col N j1) \<bullet> (col N j2) = card {i . i < \<v> \<and> (N $$ (i, j1) = 1) \<and> (N $$ (i, j2) = 1) }"
    by simp 
  then show ?thesis using mat_inter_num_def N_carrier_mat assms
    by (metis (no_types, lifting) Collect_cong dim_row_is_v) 
qed

lemma scalar_prod_inc_vec_inter_num: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "(col N j1) \<bullet> (col N j2) = (\<B>s ! j1) |\<inter>| (\<B>s ! j2)"
  using scalar_prod_inc_vec_mat_inter_num assms mat_inter_num_conv N_carrier_mat by simp

lemma inc_matrix_col_block: 
  assumes "c \<in> set (cols N)"
  shows "(\<lambda> x. \<V>s ! x) ` (mat.map_col_to_block c) \<in># \<B>"
proof -
  obtain j where "c = col N j" and "j < \<b>" using assms
    by (metis cols_length cols_nth in_mset_conv_nth ordered_incidence_system.dim_col_b_lt_iff 
        ordered_incidence_system_axioms set_mset_mset) 
  thus ?thesis
    using matrix_col_in_blocks by blast 
qed

lemma inc_mat_ordered_blocks_Bs: "map (\<lambda> x. ((!) \<V>s) ` x) (mat.map_to_blocks_ordered) = \<B>s"
proof (auto simp add: list_eq_iff_nth_eq)
  show lengtheq: "length (zero_one_matrix.map_to_blocks_ordered N) = length \<B>s"
    by (simp add: mat.dim_col_length inc_mat_dim_col) 
  show "\<And>j i.
       j < length (zero_one_matrix.map_to_blocks_ordered N) \<Longrightarrow> i \<in> zero_one_matrix.map_to_blocks_ordered N ! j \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
  proof -
    fix j i
    assume jlt: "j < length (zero_one_matrix.map_to_blocks_ordered N)"
    assume "i \<in> zero_one_matrix.map_to_blocks_ordered N ! j"
    then have "i \<in> map (\<lambda> c . mat.map_col_to_block c) (cols N) ! j" by (simp add: mat.map_to_blocks_ordered_def)
    then have "i \<in> mat.map_col_to_block (cols N ! j)"
      by (metis jlt length_map mat.map_to_blocks_ordered_def nth_map) 
    then have xain: "i \<in> mat.map_col_to_block (col N j)" using jlt
      by (metis cols_length cols_nth length_map mat.map_to_blocks_ordered_def) 
    then have "N $$ (i, j) = 1" using mat.M_def_from_lists
      by (metis mat.dim_col_length mat.in_map_col_valid_index_M jlt mat.map_blocks_ordered_nth mat.map_points_ordered_nth) 
    then show "\<V>s ! i \<in> \<B>s ! j"
      by (metis lengtheq xain mat.dim_col_length mat.in_map_col_valid_index_M inc_mat_dim_row inc_matrix_point_in_block jlt) 
  qed
  show "\<And>i x. i < length (zero_one_matrix.map_to_blocks_ordered N) \<Longrightarrow>
           x \<in> \<B>s ! i \<Longrightarrow> x \<in> (!) \<V>s ` zero_one_matrix.map_to_blocks_ordered N ! i"
  proof -
    fix j x
    assume jl:"j < length (zero_one_matrix.map_to_blocks_ordered N)"
    then have jlt: "j < \<b>"
      using blocks_list_length lengtheq by metis
    assume "x \<in> \<B>s ! j"
    then have xin:  "x \<in> ((!) \<V>s) ` (mat.map_col_to_block (col N j))" using matrix_col_to_block_v2 jlt by simp
    then have "(!) \<V>s ` (zero_one_matrix.map_to_blocks_ordered N ! j) = (!) \<V>s ` ((map (\<lambda> c . mat.map_col_to_block c) (cols N)) !j)" 
      by (simp add: mat.map_to_blocks_ordered_def)
    also have "... = (!) \<V>s ` ( mat.map_col_to_block (cols N ! j))" 
      by (metis jl length_map mat.map_to_blocks_ordered_def nth_map) 
    finally have "(!) \<V>s ` (zero_one_matrix.map_to_blocks_ordered N ! j) = (!) \<V>s ` (mat.map_col_to_block (col N j))" using jl
      by (metis cols_length cols_nth length_map mat.map_to_blocks_ordered_def) 
    then show "x \<in> (!) \<V>s ` zero_one_matrix.map_to_blocks_ordered N ! j"
      by (simp add: xin) 
  qed
qed

lemma inc_matrix_blocks: "image_mset (\<lambda> bl. ((!) \<V>s) ` bl) (mat.map_to_blocks) = \<B>"
proof -
  have "image_mset (\<lambda> bl. ((!) \<V>s) ` bl) (mat.map_to_blocks) = mset (map (\<lambda> x. ((!) \<V>s) ` x) (mat.map_to_blocks_ordered)) "
    by (simp add: mat.map_to_blocks_ordered_set)
  also have "... = mset (\<B>s)"using inc_mat_ordered_blocks_Bs by simp
  finally have "image_mset (\<lambda> bl. ((!) \<V>s) ` bl) (mat.map_to_blocks) = \<B>"
    by (simp)
  thus ?thesis by simp
qed

(* Complement is flipped matrix *)

lemma map_block_complement_entry: "j < \<b> \<Longrightarrow> (map block_complement \<B>s) ! j = block_complement (\<B>s ! j)"
  using blocks_list_length
  by (metis nth_map) 

lemma complement_mat_entries: 
  assumes "i < \<v>" and "j < \<b>"
  shows "(\<V>s ! i \<notin> \<B>s ! j) \<longleftrightarrow> (\<V>s ! i \<in> (map block_complement \<B>s) ! j)"
  using assms block_complement_def map_block_complement_entry valid_points_index by simp

lemma length_blocks_complement: "length (map block_complement \<B>s) = \<b>"
  by auto 

lemma ordered_complement: "ordered_incidence_system \<V>s (map block_complement \<B>s)"
proof -
  interpret inc: finite_incidence_system \<V> "complement_blocks" (* does not retain notation ? *)
    by (simp add: complement_finite)
  have "map inc.block_complement \<B>s \<in> permutations_of_multiset complement_blocks"
    using complement_image by (simp add: permutations_of_multiset_def)
  then show ?thesis using ordered_incidence_sysI[of "\<V>" "complement_blocks" "\<V>s" "(map block_complement \<B>s)"]
    by (simp add: inc.finite_incidence_system_axioms points_indexing) 
qed

interpretation ordered_comp: ordered_incidence_system "\<V>s" "(map block_complement \<B>s)"
  using ordered_complement by simp

lemma complement_mat_entries_val: 
  assumes "i < \<v>" and "j < \<b>"
  shows "ordered_comp.N $$ (i, j) = (if \<V>s ! i \<in> \<B>s ! j then 0 else 1)"
proof -
  have cond: "(\<V>s ! i \<notin> \<B>s ! j) \<longleftrightarrow> (\<V>s ! i \<in> (map block_complement \<B>s) ! j)"
    using complement_mat_entries assms by simp
  then have "ordered_comp.N $$ (i, j) = (if (\<V>s ! i \<in> (map block_complement \<B>s) ! j) then 1 else 0)"
    using assms(1) assms(2) ordered_comp.matrix_point_in_block_one ordered_comp.matrix_point_not_in_block_iff by force 
  then show ?thesis using cond by (simp) 
qed

lemma ordered_complement_mat: "ordered_comp.N = mat \<v> \<b> (\<lambda> (i,j) . if (\<V>s ! i) \<in> (\<B>s ! j) then 0 else 1)"
proof (intro eq_matI)
  show "\<And>i j. i < dim_row (mat ordered_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1)) \<Longrightarrow>
           j < dim_col (mat ordered_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1)) \<Longrightarrow>
           ordered_comp.N $$ (i, j) =
           mat ordered_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1) $$ (i, j)" 
    using complement_mat_entries_val by fastforce   
  show "dim_row ordered_comp.N = dim_row (mat ordered_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1))"
    by (simp add: ordered_comp.dim_row_is_v)
  show " dim_col ordered_comp.N =
    dim_col (mat ordered_comp.\<v> \<b> (\<lambda>(i, j). if \<V>s ! i \<in> \<B>s ! j then 0 else 1)) "
    by (simp add: ordered_comp.dim_col_is_b)
qed

lemma ordered_complement_mat_map: "ordered_comp.N = map_mat (\<lambda>x. if x = 1 then 0 else 1) N"
proof (intro eq_matI)
  show "\<And>i j. i < dim_row (map_mat (\<lambda>x. if x = 1 then 0 else 1) N) \<Longrightarrow>
           j < dim_col (map_mat (\<lambda>x. if x = 1 then 0 else 1) N) \<Longrightarrow>
           ordered_comp.N $$ (i, j) = map_mat (\<lambda>x. if x = 1 then 0 else 1) N $$ (i, j)"
    using  complement_same_b dim_col_is_b dim_row_is_v index_map_mat(1) 
        index_map_mat(2) index_map_mat(3) ordered_complement ordered_incidence_system.complement_mat_entries 
        ordered_incidence_system.matrix_point_in_block_iff ordered_incidence_system.matrix_point_not_in_block_iff
        ordered_incidence_system_axioms
    using complement_mat_entries_val by auto
  show "dim_row ordered_comp.N = dim_row (map_mat (\<lambda>x. if x = 1 then 0 else 1) N)"
    by (simp add: dim_row_is_v ordered_comp.dim_row_is_v)
  show "dim_col ordered_comp.N = dim_col (map_mat (\<lambda>x. if x = 1 then 0 else 1) N)"
    by (simp add: dim_col_is_b ordered_comp.dim_col_is_b)
qed

(* Alternative incidence matrix reps *)

lemma alt_ordering_sysI: "Vs \<in> permutations_of_set \<V> \<Longrightarrow> Bs \<in> permutations_of_multiset \<B> \<Longrightarrow> ordered_incidence_system Vs Bs"
  using ordered_incidence_sysI ordered_incidence_system.wf_list permutations_of_setD(2) by (unfold_locales) blast

end

lemma inc_sys_ordered_permI: 
  assumes "incidence_system V B" and "Vs \<in> permutations_of_set V" and "Bs \<in> permutations_of_multiset B" 
  shows "ordered_incidence_system Vs Bs"
proof -
  have bset: "mset Bs = B" using assms(3) permutations_of_multisetD by auto
  have vset: "set Vs = V" using assms(2) permutations_of_setD(1) by auto
  interpret inc: incidence_system V B using assms by simp
  show ?thesis proof (unfold_locales)
    show "\<And>b. b \<in># mset Bs \<Longrightarrow> b \<subseteq> set Vs" using inc.wellformed vset bset by simp
    show "distinct Vs" using assms(2)permutations_of_setD(2) by auto 
  qed
qed

lemma inc_sys_orderedI: 
  assumes "incidence_system V B" and "distinct Vs" and "set Vs = V" and "mset Bs = B" 
  shows "ordered_incidence_system Vs Bs"
proof -
  interpret inc: incidence_system V B using assms by simp
  show ?thesis proof (unfold_locales)
    show "\<And>b. b \<in># mset Bs \<Longrightarrow> b \<subseteq> set Vs" using inc.wellformed assms by simp
    show "distinct Vs" using assms(2)permutations_of_setD(2) by auto 
  qed
qed

(* Lemma exists incidence matrix *)

definition is_incidence_matrix :: "int mat \<Rightarrow> 'a set \<Rightarrow> 'a set multiset \<Rightarrow> bool" where
"is_incidence_matrix \<N> V B \<longleftrightarrow> (\<exists> Vs Bs . (Vs \<in> permutations_of_set V \<and> Bs \<in> permutations_of_multiset B \<and> \<N> = (inc_mat_of Vs Bs)))"

lemma (in incidence_system) is_incidence_mat_alt: "is_incidence_matrix \<N> \<V> \<B> \<longleftrightarrow>  (\<exists> Vs Bs . (ordered_incidence_system Vs Bs \<and> \<N> = (inc_mat_of Vs Bs)))"
  apply (auto simp add: is_incidence_matrix_def)
  oops

lemma (in ordered_incidence_system) is_incidence_mat_true: "is_incidence_matrix N \<V> \<B> = True"
  using blocks_indexing is_incidence_matrix_def points_indexing by blast


locale ordered_design = ordered_incidence_system \<V>s \<B>s + design "set \<V>s" "mset \<B>s" 
  for \<V>s and \<B>s
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

lemma (in ordered_design) all_cols_non_empty: "j < dim_col N \<Longrightarrow> non_empty_col N j"
  using blocks_nempty non_empty_col_map_conv dim_col_is_b
  by simp 
end

locale ordered_simple_design = ordered_design \<V>s \<B>s + simple_design "(set \<V>s)" "mset \<B>s" for \<V>s \<B>s
begin

lemma block_list_distinct: "distinct \<B>s"
  using block_mset_distinct by auto
  

lemma distinct_cols_N: "distinct (cols N)"
proof -
  have "inj_on (\<lambda> bl . inc_vec_of \<V>s bl) (set \<B>s)" using inc_vec_eq_iff_blocks 
    by (simp add: inc_vec_eq_iff_blocks inj_on_def) 
  then show ?thesis using distinct_map inc_mat_of_cols_inc_vecs block_list_distinct
    by (simp add: distinct_map inc_mat_of_cols_inc_vecs ) 
qed

lemma simp_blocks_length_card: "length \<B>s = card (set \<B>s)"
  using design_support_def simple_block_size_eq_card by fastforce

lemma blocks_index_inj_on: "inj_on (\<lambda> i . \<B>s ! i) {0..<length \<B>s}"
  apply (auto simp add: inj_on_def)
  by (metis simp_blocks_length_card card_distinct nth_eq_iff_index_eq)

lemma x_in_block_set_img: assumes "x \<in> set \<B>s" shows "x \<in> (!) \<B>s ` {0..<length \<B>s}"
proof -
  obtain i where "\<B>s ! i = x" and "i < length \<B>s" using assms
    by (meson in_set_conv_nth) 
  thus ?thesis by auto
qed

lemma blocks_index_simp_bij_betw: "bij_betw (\<lambda> i . \<B>s ! i) {0..<length \<B>s} (set \<B>s)"
  using blocks_index_inj_on x_in_block_set_img by (auto simp add: bij_betw_def) 

lemma blocks_index_simp_unique: 
  assumes "i1 < length \<B>s"
  assumes "i2 < length \<B>s" 
  assumes "i1 \<noteq> i2"
  shows "\<B>s ! i1 \<noteq> \<B>s ! i2"
  using block_list_distinct assms nth_eq_iff_index_eq by blast 

end

locale ordered_proper_design = ordered_design \<V>s \<B>s + proper_design "set \<V>s" "mset \<B>s" 
  for \<V>s and \<B>s
begin
lemma mat_is_proper: "proper_inc_mat N"
  using design_blocks_nempty v_non_zero by (auto simp add: proper_inc_mat_def dim_row_is_v dim_col_is_b)
end

locale ordered_constant_rep = ordered_proper_design \<V>s \<B>s + constant_rep_design "set \<V>s" "mset \<B>s" \<r> 
  for \<V>s and \<B>s and \<r>

begin

lemma incidence_mat_rep_num: 
  assumes "i < \<v>"
  shows "count_vec (row N i) 1 = \<r>"
  using point_rep_mat_row rep_number assms valid_points_index by auto 

lemma incidence_mat_rep_num_sum: 
  assumes "i < \<v>"
  shows "sum_vec (row N i) = \<r>"
  using  incidence_mat_rep_num  assms point_rep_mat_row point_rep_mat_row_sum by presburger 

lemma transpose_N_mult_diag: 
  assumes "i = j" and "i < \<v>" and "j < \<v>" 
  shows "(N * N\<^sup>T) $$ (i, j) = \<r>"
proof -
  have unsq: "\<And> k . k < \<b> \<Longrightarrow> (N $$ (i, k))^2 = N $$ (i, k)"
    using assms(2) matrix_elems_one_zero by fastforce
  then have "(N * N\<^sup>T) $$ (i, j) = (\<Sum>k \<in>{0..<\<b>} . N $$ (i, k) * N $$ (j, k))"
    using assms(2) assms(3) transpose_mat_mult_entries[of "i" "N" "j"]
    by (simp add: dim_row_is_v dim_col_is_b) 
  also have "... = (\<Sum>k \<in>{0..<\<b>} . (N $$ (i, k))^2)" using assms(1)
    by (simp add: power2_eq_square)
  also have "... = (\<Sum>k \<in>{0..<\<b>} . N $$ (i, k))"
    by (meson atLeastLessThan_iff sum.cong unsq) 
  also have "... = (\<Sum>k \<in>{0..<\<b>} . (row N i) $ k)"
    using assms(2) dim_col_is_b dim_row_is_v by auto 
  finally have "(N * N\<^sup>T) $$ (i, j) = sum_vec (row N i)" using sum_vec_def
    by (simp add: sum_vec_def dim_col_is_b)
  thus ?thesis using incidence_mat_rep_num_sum
    using assms(2) by presburger 
qed

end

locale ordered_block_design = ordered_proper_design \<V>s \<B>s + block_design "set \<V>s" "mset \<B>s" \<k>
  for \<V>s and \<B>s and \<k>

begin 

(* Every col has k ones *)
lemma incidence_mat_block_size:
  assumes "j < \<b>"
  shows "count_vec (col N j) 1 = \<k>"
  using block_size_mat_rep uniform assms valid_blocks_index by fastforce

lemma incidence_mat_block_size_sum:
  assumes "j < \<b>"
  shows "sum_vec (col N j) = \<k>"
  using count_vec_sum_ones_alt incidence_mat_block_size mat_col_elems
  by (metis assms) 

lemma ones_mult_incidence_mat_k_index: 
  assumes "j < \<b>"
  shows "((u\<^sub>v \<v>) \<^sub>v* N) $ j = \<k>"
  using ones_incidence_mat_block_size uniform
  by (metis assms valid_blocks_index) 

lemma ones_mult_incidence_mat_k: "((u\<^sub>v \<v>) \<^sub>v* N) = \<k> \<cdot>\<^sub>v (u\<^sub>v \<b>)"
  using ones_mult_incidence_mat_k_index dim_col_is_b by (intro eq_vecI) (simp_all)


end

locale ordered_incomplete_design = ordered_block_design \<V>s \<B>s \<k> + incomplete_design \<V> \<B> \<k>
  for \<V>s and \<B>s and \<k>

begin 
lemma incidence_mat_incomplete: 
  assumes "j < \<b>"
  shows "0 \<in>$ (col N j)"
  using assms valid_blocks_index incomplete_block_col incomplete_imp_incomp_block by blast 

end

locale ordered_t_wise_balance = ordered_proper_design \<V>s \<B>s + t_wise_balance "set \<V>s" "mset \<B>s" \<t> \<Lambda>\<^sub>t
  for \<V>s and \<B>s and \<t> and \<Lambda>\<^sub>t

begin

lemma incidence_mat_des_index: 
  assumes "I \<subseteq> {0..<\<v>}"
  assumes "card I = \<t>"
  shows "card {j \<in> {0..<\<b>} . (\<forall> i \<in> I . N $$(i, j) = 1)} = \<Lambda>\<^sub>t"
proof -
  have card: "card ((!) \<V>s ` I) = \<t>" using assms points_indexing_inj
    by (metis (mono_tags, lifting) card_image ex_nat_less_eq not_le points_list_length subset_iff) 
  have "((!) \<V>s ` I) \<subseteq> \<V>" using assms
    by (metis atLeastLessThan_iff image_subset_iff subsetD valid_points_index)
  then have "\<B> index ((!) \<V>s ` I) = \<Lambda>\<^sub>t" using balanced assms(2) card by simp
  thus ?thesis using points_index_mat_rep assms(1) lessThan_atLeast0 by presburger 
qed

end

locale ordered_pairwise_balance = ordered_t_wise_balance \<V>s \<B>s 2 \<Lambda> + pairwise_balance "set \<V>s" "mset \<B>s" \<Lambda>
  for \<V>s and \<B>s and \<Lambda>
begin

lemma incidence_mat_des_two_index: 
  assumes "i1 < \<v>"
  assumes "i2 < \<v>"
  assumes "i1 \<noteq> i2"
  shows "card {j \<in> {0..<\<b>} . N $$(i1, j) = 1 \<and> N $$ (i2, j) = 1} = \<Lambda>"
  using incidence_mat_des_index incidence_mat_two_index 
proof -
  have "\<V>s ! i1 \<noteq> \<V>s ! i2" using assms(3)
    by (simp add: assms(1) assms(2) distinct nth_eq_iff_index_eq points_list_length) 
  then have pair: "card {\<V>s ! i1, \<V>s ! i2} = 2" using card_2_iff by blast
  have "{\<V>s ! i1, \<V>s ! i2} \<subseteq> \<V>" using assms
    by (simp add: valid_points_index) 
  then have "\<B> index {\<V>s ! i1, \<V>s ! i2} = \<Lambda>" using pair
    using balanced by blast 
  thus ?thesis using incidence_mat_two_index assms by simp
qed

lemma transpose_N_mult_off_diag: 
  assumes "i \<noteq> j" and "i < \<v>" and "j < \<v>"
  shows "(N * N\<^sup>T) $$ (i, j) = \<Lambda>"
proof -
  have rev: "\<And> k. k \<in> {0..<\<b>} \<Longrightarrow> \<not> (N $$ (i, k) = 1 \<and> N $$ (j, k) = 1) \<longleftrightarrow> N $$ (i, k) = 0 \<or> N $$ (j, k) = 0"
    using assms matrix_elems_one_zero by auto
  then have split: "{0..<\<b>} = {k \<in> {0..<\<b>}. N $$ (i, k) = 1 \<and> N $$ (j, k) = 1} \<union> {k \<in> {0..<\<b>}. N $$ (i, k) = 0 \<or> N $$ (j, k) = 0}"
    by blast
  have zero: "\<And> k . k \<in> {0..<\<b>} \<Longrightarrow> N $$ (i, k) = 0 \<or> N $$ (j, k) = 0 \<Longrightarrow> N $$ (i, k) * N$$ (j, k) = 0"
    by simp 
  have djnt: "{k \<in> {0..<\<b>}. N $$ (i, k) = 1 \<and> N $$ (j, k) = 1} \<inter> {k \<in> {0..<\<b>}. N $$ (i, k) = 0 \<or> N $$ (j, k) = 0} = {}" using rev by auto
  have fin1: "finite {k \<in> {0..<\<b>}. N $$ (i, k) = 1 \<and> N $$ (j, k) = 1}" by simp
  have fin2: "finite {k \<in> {0..<\<b>}. N $$ (i, k) = 0 \<or> N $$ (j, k) = 0}" by simp
  have "(N * N\<^sup>T) $$ (i, j) = (\<Sum>k \<in>{0..<\<b>} . N $$ (i, k) * N $$ (j, k))"
    using assms(2) assms(3) transpose_mat_mult_entries[of "i" "N" "j"]
    by (simp add: dim_row_is_v dim_col_is_b)
  also have "... = (\<Sum>k \<in>({k' \<in> {0..<\<b>}. N $$ (i, k') = 1 \<and> N $$ (j, k') = 1} \<union> {k' \<in> {0..<\<b>}. N $$ (i, k') = 0 \<or> N $$ (j, k') = 0}) . N $$ (i, k) * N $$ (j, k))"
    using split by metis
  also have "... = (\<Sum>k \<in>{k' \<in> {0..<\<b>}. N $$ (i, k') = 1 \<and> N $$ (j, k') = 1} . N $$ (i, k) * N $$ (j, k)) + 
    (\<Sum>k \<in>{k' \<in> {0..<\<b>}. N $$ (i, k') = 0 \<or> N $$ (j, k') = 0} . N $$ (i, k) * N $$ (j, k))"
    using fin1 fin2 djnt sum.union_disjoint
    by blast 
  also have "... = card {k' \<in> {0..<\<b>}. N $$ (i, k') = 1 \<and> N $$ (j, k') = 1}" 
    by (simp add: zero) 
  finally have "(N * N\<^sup>T) $$ (i, j) = \<Lambda>" using incidence_mat_des_two_index assms by simp
  thus ?thesis by simp
qed

end

context pairwise_balance
begin

lemma ordered_pbdI: 
  assumes "\<B> = mset \<B>s" and "\<V> = set \<V>s" and "distinct \<V>s"
  shows "ordered_pairwise_balance \<V>s \<B>s \<Lambda>"
proof -
  interpret ois: ordered_incidence_system \<V>s \<B>s 
    using ordered_incidence_sysII assms finite_incidence_system_axioms by blast 
  show ?thesis using b_non_zero blocks_nempty assms t_lt_order balanced  by (unfold_locales)(simp_all)
qed
end

locale ordered_regular_pairwise_balance = ordered_pairwise_balance "\<V>s" "\<B>s" \<Lambda> + regular_pairwise_balance  "set \<V>s" "mset \<B>s" \<Lambda> \<r>
  for \<V>s and \<B>s and \<Lambda> and \<r>

sublocale ordered_regular_pairwise_balance \<subseteq> ordered_constant_rep
  by unfold_locales

context ordered_regular_pairwise_balance
begin

(* Theorem 1.15 Stinson *)
lemma rpbd_incidence_matrix_cond: "N * (N\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m \<v>) + (\<r> - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m \<v>)"
proof (intro eq_matI)
  fix i j
  assume ilt: "i < dim_row (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)" 
    and jlt: "j < dim_col (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
  then have "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = 
    (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) + (int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j)" 
    by simp
  then have split: "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = 
    (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) + (\<r> - \<Lambda>) * ((1\<^sub>m \<v>) $$ (i, j))"
    using ilt jlt by simp
  have lhs: "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) = \<Lambda>" using ilt jlt by simp
  show "(N * N\<^sup>T) $$ (i, j) = (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j)"
  proof (cases "i = j")
    case True
    then have rhs: "(int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = (\<r> - \<Lambda>)" using ilt by fastforce 
    have "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = \<Lambda> + (\<r> - \<Lambda>)"
      using True jlt by auto
    then have "(int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = \<r>" 
      using reg_index_lt_rep by (simp add: nat_diff_split)
    then show ?thesis using lhs split rhs True transpose_N_mult_diag ilt jlt by simp
  next
    case False
    then have "(1\<^sub>m \<v>) $$ (i, j) = 0" using ilt jlt by simp
    then have "(\<r> - \<Lambda>) * ((1\<^sub>m \<v>) $$ (i, j)) = 0" using ilt jlt
      by (simp add: \<open>1\<^sub>m \<v> $$ (i, j) = 0\<close>) 
    then show ?thesis using lhs transpose_N_mult_off_diag ilt jlt False by simp
  qed
next
  show "dim_row (N * N\<^sup>T) = dim_row (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
    using transpose_N_mult_dim(1) by auto
next
  show "dim_col (N * N\<^sup>T) = dim_col (int \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + int (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
    using transpose_N_mult_dim(1) by auto
qed
end

locale ordered_bibd = ordered_proper_design \<V>s \<B>s + bibd "set \<V>s" "mset \<B>s" \<k> \<Lambda> 
  for \<V>s and \<B>s and \<k> and \<Lambda>

sublocale ordered_bibd \<subseteq> ordered_incomplete_design
  by unfold_locales

sublocale ordered_bibd \<subseteq> ordered_constant_rep \<V>s \<B>s \<r>
  by unfold_locales

sublocale ordered_bibd \<subseteq> ordered_pairwise_balance
  by unfold_locales

locale ordered_sym_bibd = ordered_bibd \<V>s \<B>s \<k> \<Lambda> + symmetric_bibd "set \<V>s" "mset \<B>s" \<k> \<Lambda> 
  for \<V>s and \<B>s and \<k> and \<Lambda>


sublocale ordered_sym_bibd \<subseteq> ordered_simple_design
  by (unfold_locales)

locale ordered_const_intersect_design = ordered_proper_design \<V>s \<B>s + const_intersect_design "set \<V>s" "mset \<B>s" \<m>
  for \<V>s \<B>s \<m>


locale simp_ordered_const_intersect_design = ordered_const_intersect_design + ordered_simple_design
begin 
lemma max_one_block_size_inter: 
  assumes "\<b> \<ge> 2"
  assumes "bl \<in># \<B>"
  assumes "card bl = \<m>"
  assumes "bl2 \<in># \<B> - {#bl#}"
  shows "\<m> < card bl2"
proof -
  have sd: "simple_design \<V> \<B>"
    by (simp add: simple_design_axioms) 
  have bl2in: "bl2 \<in># \<B>" using assms(4)
    by (meson in_diffD)
  have slt: "size {#b \<in># \<B> . card b = \<m>#} \<le> 1" using simple_const_inter_iff sd assms(1) by simp
  have "bl \<in># {#b \<in># \<B> . card b = \<m>#}" using assms(3) assms(2) by simp
  then have "bl2 \<notin># {#b \<in># \<B> . card b = \<m>#}" using slt
    by (smt (verit) Multiset.set_mset_filter add_mset_eq_singleton_iff assms(4) diff_empty diff_is_0_eq' 
empty_not_add_mset filter_diff_mset filter_empty_mset filter_mset_add_mset insert_DiffM insert_noteq_member 
mem_Collect_eq mset_add multi_member_split multi_nonempty_split multi_self_add_other_not_self 
set_mset_empty size_Diff_singleton size_eq_0_iff_empty) 
  then have ne: "card bl2 \<noteq> \<m>" using bl2in by auto 
  thus ?thesis using inter_num_le_block_size assms bl2in
    using nat_less_le by presburger 
qed

lemma block_size_inter_num_cases:
  assumes "bl \<in># \<B>"
  assumes "\<b> \<ge> 2"
  shows "\<m> < card bl \<or> (card bl = \<m> \<and> (\<forall> bl' \<in># (\<B> - {#bl#}) . \<m> < card bl'))"
proof (cases "card bl = \<m>")
  case True
  have "(\<And> bl'. bl' \<in># (\<B> - {#bl#}) \<Longrightarrow> \<m> < card bl')"
    using max_one_block_size_inter True assms by simp
  then show ?thesis using True by simp
next
  case False
  then have "\<m> < card bl" using assms inter_num_le_block_size nat_less_le by presburger
  then show ?thesis by simp
qed

lemma indexed_const_intersect: 
  assumes "j1 < \<b>"
  assumes "j2 < \<b>"
  assumes "j1 \<noteq> j2"
  shows "(\<B>s ! j1) |\<inter>| (\<B>s ! j2) = \<m>"
proof -
  obtain bl1 bl2 where "bl1 \<in># \<B>" and "\<B>s ! j1 = bl1" and "bl2 \<in># \<B> - {#bl1#}" and "\<B>s ! j2 = bl2" 
    using obtains_two_diff_index assms
    by fastforce 
  thus ?thesis by (simp add: const_intersect)
qed

lemma scalar_prod_inc_vec_const_inter: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "(col N j1) \<bullet> (col N j2) = \<m>"
  using scalar_prod_inc_vec_inter_num indexed_const_intersect assms by simp

end

context zero_one_matrix
begin

lemma mat_is_ordered_incidence_sys: "ordered_incidence_system map_to_points_ordered map_to_blocks_ordered"
  apply (unfold_locales)
  by (simp_all add: map_to_blocks_ordered_set map_to_points_ordered_set 
      mat_to_blocks_wf map_to_points_ordered_distinct)

lemma transpose_cond_index_vals: 
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "i < dim_row (M * (M\<^sup>T))"
  assumes "j < dim_col (M * (M\<^sup>T))"
  shows "i = j \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = r" "i \<noteq> j \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = \<Lambda>"
  using assms by auto

lemma transpose_cond_diag_r:
  assumes "i < dim_row (M * (M\<^sup>T))"
  assumes "\<And> j. i = j \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = r"
  shows "sum_vec (row M i) = r"
proof -
  have eqr: "(M * M\<^sup>T) $$ (i, i) = r" using assms(2)
    by simp
  have unsq: "\<And> k . k < dim_col M \<Longrightarrow> (M $$ (i, k))^2 = M $$ (i, k)"
    using assms elems_are_one_zero by fastforce
  have "sum_vec (row M i) = (\<Sum>k \<in>{0..<(dim_col M)} . (row M i) $ k)"
    using assms by (simp add: sum_vec_def)
  also have "... = (\<Sum>k \<in>{0..<(dim_col M)} . M $$ (i, k))"
    using assms by auto
  also have "... = (\<Sum>k \<in>{0..<(dim_col M)} . M $$ (i, k)^2)"
    using atLeastLessThan_iff sum.cong unsq by simp
  also have "... = (\<Sum>k \<in>{0..<(dim_col M)} . M $$ (i, k) * M $$ (i, k))"
    using assms by (simp add: power2_eq_square)
  also have "... = (M * M\<^sup>T) $$ (i, i)" 
    using assms transpose_mat_mult_entries[of "i" "M" "i"] by simp
  finally have "sum_vec (row M i) = r" using eqr by simp
  thus ?thesis by simp
qed


lemma transpose_cond_non_diag:
  assumes "i1 < dim_row (M * (M\<^sup>T))"
  assumes "i2 < dim_row (M * (M\<^sup>T))"
  assumes "i1 \<noteq> i2"
  assumes "\<And> j i. j \<noteq> i \<Longrightarrow> i < dim_row (M * (M\<^sup>T)) \<Longrightarrow> j < dim_row (M * (M\<^sup>T)) \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = \<Lambda>"
  shows "\<Lambda> = card {j \<in> {0..<dim_col M} . M $$(i1, j) = 1 \<and> M $$ (i2, j) = 1}"
proof -
  have rev: "\<And> k. k \<in> {0..<dim_col M} \<Longrightarrow> \<not> (M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1) \<longleftrightarrow> M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0"
    using assms elems01 by fastforce 
  then have split: "{0..<dim_col M} = {k \<in> {0..<dim_col M}. M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1} \<union> {k \<in> {0..<dim_col M}. M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0}"
    by blast
  have zero: "\<And> k . k \<in> {0..<dim_col M} \<Longrightarrow> M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0 \<Longrightarrow> M $$ (i1, k) * M$$ (i2, k) = 0"
    by simp 
  have djnt: "{k \<in> {0..<dim_col M}. M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1} \<inter> {k \<in> {0..<dim_col M}. M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0} = {}" using rev by auto
  have fin1: "finite {k \<in> {0..<dim_col M}. M $$ (i1, k) = 1 \<and> M $$ (i2, k) = 1}" by simp
  have fin2: "finite {k \<in> {0..<dim_col M}. M $$ (i1, k) = 0 \<or> M $$ (i2, k) = 0}" by simp
  have "card {k' \<in> {0..<dim_col M}. M $$ (i1, k') = 1 \<and>M $$ (i2, k') = 1} = 
    (\<Sum>k \<in>{k' \<in> {0..<dim_col M}. M $$ (i1, k') = 1 \<and> M $$ (i2, k') = 1} . M $$ (i1, k) * M $$ (i2, k)) + 
    (\<Sum>k \<in>{k' \<in> {0..<dim_col M}. M $$ (i1, k') = 0 \<or> M $$ (i2, k') = 0} . M $$ (i1, k) * M $$ (i2, k))"
    by (simp add: zero)
  also have "... = (\<Sum>k \<in>({k' \<in> {0..<dim_col M}. M $$ (i1, k') = 1 \<and> M $$ (i2, k') = 1} \<union> 
    {k' \<in> {0..<dim_col M}. M $$ (i1, k') = 0 \<or> M $$ (i2, k') = 0}) . M $$ (i1, k) * M $$ (i2, k))"
    using fin1 fin2 djnt sum.union_disjoint by (metis (no_types, lifting)) 
  also have "... =  (\<Sum>k \<in>{0..<dim_col M} . M $$ (i1, k) * M $$ (i2, k))"
    using split by metis
  finally have "card {k' \<in> {0..<dim_col M}. M $$ (i1, k') = 1 \<and>M $$ (i2, k') = 1} = (M * (M\<^sup>T)) $$ (i1, i2)"
    using assms(1) assms(2) transpose_mat_mult_entries[of "i1" "M" "i2"] by simp
  thus ?thesis using assms by simp
qed

lemma trans_cond_implies_map_rep_num:
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "x \<in> map_to_points"
  shows "map_to_blocks rep x = r"
proof -
  interpret ois: ordered_incidence_system map_to_points_ordered map_to_blocks_ordered 
    using mat_is_ordered_incidence_sys by simp
  obtain i where "x = (map_to_points_ordered ! i)" and "i < dim_row M"
    using assms(2) ois.valid_points_index_cons local.map_to_points_card map_to_points_ordered_set by auto 
  then have eq: "map_to_blocks rep x = sum_vec (row M i)" using ois.point_rep_mat_row_sum
    using local.map_to_points_card local.rev_map_points_blocks
    using local.map_to_blocks_ordered_set local.map_to_points_ordered_set by fastforce 
  then have "\<And> j. i = j \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = r" using assms(1) transpose_cond_index_vals
    by (metis \<open>i < dim_row M\<close> index_mult_mat(2) index_mult_mat(3) index_transpose_mat(3)) 
  thus ?thesis using eq transpose_cond_diag_r
    by (metis \<open>i < dim_row M\<close> index_mult_mat(2) of_nat_eq_iff) 
qed

lemma trans_cond_implies_map_index:
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "ps \<subseteq> map_to_points"
  assumes "card ps = 2"
  shows "map_to_blocks index ps = \<Lambda>"
proof - 
  interpret ois: ordered_incidence_system map_to_points_ordered map_to_blocks_ordered 
    using mat_is_ordered_incidence_sys by simp
  obtain x1 x2 where "x1 \<in> map_to_points" and "x2 \<in> map_to_points" and "ps = {x1, x2}"
    using assms(2) assms(3) by (metis card_2_iff insert_subset) 
  then have neqx: "x1 \<noteq> x2" using assms(3)
    by fastforce
  then obtain i1 i2 where "map_to_points_ordered ! i1 = x1" and "map_to_points_ordered ! i2 = x2" and "i1 < dim_row M" and "i2 < dim_row M"
    by (metis \<open>x1 \<in> local.map_to_points\<close> \<open>x2 \<in> local.map_to_points\<close> local.map_to_points_card 
        local.map_to_points_ordered_set ois.valid_points_index_cons)
  then have neqi: "i1 \<noteq> i2" using neqx
    by blast 
  have cond: "\<And> j i. j \<noteq> i \<Longrightarrow> i < dim_row (M * (M\<^sup>T)) \<Longrightarrow> j < dim_row (M * (M\<^sup>T)) \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = \<Lambda>"
    using assms(1) by simp
  then have "map_to_blocks index ps = card {j \<in> {0..<dim_col M} . M $$(i1, j) = 1 \<and> M $$ (i2, j) = 1}"
    using ois.incidence_mat_two_index \<open>Vs ! i1 = x1\<close> \<open>Vs ! i2 = x2\<close> \<open>i1 < dim_row M\<close> 
      \<open>i2 < dim_row M\<close> \<open>ps = {x1, x2}\<close> map_to_blocks_size map_to_points_card rev_map_points_blocks neqi
    using local.map_to_blocks_ordered_set local.map_to_points_ordered_set by fastforce 
  thus ?thesis using cond transpose_cond_non_diag \<open>i1 < dim_row M\<close> \<open>i2 < dim_row M\<close> index_mult_mat(2) 
      index_transpose_mat(2) neqi of_nat_eq_iff by fastforce 
qed

(* Stinson Theorem 1.15 *)
lemma rpbd_exists: 
  assumes "dim_row M \<ge> 2" (* Min two points *)
  assumes "dim_col M \<ge> 1" (* Min one block *)
  assumes "\<And> j. j < dim_col M \<Longrightarrow> 1 \<in>$ col M j" (*no empty blocks *)
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  shows "ordered_regular_pairwise_balance map_to_points_ordered map_to_blocks_ordered \<Lambda> r"
proof -
  interpret ois: ordered_incidence_system map_to_points_ordered map_to_blocks_ordered 
    using mat_is_ordered_incidence_sys by simp
  interpret pdes: ordered_design "map_to_points_ordered" "map_to_blocks_ordered"
    using assms(2) mat_is_design assms(3)
    by (simp add: local.map_to_blocks_ordered_set local.map_to_points_ordered_set ordered_design_def ois.ordered_incidence_system_axioms)  
  show ?thesis proof (unfold_locales, simp_all)
    show "Bs \<noteq> []"
      using assms(2) local.rev_map_points_blocks ois.dim_col_is_b by auto 
    show "2 \<le> ois.\<v>" using assms
      by (simp add: local.map_to_points_card local.map_to_points_ordered_set) 
    show "\<And>ps. ps \<subseteq> ois.\<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> ois.\<B> index ps = \<Lambda>"
      using assms  trans_cond_implies_map_index
      by (simp add: local.map_to_blocks_ordered_set local.map_to_points_ordered_set) 
    show "\<And>x. x \<in> ois.\<V> \<Longrightarrow> ois.\<B> rep x = r" 
      using assms trans_cond_implies_map_rep_num by (simp add: local.map_to_blocks_ordered_set local.map_to_points_ordered_set) 
  qed
qed

lemma col_ones_sum_eq_block_size: 
  assumes "j < dim_col M"
  shows "card (map_col_to_block (col M j)) = sum_vec (col M j)"
proof -
  interpret ois: ordered_incidence_system map_to_points_ordered map_to_blocks_ordered 
    using mat_is_ordered_incidence_sys by simp
  show ?thesis 
    using assms map_blocks_ordered_nth ois.block_size_mat_rep_sum zero_one_matrix_axioms map_to_blocks_size rev_map_points_blocks
  by (metis dim_col_length ois.blocks_list_length)
qed

lemma vec_k_impl_uniform_block_size: 
  assumes "dim_row M \<ge> 2" (* Min two points *)
  assumes "dim_col M \<ge> 1" (* Min one block *)
  assumes "((u\<^sub>v (dim_row M)) \<^sub>v* M) = k \<cdot>\<^sub>v (u\<^sub>v (dim_col M))"
  assumes "k \<ge> 2" "k < dim_row M"
  assumes "bl \<in># map_to_blocks"
  shows "card bl = k"
proof -
  obtain j where jlt: "j < dim_col M" and bleq: "bl = map_col_to_block (col M j)"
    using assms(6) obtain_block_index by auto
  then have "card (map_col_to_block (col M j)) = sum_vec (col M j)" using jlt col_ones_sum_eq_block_size by simp
  also have "... = (\<Sum> i \<in> {0 ..< dim_row M}. (u\<^sub>v (dim_row M)) $ i * (col M j) $ i)" by (simp add: sum_vec_def)
  also have "... = ((u\<^sub>v (dim_row M)) \<^sub>v* M) $ j" using jlt by (simp add: scalar_prod_def)
  also have "... = (k \<cdot>\<^sub>v (u\<^sub>v (dim_col M))) $ j" using assms(3) jlt by simp
  finally have "card (map_col_to_block (col M j)) = k" using jlt by simp
  thus ?thesis using bleq by simp
qed

lemma bibd_exists: 
  assumes "dim_row M \<ge> 2" (* Min two points *)
  assumes "dim_col M \<ge> 1" (* Min one block *)
  assumes "\<And> j. j < dim_col M \<Longrightarrow> 1 \<in>$ col M j" (*no empty blocks *)
  assumes "M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m (dim_row M)) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m (dim_row M))"
  assumes "((u\<^sub>v (dim_row M)) \<^sub>v* M) = k \<cdot>\<^sub>v (u\<^sub>v (dim_col M))"
  assumes "(r ::nat) \<ge> 0"
  assumes "k \<ge> 2" "k < dim_row M"
  shows "ordered_bibd map_to_points_ordered map_to_blocks_ordered k \<Lambda>"
proof -
  interpret ois: ordered_incidence_system map_to_points_ordered map_to_blocks_ordered 
    using mat_is_ordered_incidence_sys by simp
  interpret ipbd: ordered_regular_pairwise_balance map_to_points_ordered map_to_blocks_ordered \<Lambda> r
    using rpbd_exists assms by simp
  show ?thesis proof (unfold_locales, simp_all add: assms)
    show "\<And>bl. bl \<in> set Bs \<Longrightarrow> card bl = k"
      using vec_k_impl_uniform_block_size assms
      by (metis local.map_to_blocks_ordered_set set_mset_mset) 
    show "k < ois.\<v>"
      using assms  local.map_to_points_card
      by (simp add: local.map_to_points_ordered_set) 
  qed
qed

end


(* Reasoning on isomorphisms *)


context ordered_incidence_system 
begin

(*"(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! i = (\<lambda>x. \<V>s' ! List_Index.index \<V>s x) ` (\<B>s ! i)"*)

lemma block_mat_cond_rep: 
  assumes "j < length \<B>s"
  shows "(\<B>s ! j) = {\<V>s ! i | i. i < length \<V>s \<and> N $$ (i, j) = 1}"
proof (intro subset_antisym subsetI)
  fix x 
  assume a: "x \<in> \<B>s ! j"
  then have "x \<in> \<V>"
    using assms nth_mem_mset wf_invalid_point by blast
  then obtain i where xeq: "x = \<V>s ! i" and ilt: "i < length \<V>s"
    using points_list_length valid_points_index_cons by auto 
  then have "\<V>s ! i \<in> \<B>s ! j" using a xeq by simp
  then have "N $$ (i, j) = 1" using assms ilt
    by (simp add: inc_matrix_point_in_block_iff) 
  then show "x\<in>{\<V>s ! i | i. i < length \<V>s \<and> N $$ (i, j) = 1}"
    using ilt xeq by blast 
next
  fix x assume "x \<in>  {\<V>s ! i | i. i < length \<V>s \<and> N $$ (i, j) = 1}"
  then obtain i where "x = \<V>s ! i" and "i < length \<V>s" and "N $$ (i, j) = 1" by blast
  then show "x \<in> (\<B>s ! j)" using assms
    by (simp add: \<open>N $$ (i, j) = 1\<close> inc_matrix_point_in_block) 
qed

lemma block_mat_cond_rep': "j < length \<B>s \<Longrightarrow> (\<B>s ! j) = ((!) \<V>s) ` {i . i < length \<V>s \<and> N $$ (i, j) = 1}"
  by (simp add: block_mat_cond_rep setcompr_eq_image)

lemma block_mat_cond_rev: 
  assumes "j < length \<B>s"
  shows "{i . i < length \<V>s \<and> N $$ (i, j) = 1} = ((List_Index.index) \<V>s) ` (\<B>s ! j)"
proof (intro Set.set_eqI iffI)
  fix i assume a1: "i \<in> {i. i < length \<V>s \<and> N $$ (i, j) = 1}"
  then have ilt1: "i < length \<V>s" and Ni1: "N $$ (i, j) = 1" by auto
  then obtain x where "\<V>s ! i = x" and "x \<in> (\<B>s ! j)"
    using assms inc_matrix_point_in_block by blast  
  then have "List_Index.index \<V>s x = i" using distinct  index_nth_id ilt1 by auto
  then show "i \<in> List_Index.index \<V>s ` \<B>s ! j" by (metis \<open>x \<in> \<B>s ! j\<close> imageI) 
next
  fix i assume a2: "i \<in> List_Index.index \<V>s ` \<B>s ! j"
  then obtain x where ieq: "i = List_Index.index \<V>s x" and xin: "x \<in> \<B>s !j"
    by blast 
  then have ilt: "i < length \<V>s"
    by (smt (z3) assms index_first index_le_size nat_less_le nth_mem_mset points_list_length valid_points_index_cons wf_invalid_point)
  then have "N $$ (i, j) = 1" using xin 
    by (metis ieq assms inc_matrix_point_in_block_one index_conv_size_if_notin less_irrefl_nat nth_index)
  then show "i \<in> {i. i < length \<V>s \<and> N $$ (i, j) = 1}" using ilt by simp
qed

end

locale two_ordered_sys = D1: ordered_incidence_system \<V>s \<B>s + D2: ordered_incidence_system \<V>s' \<B>s'
  for "\<V>s" and "\<B>s" and "\<V>s'" and "\<B>s'" 

begin

lemma equal_inc_mat_isomorphism: 
  assumes "D1.N = D2.N"
  shows "incidence_system_isomorphism D1.\<V> D1.\<B> D2.\<V> D2.\<B> (\<lambda> x . \<V>s' ! (List_Index.index \<V>s x))"
proof (unfold_locales)
  show "bij_betw (\<lambda>x. \<V>s' ! List_Index.index \<V>s x) D1.\<V> D2.\<V>" 
  proof -
    have comp: "(\<lambda>x. \<V>s' ! List_Index.index \<V>s x) = (\<lambda> i. \<V>s' ! i) \<circ> (\<lambda> y . List_Index.index \<V>s y)"
      by (simp add: comp_def)
    have leq: "length \<V>s = length \<V>s'" using assms
      using D1.dim_row_is_v D1.points_list_length D2.dim_row_is_v D2.points_list_length by force 
    have dis1: "distinct \<V>s"
      by (simp add: D1.distinct)  
    have dis2: "distinct \<V>s'" by (simp add: D2.distinct)
    have bij1: "bij_betw (\<lambda> i. \<V>s' !i) {..<length \<V>s} (set \<V>s') " using  leq
      by (simp add: bij_betw_nth dis2) 
    have "bij_betw (List_Index.index \<V>s) (set \<V>s) {..<length \<V>s}" using dis1
      by (simp add: bij_betw_index lessThan_atLeast0) 
    thus ?thesis using bij_betw_trans comp bij1 by simp
  qed
next
  have len:  "length (map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) = length \<B>s'"
    by (metis D1.inc_mat_ordered_blocks_Bs D2.inc_mat_ordered_blocks_Bs assms length_map) 
  have mat_eq: "\<And> i j . D1.N $$ (i, j) = D2.N $$ (i, j)" using assms
    by simp 
  have vslen: "length \<V>s = length \<V>s'" using assms
      using D1.dim_row_is_v D1.points_list_length D2.dim_row_is_v D2.points_list_length by force 
  have "\<And> j. j < length \<B>s' \<Longrightarrow> (map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = \<B>s' ! j"
  proof -
    fix j assume a: "j < length \<B>s'" 
    then have "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<lambda>x. \<V>s' ! List_Index.index \<V>s x) ` (\<B>s ! j)"
      by (metis D1.blocks_list_length D1.dim_col_is_b D2.blocks_list_length D2.dim_col_is_b assms nth_map) 
    also have "... = (\<lambda> i . \<V>s' ! i) ` ((\<lambda> x. List_Index.index \<V>s x) ` (\<B>s ! j))" 
      by blast
    also have "... = ((\<lambda> i . \<V>s' ! i) ` {i . i < length \<V>s \<and> D1.N $$ (i, j) = 1})" using D1.block_mat_cond_rev a
      by (metis (no_types, lifting)  D1.blocks_list_length D1.dim_col_is_b D2.blocks_list_length D2.dim_col_is_b assms) 
    also have "... = ((\<lambda> i . \<V>s' ! i) ` {i . i < length \<V>s' \<and> D2.N $$ (i, j) = 1})" using vslen mat_eq by simp
    finally have "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<B>s' ! j)" using D2.block_mat_cond_rep' a
      by presburger
    then show "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s) ! j = (\<B>s' ! j)" by simp
  qed
  then have "map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s = \<B>s'" 
    using len nth_equalityI[of "(map ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) \<B>s)" "\<B>s'"] by simp
  then show "image_mset ((`) (\<lambda>x. \<V>s' ! List_Index.index \<V>s x)) D1.\<B> = D2.\<B>"
    using mset_map by auto
qed

lemma equal_inc_mat_isomorphism_ex: 
  assumes "D1.N = D2.N"
  shows "\<exists> \<pi> . incidence_system_isomorphism D1.\<V> D1.\<B> D2.\<V> D2.\<B> \<pi>"
  using equal_inc_mat_isomorphism assms by auto 

lemma equal_inc_mat_isomorphism_obtain: 
  assumes "D1.N = D2.N"
  obtains \<pi> where "incidence_system_isomorphism D1.\<V> D1.\<B> D2.\<V> D2.\<B> \<pi>"
  using equal_inc_mat_isomorphism assms by auto 



end

end