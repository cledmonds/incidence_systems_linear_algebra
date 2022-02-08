(* Title: Fishers_Inequality_Variations.thy
   Author: Chelsea Edmonds
*)

theory Fishers_Inequality_Variations imports Dual_Systems Rank_Argument_General
Vector_Matrix_Mod Linear_Bound_Argument
begin

(* Matrix mod properties inc *)

context mat_mod
begin

lemma mat_mod_proper_iff:  "proper_inc_mat (mat_mod N)  \<longleftrightarrow> proper_inc_mat N"
  by (simp add: proper_inc_mat_def)

lemma mat_mod_rep_num_eq: 
  assumes "i < dim_row N"
  assumes "elements_mat N \<subseteq> {0..<m}"
  shows "mat_rep_num (mat_mod N) i = mat_rep_num N i"
  by (simp add: mat_mod_count_row_eq mat_rep_num_def assms)

lemma mat_point_index_eq: 
  assumes "\<And> i. i\<in> I \<Longrightarrow> i < dim_row N"
  assumes "elements_mat N \<subseteq> {0..<m}"
  shows "mat_point_index (mat_mod N) I = mat_point_index N I"
  by (simp add: assms(2) mat_mod_eq_cond) 

lemma mod_mat_inter_num_eq: 
  assumes "j1 < dim_col N" "j2 < dim_col N"
  assumes "elements_mat N \<subseteq> {0..<m}"
  shows "mat_inter_num (mat_mod N) j1 j2 = mat_inter_num N j1 j2"
  by (simp add: assms mat_mod_eq_cond) 

lemma mod_mat_block_size: 
  assumes "j < dim_col N"
  assumes "elements_mat N \<subseteq> {0..<m}"
  shows "mat_block_size (mat_mod N) j = mat_block_size N j"
  by (simp add: assms mat_mod_eq_cond) 
end


context mat_mod_type
begin


lemma mat_rep_num_MM_Rel: 
  assumes "MM_Rel A B"
  assumes "i < dim_row A"
  shows "mat_rep_num (mat_mod A) i = mat_rep_num B i"
  unfolding mat_rep_num_def using vec_count_MV_Rel_direct assms
  by (metis MM_Rel_def MV_Rel_def index_map_mat(2) mat_mod_dim(1) mat_mod_vec_mod_row row_map_mat to_int_mod_ring_hom.hom_one) 


lemma mat_block_size_MM_Rel: 
  assumes "MM_Rel A B"
  assumes " j < dim_col A"
  shows "mat_block_size (mat_mod A) j = mat_block_size B j"
  using vec_count_MV_Rel_direct assms MM_Rel_MV_Rel_col
  by (metis mat_mod_vec_mod_col to_int_mod_ring_hom.hom_one) 

lemma mat_inter_num_MM_Rel: 
  assumes "MM_Rel A B"
  assumes "j1 < dim_col A" "j2 < dim_col B"
  shows "mat_inter_num (mat_mod A) j1 j2 = mat_inter_num B j1 j2"
  unfolding mat_inter_num_def
  by (smt (z3) Collect_cong MM_Rel_def assms index_map_mat mat_mod_dim(2) to_int_mod_ring_hom.hom_1 to_int_mod_ring_hom.hom_one) 

end

locale even_town = ordered_simple_design +  
  assumes even_groups: "bl \<in># \<B> \<Longrightarrow> even (card bl)"
    and even_inters: "bl1 \<in># \<B> \<Longrightarrow> bl2 \<in># \<B> \<Longrightarrow> bl1 \<noteq> bl2 \<Longrightarrow> even (bl1 |\<inter>| bl2)"
begin
end

locale odd_town = ordered_design + 
  assumes odd_groups: "bl \<in># \<B> \<Longrightarrow> odd (card bl)"
  and even_inters: "bl1 \<in># \<B> \<Longrightarrow> bl2 \<in># (\<B> - {#bl1#})  \<Longrightarrow> even (bl1 |\<inter>| bl2)"
begin

lemma odd_town_no_repeat_clubs: "distinct_mset \<B>"
proof (rule ccontr)
  assume "\<not> distinct_mset \<B>"
  then obtain a where ain: "a \<in># \<B>" and countne: "count \<B> a \<noteq> 1"
    by (auto simp add: distinct_mset_def)
  then have "count \<B> a > 1"
    using nat_less_le by auto 
  then have ain2: "a \<in># (\<B> - {#a#})"
    by (simp add: in_diff_count) 
  then have "odd (a |\<inter>| a)" using odd_groups ain by simp
  thus False using even_inters ain ain2
    by blast 
qed

lemma odd_blocks_mat_block_size: 
  assumes "j < dim_col N"
  shows "odd (mat_block_size N j)"
  using mat_block_size_conv assms odd_groups 
  by (metis dim_col_is_b valid_blocks_index) 

lemma valid_indices_block_min: 
  assumes "j1 < dim_col N" "j2 < dim_col N"
  assumes "j1 \<noteq> j2"
  shows "\<b> \<ge> 2"
proof (rule ccontr)
  assume "\<not> (\<b> \<ge> 2)"
  then have "\<b> \<le> 1" by simp
  then have lt1: "dim_col N \<le> 1" by (simp add: dim_col_is_b)
  then have j1: "j1 = 0" using assms(1) by simp
  have "j2 = 0" using assms(2) lt1 by simp
  thus False using j1 assms(3) by simp
qed

lemma even_inter_mat_intersections: 
  assumes "j1 < dim_col N" "j2 < dim_col N"
  assumes "j1 \<noteq> j2"
  shows "even (mat_inter_num N j1 j2)"
  using even_inters mat_inter_num_conv assms dim_col_b_lt_iff obtains_two_diff_index valid_indices_block_min
  by (metis (mono_tags, lifting)) 

end

sublocale odd_town \<subseteq> ordered_simple_design
  using odd_town_no_repeat_clubs by (unfold_locales) (meson distinct_mset_def) 

context odd_town 
begin

lemma vec_scalar_prod_even_0: 
  fixes N2 :: "'b:: {prime_card} mod_ring mat"
  assumes "CARD('b) = 2"
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  assumes "N2 \<in> carrier_mat \<v> \<b>"
  assumes "N = to_int_mat N2"
  shows "(col N2 j1) \<bullet> (col N2 j2) = 0"
proof - 
  interpret mmt: mat_mod_type 2 "TYPE('b::prime_card)" 
    using assms by (unfold_locales) (simp_all)
  have nmm: "N = mmt.mat_mod N" using mmt.mat_mod_eq_cond mat.elems01 by auto
  then have mmrel: "mmt.MM_Rel N N2" using mmt.MM_Rel_def nmm assms by simp
  then have "N2 = map_mat (of_int_mod_ring) N" using assms
    by auto  
  have ev: "even (mat_inter_num N j1 j2)" 
    using assms even_inter_mat_intersections[of j1 j2] N_carrier_mat dim_col_is_b by simp
  have "mat_inter_num N2 j1 j2 = mat_inter_num N j1 j2" using mmt.mat_inter_num_MM_Rel mmrel nmm  N_carrier_mat
    by (metis dim_col_is_b index_map_mat(3) assms) 
  then have "even (int (mat_inter_num N2 j1 j2))" using ev by simp
  then have mod0: "of_int (mat_inter_num N2 j1 j2) = (0 :: 'b mod_ring)" by (transfer' fixing: \<V>s \<B>s N2 j1 j2, simp add: assms(1)) 
  then have  "elements_mat N2 = (of_int_mod_ring) `elements_mat N"
    by (simp add: \<open>N2 = map_mat of_int_mod_ring N\<close> map_mat_elements) 
  then have "elements_mat N2 \<subseteq> {(of_int 0),(of_int 1)}"
    using mat.elems01 by (auto simp add: of_int_of_int_mod_ring) 
  then have N2_elems_01: "elements_mat N2 \<subseteq> {0,1}"
    by simp 
  then have "\<And> i j. i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N2 $$ (i, j) \<noteq> 0 \<Longrightarrow> N2 $$ (i, j) = 1"
    using assms(5) by auto 
  then have split: "{0 ..< \<v>} = {l \<in> {0..< \<v>}. N2 $$ (l , j1) = 1 \<and> (N2 $$ (l, j2) = 1)} \<union> {l \<in> {0..< \<v>}. N2 $$ (l , j1) = 0 \<or> (N2 $$ (l, j2) = 0)}"
     using assms(2) assms(3) assms(4) assms(5) by auto
  have inter: "{l \<in> {0..< \<v>}. N2 $$ (l , j1) = 1 \<and> (N2 $$ (l, j2) = 1)} \<inter>{l \<in> {0..< \<v>}. N2 $$ (l , j1) = 0 \<or> (N2 $$ (l, j2) = 0)} = {}" by auto
  have "(col N2 j1) \<bullet> (col N2 j2) = (\<Sum> k \<in> {0 ..< dim_vec (col N2 j2)}. (col N2 j1) $ k * (col N2 j2) $ k)"
    using scalar_prod_def[of "col N2 j1" "col N2 j2"] by auto
  also have "... = (\<Sum> k \<in> {0 ..<\<v>}. N2 $$ (k , j1) * (N2 $$ (k, j2)))" 
    using index_col carrier_dim_vec assms by simp
  also have "... = (\<Sum> k \<in> {l \<in> {0..< \<v>}. N2 $$ (l , j1) = 1 \<and> (N2 $$ (l, j2) = 1)}.N2 $$ (k , j1) * N2 $$ (k , j2))  
    + (\<Sum> k \<in> {l \<in> {0..< \<v>}. N2 $$ (l , j1) = 0 \<or> (N2 $$ (l, j2) = 0)}. N2 $$ (k , j1) * N2 $$ (k , j2))"
    using inter split sum.union_disjoint[of " {l \<in> {0..< \<v>}. N2 $$ (l , j1) = 1 \<and> (N2 $$ (l, j2) = 1)}" "{l \<in> {0..< \<v>}. N2 $$ (l , j1) = 0 \<or> (N2 $$ (l, j2) = 0)}"]
      finite_nat_set_iff_bounded
    by (smt (verit, del_insts) finite_Un finite_atLeastLessThan) 
  also have "... = (of_int (card {l. l < \<v> \<and> N2 $$ (l , j1) = 1 \<and> (N2 $$ (l, j2) = 1)}))"
    using mult_0 by (simp add: sum.neutral)
  also have "... = (of_int (mat_inter_num N2 j1 j2))" using mat_inter_num_def assms
    by (smt (verit) Collect_cong carrier_matD(1)) 
  finally show "(col N2 j1) \<bullet> (col N2 j2) = 0" using mod0 by simp
qed

lemma vec_scalar_prod_odd_1: 
  fixes N2 :: "'b:: {prime_card} mod_ring mat"
  assumes "CARD('b) = 2"
  assumes "j < \<b>"
  assumes "N2 \<in> carrier_mat \<v> \<b>"
  assumes "N = to_int_mat N2"
  shows "(col N2 j) \<bullet> (col N2 j) = 1"
proof -
  interpret mmt: mat_mod_type 2 "TYPE('b::prime_card)" 
    using assms by (unfold_locales) (simp_all)
  have nmm: "N = mmt.mat_mod N" using mmt.mat_mod_eq_cond mat.elems01 by auto
  then have mmrel: "mmt.MM_Rel N N2" using mmt.MM_Rel_def nmm assms by simp
  then have "N2 = map_mat (of_int_mod_ring) N" using assms
    by auto  
  have od: "odd (mat_block_size N j)" 
    using assms odd_blocks_mat_block_size[of j] N_carrier_mat dim_col_is_b by simp
  have "(mat_block_size N2 j) = (mat_block_size N j)" using mmt.mat_block_size_MM_Rel mmrel nmm  N_carrier_mat
    by (metis dim_col_is_b index_map_mat(3) assms) 
  then have "odd (int (mat_block_size N2 j))" using od by simp
  then have mod1: "of_int (mat_block_size N2 j) = (1 :: 'b mod_ring)" 
    by (transfer' fixing: \<V>s \<B>s N2 j, simp add: assms(1)) (presburger)
  then have  "elements_mat N2 = (of_int_mod_ring) `elements_mat N"
    by (simp add: \<open>N2 = map_mat of_int_mod_ring N\<close> map_mat_elements) 
  then have "elements_mat N2 \<subseteq> {(of_int 0),(of_int 1)}"
    using mat.elems01 by (auto simp add: of_int_of_int_mod_ring) 
  then have N2_elems_01: "elements_mat N2 \<subseteq> {0,1}"
    by simp 
  then have "\<And> i j. i < \<v> \<Longrightarrow> j < \<b> \<Longrightarrow> N2 $$ (i, j) \<noteq> 0 \<Longrightarrow> N2 $$ (i, j) = 1"
    using assms(3) by auto 
  then have split: "{0 ..< \<v>} = {l \<in> {0..< \<v>}. N2 $$ (l , j) = 1 } \<union> {l \<in> {0..< \<v>}. N2 $$ (l , j) = 0}"
    using assms(2) assms(3) by auto
  have inter: "{l \<in> {0..< \<v>}. N2 $$ (l , j) = 1 } \<inter>{l \<in> {0..< \<v>}. N2 $$ (l , j) = 0} = {}" by auto
  have "(col N2 j) \<bullet> (col N2 j) = (\<Sum> i \<in> {0..<\<v>} . (col N2 j) $ i * (col N2 j) $ i)" 
    using assms scalar_prod_def dim_col
    by (metis (mono_tags, lifting) carrier_matD(1) sum.cong) 
  also have "... = (\<Sum> i \<in> {0..<\<v>} .  N2 $$ (i, j) * N2 $$ (i, j))" using assms(2) assms(3) by simp
  also have "... = (\<Sum> i \<in> {i . i <\<v> \<and> N2 $$ (i, j) = 1}. N2 $$ (i, j) * N2 $$ (i, j)) + (\<Sum> i \<in> {i . i <\<v> \<and> N2 $$ (i, j) = 0}. N2 $$ (i, j) * N2 $$ (i, j))" 
    using split inter sum.union_disjoint[of " {i . i <\<v> \<and> N2 $$ (i, j) = 1}" "{i . i <\<v> \<and> N2 $$ (i, j) = 0}" "\<lambda> i. N2 $$ (i, j) * N2 $$ (i, j)"] by auto
  also have "... = of_int (card {i . i <\<v> \<and> (col N2 j) $ i = 1})" using assms(2) assms(3) index_col 
    by (simp) (smt (verit, del_insts) Collect_cong carrier_matD(1) carrier_matD(2)  index_col) 
  also have "... = of_int (card {i .  (col N2 j) $ i = 1 \<and> i <(dim_vec (col N2 j))})" 
    using assms(2) assms(3) dim_col by (metis carrier_matD(1)) 
  also have "... = of_int (mat_block_size N2 j)" using count_vec_alt[of "col N2 j" "1"]  by (simp) 
  finally show ?thesis using mod1 by simp
qed

lemma upper_bound_clubs: 
  assumes "CARD('b::prime_card) = 2"
  shows "\<b> \<le> \<v>"
proof -
  have cb2: "CARD('b) = 2" using assms by simp
  then interpret mmt: mat_mod_type 2 "TYPE('b::prime_card)" 
    using assms by (unfold_locales) (simp_all)
  have nmm: "N = mmt.mat_mod N" using mmt.mat_mod_eq_cond mat.elems01 by auto
  then obtain N2 :: "'b mod_ring mat" where neq: "N = to_int_mat N2"
    by (simp add: mmt.mat_mod_N_representative)
  then have mmrel: "mmt.MM_Rel N N2" using mmt.MM_Rel_def nmm neq by simp
  then have "N2 = map_mat (of_int_mod_ring) N" using neq
    by auto  
  show ?thesis proof (intro lin_bound_argument2[of "N2"])
    show "distinct (cols (N2))" using distinct_cols_N neq to_int_mod_ring_hom.vec_hom_set_distinct_iff neq map_vec_mat_cols
      by metis
    show n2cm:"N2 \<in> carrier_mat \<v> \<b>" 
      using neq N_carrier_mat by fastforce 
    show "\<And>f. vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. f (col N2 j) * (col N2 j) $ i) = 0\<^sub>v \<v> \<Longrightarrow> \<forall>v\<in>set (cols N2). f v = 0"
    proof (auto)
      fix f v 
      assume eq0: "vec \<v> (\<lambda>i. \<Sum>j = 0..<length \<B>s. f (col N2 j) * (col N2 j) $ i) = 0\<^sub>v \<v>" 
      assume vin: "v \<in> set (cols N2)"
      define c where "c \<equiv> (\<lambda> j. f (col N2 j))"
      have inner: "\<And> j l. v $ l * (c j * (col N2 j) $ l) = c j * v $ l *  (col N2 j) $ l" 
        using mult.commute by auto
      obtain j' where v_def: "col N2 j' = v" and jvlt: "j' < dim_col N2"
        using vin by (metis cols_length cols_nth index_less_size_conv nth_index) 
      have even0: "\<And> j. j \<in> {0..<dim_col N2} - {j'} \<Longrightarrow>  c j * (v \<bullet> (col N2 j)) = 0"
      proof - 
        fix j assume "j \<in> {0..<dim_col N2} - {j'}"
        then have  "(v \<bullet> (col N2 j)) = 0" using vec_scalar_prod_even_0[of "j'" "j" "N2"] v_def jvlt n2cm neq cb2 by simp
        then show "c j * (v \<bullet> (col N2 j)) = 0" by simp
      qed
      have vinc: "v \<in> carrier_vec \<v>" using n2cm set_cols_carrier vin
        by blast
      then have "0 = v \<bullet> vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. c j * (col N2 j) $ i)"
        using eq0 c_def by auto  
      also have "... = (\<Sum> l =0..<dim_row N2 . v $ l *  (\<Sum> j = 0..<dim_col N2 . (c j * (col N2 j) $ l)))"
        unfolding scalar_prod_def  using n2cm by auto 
      also have "... = (\<Sum> l =0..<dim_row N2 . (\<Sum> j = 0..<dim_col N2 . v $ l * (c j * (col N2 j) $ l)))"
        by (simp add: sum_distrib_left) 
      also have "... = (\<Sum> j \<in> {0..<dim_col N2} .  v \<bullet> (c j \<cdot>\<^sub>v (col N2 j)))" using sum.swap scalar_prod_def[of v]
        by simp
      also have "... = v \<bullet> (c j' \<cdot>\<^sub>v v) + (\<Sum> j \<in> {0..<dim_col N2} - {j'}.  v \<bullet> (c j \<cdot>\<^sub>v (col N2 j)))" 
        using jvlt sum.remove[of "{0..<dim_col N2}" "j'" "\<lambda> j. v \<bullet> (c j \<cdot>\<^sub>v (col N2 j))"] v_def by simp
      also have "... = v \<bullet> (c j' \<cdot>\<^sub>v v) + (\<Sum> j \<in> {0..<dim_col N2} - {j'}.  c j * (v \<bullet> (col N2 j)))" 
        using n2cm scalar_prod_smult_distrib col_dim v_def by force 
      also have "... = v \<bullet> (c j' \<cdot>\<^sub>v v)" 
         using even0 by (simp add: sum.neutral) 
      also have "... = (c j') * (v \<bullet> v)" using scalar_prod_smult_distrib
        by (simp add: v_def)
      finally have "0 = (c j')" using vec_scalar_prod_odd_1[of "j'" "N2"] v_def jvlt n2cm neq cb2 by simp
      then show "f v = 0"
        using c_def v_def by simp 
    qed
  qed
qed

end

end