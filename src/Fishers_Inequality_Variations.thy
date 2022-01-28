theory Fishers_Inequality_Variations imports Dual_Systems Rank_Argument_General 
Vector_Matrix_Mod
begin

(*
lemma mod_ring_distinct_vecs: 
  fixes A :: "int vec list" and A' :: "('a :: {prime_card} mod_ring) vec list"
  assumes "A' = map (\<lambda> v. map_vec of_int v) A"
  assumes "\<And> i x. i < length A \<Longrightarrow> x \<in> set\<^sub>v (A ! i) \<Longrightarrow> x < CARD('a :: {prime_card})"
  assumes "distinct A" 
  shows "distinct A'"
  using assms proof (induct A arbitrary: A')
  case Nil
  then show ?case by simp
next
  case (Cons a A)
  define xs :: "('a :: {prime_card} mod_ring) vec list" where "xs \<equiv> map (map_vec of_int) A"
  have "A' = (map_vec of_int a) # xs"
    by (simp add: Cons.prems(1) xs_def) 
  have d: "distinct A" using Cons.prems by simp
  have "(\<And>i x. i < length A \<Longrightarrow> x \<in>$ A ! i \<Longrightarrow> x < int CARD('a))" using Cons.prems
    by (metis find_first_le list.set_intros(2) nth_find_first nth_mem) 
  then have dxs: "distinct xs" using Cons.hyps d apply (auto)
    using xs_def by blast  
  have "(map_vec of_int a) \<in> set xs \<Longrightarrow> False" 
  proof - 
    assume a: "(map_vec of_int a) \<in> set xs"
    then obtain i where ilt: "i < length xs" and "xs ! i = (map_vec of_int a)" 
      using obtain_set_list_item by metis 
    show "False" sorry
  qed
  then have "(map_vec of_int_mod_ring a) \<notin> set ?xs"
    by blast
  then show ?case using dxs
    by (simp add: \<open>A' = map_vec of_int_mod_ring a # map (map_vec of_int_mod_ring) A\<close>) 
qed
*)

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

lemma right_unique_MM_Rel[transfer_rule]: "right_unique MM_Rel"
  unfolding right_unique_def MM_Rel_def 
  using to_int_mod_ring_hom.mat_hom_inj by auto

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

(* 
lemma mat_block_size_MM_Rel[transfer_rule]: "(MM_Rel ===> (=) ===>  (=) ) (\<lambda> A i. mat_block_size (mat_mod A) i) (\<lambda> B i. mat_block_size B i)"
  unfolding MM_Rel_def rel_fun_def apply auto 
  sorry

lemma proper_inc_mat_MM_Rel[transfer_rule]: "(MM_Rel ===>  (=) ) (proper_inc_mat ) (proper_inc_mat)"
  unfolding MM_Rel_def rel_fun_def
  by (metis index_map_mat(2) index_map_mat(3) mat_mod_dim(1) mat_mod_dim(2) proper_inc_mat_def) 

lemma mat_block_size_eq: 
  assumes "MM_Rel N1 N2"
  assumes "j < dim_col N1"
  shows "mat_block_size N2 j = mat_block_size (mat_mod N1) j"
proof -
  have "mat_block_size N2 j = count_vec (col N2 j) 1" by simp
  then have "... = count_vec (to_int_vec (col N2 j)) 1" 
    sorry
  thus ?thesis sorry
qed

*)

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

lemma even_inter_mat_intersections: 
  assumes "j1 < dim_col N" "j2 < dim_col N"
  assumes "j1 \<noteq> j2"
  shows "even (mat_inter_num N j1 j2)"
  using even_inters mat_inter_num_conv assms
  by (metis dim_col_b_lt_iff obtains_two_diff_index) 

end

sublocale odd_town \<subseteq> ordered_simple_design
  using odd_town_no_repeat_clubs by (unfold_locales) (meson distinct_mset_def) 

context odd_town 
begin

(* 

What's required
- Work in the vector space Z/Z2 instead of reals \<Longrightarrow> need to convert vectors to be of appropriate type.
- conversion between real vector columns of N and appropriate type. 
- Reasoning that vi * vj (dot) = 0 if i \<noteq> j as intersections are even, and = 1 if i = j (as club sizes are odd).
- easy to see that in sum over all vectors = 0, if we times whole thing by vi (dot prod), all terms will disappear except 1. 
Therefore this term must be 0.
-Convert result bac to reals?
*)

lemma upper_bound_clubs: 
  assumes "CARD('b::prime_card) = 2"
  shows "\<b> \<le> \<v>"
proof -
  have "CARD('b::prime_card) = CARD('b)"
    by simp 
  then have cb2: "CARD('b) = 2" using assms by simp
  then interpret mmt: mat_mod_type 2 "TYPE('b::prime_card)" 
    using assms by (unfold_locales) (simp_all)
  interpret vs: vec_space "TYPE('b::{prime_card} mod_ring)" \<v> .
  have nmm: "N = mmt.mat_mod N" using mmt.mat_mod_eq_cond mat.elems01 by auto
  then obtain N2 :: "'b mod_ring mat" where neq: "N = to_int_mat N2"
    by (simp add: mmt.mat_mod_N_representative)
  then have mmrel: "mmt.MM_Rel N N2" using mmt.MM_Rel_def nmm neq by simp
  then have "N2 = map_mat (of_int_mod_ring) N" using neq
    by auto  
  then have N2_elems_01: "elements_mat N2 \<subseteq> {0, 1}"
    using map_mat_elements
    by (metis (no_types, lifting) image_empty image_insert image_mono mat.elems01 of_int_mod_ring_hom.hom_zero of_int_mod_ring_to_int_mod_ring to_int_mod_ring_hom.hom_one) 
  have dimv: "vs.dim  = \<v>" using vs.dim_is_n by simp
  have N2_carrier_mat: "N2 \<in> carrier_mat \<v> \<b>" 
    using neq N_carrier_mat by fastforce 
  then have length_cols: "length (cols (N2)) = \<b>" by simp
  then have dim_col: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> dim_vec ((cols N2) ! j) = \<v>" 
    using N2_carrier_mat by simp
  have fin: "finite (set (cols N2))"
    by simp
  have distinct_cols_N2: "distinct (cols N2)"
    using distinct_cols_N neq to_int_mod_ring_hom.vec_hom_set_distinct_iff neq map_vec_mat_cols
    by metis 
  have cv: "set (cols N2) \<subseteq> carrier_vec \<v>"
    using cols_dim dim_row_is_v neq
    by (metis N2_carrier_mat carrier_matD(1)) 
  have lidpt: "vs.lin_indpt (set (cols N2))" (* Easy set to relate to *)
  proof (rule vs.finite_lin_indpt2, simp_all add: cv)
    fix a assume comb: "vs.lincomb a (set (cols N2)) = 0\<^sub>v \<v>"
    define c where ceq: "c = (\<lambda> i. a ((cols N2) ! i))"
    then have listcomb: "vs.lincomb_list c (cols N2) = 0\<^sub>v \<v>" 
      using vs.lincomb_as_lincomb_list_distinct[OF cv distinct_cols_N2] comb by simp
    have dim: "\<And> j. j < \<b> \<Longrightarrow>  dim_vec (c j \<cdot>\<^sub>v (cols N2) ! j) = \<v>" using cv
      using carrier_dim_vec nth_mem N2_carrier_mat by (simp) 
    have "\<And> v. v \<in> set (cols N2) \<Longrightarrow> a v = 0"
    proof -
      fix v assume vin: "v \<in> set (cols N2)"
      then obtain i where v_def: "cols N2 ! i = v" and ilt: "i < length (cols N2)"
        by (metis in_set_conv_nth)
      then have iin: "i \<in> {0..<\<b>}" using length_cols by simp
      have v_def_alt: "v = col N2 i" using v_def ilt by simp
      have dv: "dim_vec v = \<v>" using vin cv by auto
      have v_elems: "set\<^sub>v v \<subseteq> {0, 1}" using N2_elems_01 vin col_elems_subset_mat
        by (metis cols_length cols_nth dual_order.trans ilt v_def) 
      have col_elems: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> set\<^sub>v (col N2 j) \<subseteq> {0, 1}"
        using N2_elems_01  col_elems_subset_mat N2_carrier_mat
        by (metis atLeastLessThan_iff carrier_matD(2) subset_iff_psubset_eq subset_psubset_trans)   
      have int_num_0: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> i \<noteq> j \<Longrightarrow> v \<bullet> (c j \<cdot>\<^sub>v (cols N2) ! j) = 0" 
      proof - 
        fix j assume jin: "j \<in> {0..<\<b>}" and ineqj: "i \<noteq> j" 
        have ev: "even (mat_inter_num N i j)" using jin ineqj iin even_inter_mat_intersections[of i j] by auto
        have "mat_inter_num N2 i j = mat_inter_num N i j" using mmt.mat_inter_num_MM_Rel mmrel nmm jin iin N_carrier_mat
          by (metis atLeastLessThan_iff dim_col_is_b index_map_mat(3) neq) 
        then have "even (int (mat_inter_num N2 i j))" using ev by simp
        then have mod0: "of_int (mat_inter_num N2 i j) = (0 :: 'b mod_ring)" by (transfer' fixing: \<V>s \<B>s N2 i j, simp add: cb2)
        have eq_cond: "\<And> l. l < dim_row N2 \<and> (col N2 i) $ l = 1 \<and> (col N2 j) $ l = 1 \<longleftrightarrow>l < dim_row N2 \<and> N2 $$ (l, i) = 1 \<and> N2 $$ (l, j) = 1"
          using jin iin index_col N2_carrier_mat by auto
        have "{0 ..< \<v>} = {l. l < \<v>}" by auto
        then have split: "{0 ..< \<v>} = {l. l < \<v> \<and> v $ l = 1 \<and> (col N2 j) $ l = 1} \<union> {l. l < \<v> \<and> (v $ l \<noteq> 1 \<or> (col N2 j) $ l \<noteq> 1)}"
          by fastforce
        have inter: "{l. l < \<v> \<and> v $ l = 1 \<and> (col N2 j) $ l = 1} \<inter>{l. l < \<v> \<and> (v $ l \<noteq> 1 \<or> (col N2 j) $ l \<noteq> 1)} = {}" by auto
        have veq_0: "\<And> k. k < \<v> \<Longrightarrow> v $ k \<noteq> 1 \<Longrightarrow> v $ k = 0" using v_elems
          by (smt (verit, best) dv insertE singletonD subset_eq vec_setI) 
        have dvj: "dim_vec (col N2 j) = \<v>" using jin N2_carrier_mat by auto
        have "\<And> k. k < \<v> \<Longrightarrow> (col N2 j) $ k \<in> {0, 1}"
          using col_elems[of j] vec_setI jin dvj jin by (metis subsetD) 
        then have jcol_eq_0: "\<And> k. k < \<v> \<Longrightarrow> (col N2 j) $ k \<noteq> 1 \<Longrightarrow> (col N2 j) $ k = 0"
          by blast 
        then have  "\<And> k. k < \<v> \<Longrightarrow> v $ k \<noteq> 1 \<or>  (col N2 j) $ k \<noteq> 1  \<Longrightarrow> v $ k * (col N2 j) $ k = 0"
          using jcol_eq_0 veq_0
          using mult_not_zero by blast
        then have mult_0: "\<And> k. k \<in> {l. l < \<v> \<and> (v $ l \<noteq> 1 \<or> (col N2 j) $ l \<noteq> 1)} \<Longrightarrow> v $ k * (col N2 j) $ k = 0" by auto
        have "v \<bullet> (c j \<cdot>\<^sub>v (cols N2) ! j) = c j * (v \<bullet> ((cols N2) ! j))" using scalar_prod_smult_distrib[of "v" "\<v>" "(cols N2) ! j" "c j"] dv dim
          using carrier_vecI jin local.dim_col by blast 
        also have "... = c j * (v \<bullet> (col N2 j))" using jin N2_carrier_mat by auto
        also have "... = c j * (\<Sum> k \<in> {0 ..< dim_vec (col N2 j)}. v $ k * (col N2 j) $ k)" 
          using scalar_prod_def[of "v" "col N2 j"] by auto
        also have "... = c j * (\<Sum> k \<in> {0 ..< \<v>}. v $ k * (col N2 j) $ k)" 
          using cv carrier_dim_vec nth_mem N2_carrier_mat jin by simp
        also have un: "... = c j * (\<Sum> k \<in> {l. l < \<v> \<and> v $ l = 1 \<and> (col N2 j) $ l = 1} \<union> {l. l < \<v> \<and> (v $ l \<noteq> 1 \<or> (col N2 j) $ l \<noteq> 1)}. v $ k * (col N2 j) $ k)" 
          using split by simp
        also have "... = c j * ((\<Sum> k \<in> {l. l < \<v> \<and> v $ l = 1 \<and> (col N2 j) $ l = 1}.v $ k * (col N2 j) $ k)  +  (\<Sum> k \<in> {l. l < \<v> \<and> (v $ l \<noteq> 1 \<or> (col N2 j) $ l \<noteq> 1)}. v $ k * (col N2 j) $ k))"
          using inter sum.union_disjoint  
          by (metis (no_types, lifting) un \<open>{0..<\<v>} = {l. l < \<v>}\<close>  finite_nat_set_iff_bounded mem_Collect_eq) 
        also have "... = c j * ((\<Sum> k \<in> {l. l < \<v> \<and> v $ l = 1 \<and> (col N2 j) $ l = 1}. 1) +  (\<Sum> k \<in> {l. l < \<v> \<and> (v $ l \<noteq> 1 \<or> (col N2 j) $ l \<noteq> 1)}. v $ k * (col N2 j) $ k))"
          by simp
        also have "... = c j * (\<Sum> k \<in> {l. l < \<v> \<and> v $ l = 1 \<and> (col N2 j) $ l = 1}. 1)" 
          using mult_0 by (simp add: sum.neutral)
        also have "... = c j * (of_int (card {l. l < \<v> \<and> v $ l = 1 \<and> (col N2 j) $ l = 1}))"
          by simp
        also have "... = c j * (of_int (card {l . l < dim_row N2 \<and> (col N2 i) $ l = 1 \<and> (col N2 j) $ l = 1}))" using N2_carrier_mat v_def_alt  by simp
        also have "... = c j * (of_int (card {l . l < dim_row N2 \<and> N2 $$ (l, i) = 1 \<and> N2 $$ (l, j) = 1}))" using eq_cond by simp
        also have "... = c j * (of_int (mat_inter_num N2 i j))" by (simp add: mat_inter_num_def)
        also have "... = c j * (0)" using mod0 by simp
        finally show "v \<bullet> (c j \<cdot>\<^sub>v (cols N2) ! j) = 0" by simp
      qed
      have "(1 :: 'b :: {prime_card} mod_ring) \<noteq> 0"
        by simp       
      then have "\<And> i. i < \<v> \<Longrightarrow> v $ i \<in> {0, 1}" 
        using dv
        by (metis in_mono v_elems vec_setI) 
      then have "\<And> i. i < \<v> \<Longrightarrow> v $ i = 0 \<or> v $ i = 1"
        by blast 
      then have split : "{0..<\<v>} = {i . i <\<v> \<and> v $ i = 1} \<union> {i . i <\<v> \<and> v $ i = 0}" by fastforce
      have split_empty: "{i . i <\<v> \<and> v $ i = 1} \<inter> {i . i <\<v> \<and> v $ i = 0} = {}" using one_neq_zero by auto
      have mbseq: "\<And> i. i < \<b> \<Longrightarrow> mat_block_size N2 i = mat_block_size N i" using mmt.mat_block_size_MM_Rel N_carrier_mat mmrel
        using nmm by fastforce 
      have same_1: "v \<bullet> v = 1"
      proof -
        have "v \<bullet> v = (\<Sum>l \<in> {0..<\<v>} . v $ l * v $ l)" using dim_col scalar_prod_def
          by (metis (full_types) iin v_def) 
        also have "... = (\<Sum> l \<in> {i . i <\<v> \<and> v $ i = 1}. v $ l * v $ l) + (\<Sum> l \<in> {i . i <\<v> \<and> v $ i = 0}. v $ l * v $ l)" 
          using split split_empty sum.union_disjoint[of " {i . i <\<v> \<and> v $ i = 1}" "{i . i <\<v> \<and> v $ i = 0}" "\<lambda> i. v $ i * v $ i"] by auto
        also have "... = of_int (card {i . i <\<v> \<and> v $ i = 1})" by( simp)
        also have "... = of_int ((count_vec v 1))" using dv
          by (metis (no_types, lifting) Collect_cong count_vec_alt) 
        also have "... = of_int (mat_block_size N2 i)" by (simp add: v_def_alt) 
        also have "... = of_int (mat_block_size N i)" using mbseq iin by simp
        also have "... = 1" apply (transfer' fixing: \<V>s \<B>s i, simp add: cb2) 
          using odd_blocks_mat_block_size[of i] iin mod2_eq_if[of "int (mat_block_size N i)"] by auto
        finally show ?thesis by simp
      qed
      have "0 = v \<bullet> (vs.lincomb_list c (cols N2))"
        using \<open>v \<in> set (cols N2)\<close> cv listcomb by auto 
      also have "... = v \<bullet> (vs.sumlist (map (\<lambda>j. c j \<cdot>\<^sub>v (cols N2) ! j) [0..<\<b>]))"
        using vs.lincomb_list_def length_cols by simp
      also have "... = (\<Sum> l \<in> {0..<\<v>} . v $ l * (vs.sumlist (map (\<lambda>j. c j \<cdot>\<^sub>v (cols N2) ! j) [0..<\<b>])) $ l)"
        by (metis (no_types) index_zero_vec(2) length_cols listcomb scalar_prod_def vs.lincomb_list_def)
      also have "... = (\<Sum> l \<in> {0..<\<v>} . v $ l * (sum (\<lambda> j. (c j \<cdot>\<^sub>v (cols N2) ! j) $ l) {0..<\<b>}))"
        using vs.sumlist_nth dim by simp
      also have "... = (\<Sum> l \<in> {0..<\<v>} .  (\<Sum> j \<in> {0..<\<b>} . v $ l * (c j \<cdot>\<^sub>v (cols N2) ! j) $ l))"
        by (simp add: sum_distrib_left) 
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (\<Sum> l \<in> {0..<\<v>} .  v $ l * (c j \<cdot>\<^sub>v (cols N2) ! j) $ l))"
        using sum.swap[of  "\<lambda> l j. v $ l * (c j \<cdot>\<^sub>v (cols N2) ! j) $ l"  "{0..<\<b>}" "{0..<\<v>}"] by simp
      also have "... = (\<Sum> j \<in> {0..<\<b>} .  v \<bullet> (c j \<cdot>\<^sub>v (cols N2) ! j) )" using scalar_prod_def dim_col
        by (smt (verit) index_smult_vec(2) sum.cong) 
      also have "... = v \<bullet> (c i \<cdot>\<^sub>v v) + (\<Sum> j \<in> {0..<\<b>} - {i}.  v \<bullet> (c j \<cdot>\<^sub>v (cols N2) ! j) )" 
        using iin sum.remove[of "{0..<\<b>}" "i" "\<lambda> j. v \<bullet> (c j \<cdot>\<^sub>v (cols N2) ! j)"] v_def by simp
      also have "... = v \<bullet> (c i \<cdot>\<^sub>v v)" using int_num_0 by simp
      also have "... = (c i) * (v \<bullet> v)" using scalar_prod_smult_distrib
        by (simp add: \<open>cols N2 ! i = v\<close>)
      finally have "0 = (c i)" using same_1 by simp
      then show "a v = 0"
        using ceq \<open>cols N2 ! i = v\<close> by simp 
    qed
    then show "\<forall>v\<in>set (cols N2). a v = 0" by simp
  qed
  show ?thesis using distinct_cols_N2 vs.lin_indpt_dim_col_lt_dim[of "N2" "\<b>"] lidpt N2_carrier_mat dimv by simp
qed

end

end