(* Title: Fishers_Inequality.thy
   Author: Chelsea Edmonds
*)

theory Fishers_Inequality imports Rank_Argument_General Linear_Bound_Argument
begin


(* Basic Fisher's Inequality *)
context ordered_bibd
begin

(* Note, some of this could be generalised further *)

lemma transform_N_step1: 
  assumes "i < dim_row (N * N\<^sup>T)"
  assumes "j < dim_col (N * N\<^sup>T)"
  shows "i = 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (N* N\<^sup>T) $$ (i, j)" 
  and "i \<noteq> 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = ((-1) * (N* N\<^sup>T)$$(0, j)) + (N* N\<^sup>T)$$(i,j)"
proof -
  let ?M = "(N * N\<^sup>T)"
  assume "i = 0"
  then have "i \<notin> set ([1..<dim_row ?M])"  by simp
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = ?M $$ (i, j)"  using assms by simp
next 
  let ?M = "(N * N\<^sup>T)"
  assume a: "i \<noteq> 0"
  then have jin:"i \<in> set ([1..<dim_row ?M])" using assms(1) by simp
  have dis: "distinct [1..<dim_row ?M]" by simp
  have notin: "0 \<notin> set ([1..<dim_row ?M])" by simp
  have "0 < dim_row ?M" using assms(1) by auto 
  then show "add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M $$ (i, j) = ((-1) * ?M$$(0, j)) + ?M$$(i,j)" 
    using dis jin assms notin  add_row_to_multiple_index_change
    by blast 
qed

lemma transform_N_step1_vals: 
  assumes "i < dim_row (N * N\<^sup>T)"
  assumes "j < dim_col (N * N\<^sup>T)"
  shows "i = 0 \<Longrightarrow> j = 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (int \<r>)"
  and "i \<noteq> 0 \<Longrightarrow> j = 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (int \<Lambda>) - (int \<r>)" 
  and "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (int \<Lambda>)"
  and "i \<noteq> 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> i = j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (int \<r>) - (int \<Lambda>)"
  and "i \<noteq> 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> i \<noteq> j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = 0"
proof - 
  let ?M = "(N * N\<^sup>T)"
  assume a: "j = 0" "i=0"
  then have "(add_row_to_multiple (-1) [1..<dim_col (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (N* N\<^sup>T) $$ (i, j)" using assms by simp
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (int \<r>)"  using transpose_N_mult_diag v_non_zero assms
    by (simp add: a)
next
  let ?M = "(N * N\<^sup>T)"
  assume a: "j = 0" "i\<noteq>0"
  then have ail: "((-1) * ?M $$(0, j)) = -(int \<r>)" 
    by (simp add: a assms transpose_N_mult_diag v_non_zero) 
  then have ijne: "j \<noteq> i" using a by simp
  then have aij: "?M $$ (i, j) = (int \<Lambda>)" using  assms transpose_N_mult_off_diag a v_non_zero
    by (metis transpose_N_mult_dim(1)) 
  then have "add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M $$ (i, j) = (-1)*(int \<r>) + (int \<Lambda>)" using ail transform_N_step1 assms a by simp
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (int \<Lambda>) - (int \<r>)"
    by linarith 
next
  let ?M = "(N * N\<^sup>T)"
  assume a: "i = 0" "j \<noteq> 0"
  have ijne: "i \<noteq> j" using a by simp
  then have "(add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (N* N\<^sup>T) $$ (i, j)" using a assms by simp
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (int \<Lambda>)" using transpose_N_mult_off_diag v_non_zero assms ijne
    by (metis a(1) transpose_N_mult_dim(2)) 
next 
  let ?M = "(N * N\<^sup>T)"
  assume a: "i \<noteq> 0" "j \<noteq> 0" "i = j"
  have ail: "((-1) * ?M $$(0, j)) = -(int \<Lambda>)" 
    using assms transpose_N_mult_off_diag a v_non_zero transpose_N_mult_dim(1) by auto  
  then have aij: "?M $$ (i, j) = (int \<r>)" using  assms transpose_N_mult_diag a v_non_zero
    by (metis transpose_N_mult_dim(1)) 
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (int \<r>) - (int \<Lambda>)"
    using ail aij transform_N_step1 assms a
    by (metis uminus_add_conv_diff) 
next 
  let ?M = "(N * N\<^sup>T)"
  assume a: "i \<noteq> 0" "j \<noteq> 0" "i \<noteq> j"
  have ail: "((-1) * ?M $$(0, j)) = -(int \<Lambda>)" 
    using assms transpose_N_mult_off_diag a v_non_zero transpose_N_mult_dim(1) by auto  
  then have aij: "?M $$ (i, j) = (int \<Lambda>)" using  assms transpose_N_mult_off_diag a v_non_zero
    by (metis transpose_N_mult_dim(1) transpose_N_mult_dim(2)) 
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = 0" using aij ail transform_N_step1 assms a
    by (metis add.commute add.right_inverse)
qed

(* Add multiple rows *)

lemma transform_N_step2: 
  assumes "i < dim_row (N * N\<^sup>T)"
  assumes "j < dim_col (N * N\<^sup>T)"
  assumes "M = (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T))"
  shows "j \<noteq> 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = M $$ (i, j)" 
  and "j = 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l \<in> {1..<dim_col M}.  M $$(i,l)) + M$$(i,0)"
proof -
  assume "j \<noteq> 0"
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = M $$ (i, j)" using assms by simp
next 
  assume a: "j = 0"
  then have inotin: "j \<notin> set [1..<dim_col M]" by simp
  have lbound: "\<And> l . l \<in> set [1..<dim_col M] \<Longrightarrow> l < dim_col M" by simp
  then have "add_multiple_cols 1 j [1..<dim_col M] M $$ (i, j) = (\<Sum>l\<leftarrow>[1..<dim_col M]. 1 * M $$(i,l)) + M$$(i,j)"
    using add_multiple_cols_index_eq[of "i" "M" "j" "[1..<dim_col M]" "1"] assms inotin by simp
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l \<in>{1..<dim_col M}.  M $$(i,l)) + M$$(i,0)"
    using a by (simp add: sum_set_upt_eq_sum_list) 
qed

lemma transform_N_step2_vals: 
  assumes "i < dim_row (N * N\<^sup>T)"
  assumes "j < dim_col (N * N\<^sup>T)"
  assumes "M = (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T))"
  shows "i = 0 \<Longrightarrow> j = 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (int \<r>) + (int \<Lambda>) * (\<v> - 1)"
  and "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = (int \<Lambda>)" 
  and "i \<noteq> 0 \<Longrightarrow> i = j \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (int \<r>) - (int \<Lambda>)"
  and "i \<noteq> 0 \<Longrightarrow> i \<noteq> j \<Longrightarrow>  add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = 0"
proof -
  assume a: "i = 0" "j =0"
  have dim_eq: "dim_col M = dim_col (N * N\<^sup>T) " using assms by simp
  then have "dim_col M = \<v>"
    by (simp add: dim_row_is_v)
  then have size: "card {1..<dim_col M} = \<v> - 1" by simp 
  have val: "\<And> l . l \<in> {1..<dim_col M} \<Longrightarrow> M $$ (i, l) = (int \<Lambda>)" using assms(3) transform_N_step1_vals(3)
    by (metis dim_eq a(1) assms(1) atLeastLessThan_iff not_one_le_zero)  
  have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l\<in>{1..<dim_col M}.  M $$(i,l)) + M$$(i,0)" using a assms transform_N_step2 by simp
  also have "... = (\<Sum>l\<in>{1..<dim_col M}.  (int \<Lambda>)) + M$$(i,0)" using val by simp
  also have "... = (\<v> - 1) * (int \<Lambda>) + M$$(i,0)" using size
    by (metis sum_constant) 
  also have "... = (\<v> - 1) * (int \<Lambda>) + (int \<r>)" using transform_N_step1_vals(1)
    using a(1) a(2) assms(1) assms(2) assms(3) by presburger 
  finally show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (int \<r>) + (int \<Lambda>) * (\<v> - 1)" by simp
next 
  assume a: "i = 0" "j \<noteq> 0"
  then have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = M $$ (i, j)" using transform_N_step2 assms a by simp
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = (int \<Lambda>)" using assms a transform_N_step1_vals(3) by simp
next 
  assume a: "i \<noteq> 0" "i = j"
  then have jne: "j \<noteq> 0" by simp
  then have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = M $$ (i, j)" using transform_N_step2 assms a by simp
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (int \<r>) - (int \<Lambda>)" using assms a jne transform_N_step1_vals(4) by simp
next
  assume a: "i \<noteq> 0"  "i \<noteq> j"
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = 0" 
  proof (cases "j = 0")
    case True
    have ibound: "i \<ge> 1 \<and> i < dim_col M" using a(1) assms by simp
    then have iin: "i \<in> {1..<dim_col M}" by simp
    have dim_eq: "dim_col M = dim_col (N * N\<^sup>T) " using assms by simp
    have cond: "\<And> l . l \<in> {1..<dim_col M} \<Longrightarrow> l <dim_col (N * N\<^sup>T) \<and> l \<noteq> 0" using dim_eq by simp 
    then have val: "\<And> l . l \<in> {1..<dim_col M } - {i} \<Longrightarrow> M $$ (i, l) = 0" 
      using assms(3) transform_N_step1_vals(5) a True assms(1) by blast
    have val2: "M $$ (i, i) = (int \<r>) - (int \<Lambda>)" using assms(3) transform_N_step1_vals(4) a True
      by (metis assms(1) transpose_N_mult_dim(1) transpose_N_mult_dim(2)) 
    have val3: "M$$ (i, 0) = (int \<Lambda>) - (int \<r>)" using assms(3) transform_N_step1_vals(2) a True assms(1) assms(2) by blast 
    have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l\<in>{1..<dim_col M}.  M $$(i,l)) + M$$(i,0)" 
      using assms transform_N_step2 True by blast
    also have "... = M $$ (i, i)  + (\<Sum>l\<in>{1..<dim_col M} - {i}.  M $$(i,l)) + M$$(i,0)"
      by (metis iin finite_atLeastLessThan sum.remove)
    also have "... = (int \<r>) - (int \<Lambda>) + (int \<Lambda>) - (int \<r>)" using val val2 val3 by simp
    finally show ?thesis
      by force 
  next
    case False
    then have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = M $$ (i, j)" using transform_N_step2 assms by simp
    then show ?thesis using assms a transform_N_step1_vals(5) False by simp
  qed
qed

lemma transform_N_step2_diag_vals: 
  assumes "i < dim_row (N * N\<^sup>T)"
  assumes "M = (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T))"
  shows "i = 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i) = (int \<r>) + (int \<Lambda>) * (\<v> - 1)"
  and "i \<noteq> 0 \<Longrightarrow>  add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i)  = (int \<r>) - (int \<Lambda>)" 
proof -
  assume a: "i = 0" 
  then have "i < dim_col (N * N\<^sup>T)"
    using transpose_N_mult_dim(2) v_non_zero by linarith 
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i) = (int \<r>) + (int \<Lambda>) * (\<v> - 1)"
    using transform_N_step2_vals(1) assms a by blast 
next
  assume a: "i \<noteq> 0"
  then have "i < dim_col (N * N\<^sup>T)"
    using transpose_N_mult_dim(2) v_non_zero assms(1) transpose_N_mult_dim(1) by linarith
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i)  = (int \<r>) - (int \<Lambda>)" 
    using transform_N_step2_vals(3)[of "i" "i"]
    using a assms(1) assms(2) by blast 
qed

lemma transform_upper_triangular: 
  assumes "M = (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T))"
  shows "upper_triangular (add_multiple_cols 1 0 [1..<dim_col M] M)"
  using transform_N_step2_vals(4) by (intro upper_triangularI) (simp add: assms)

lemma determinant_inc_mat_square: "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1)"
proof -
(* Subtract the first column from each other column - adding a scalar multiple of one row (col?) to another does not change the determinant  *)

(* Add rows 2...v to the first row - adding a scalar multiple does not change the determinant...*)

(* Show the matrix is now lower triangular, therefore the det is the product of the sum of diagonal *)
  let ?B = "(N * N\<^sup>T)"
  have cm: "?B \<in> carrier_mat \<v> \<v>"
    using transpose_N_mult_dim(1) transpose_N_mult_dim(2) by blast  
  let ?C = "(add_row_to_multiple (-1) [1..<dim_row ?B] 0 ?B)"
(* assumes "l \<notin> set ks" and "l < n" and "A \<in> carrier_mat n n" *)
  have "0 \<notin> set [1..<dim_row ?B]" by simp
  then have detbc: "det (N * N\<^sup>T) = det ?C" using add_row_to_multiple_det v_non_zero
    by (metis cm) 
  let ?D = "add_multiple_cols 1 0 [1..<dim_col ?C] ?C"
(*  assumes "k \<notin> set ls" and "\<And>l. l \<in> set ls \<Longrightarrow> l < n" and "A \<in> carrier_mat n n"*)
  have d00: "?D $$ (0, 0) = ((int \<r>) + (int \<Lambda>) * (\<v> - 1))" using transform_N_step2_diag_vals(1) 
    by (metis transpose_N_mult_dim(1) v_non_zero) 
  have ine0: "\<And> i. i \<in> {1..<dim_row ?D} \<Longrightarrow> i \<noteq> 0" by simp
  have "\<And> i. i \<in> {1..<dim_row ?D} \<Longrightarrow> i < dim_row (N * N\<^sup>T)" by simp       
  then have diagnon0: "\<And> i. i \<in> {1..<\<v>} \<Longrightarrow> ?D $$ (i, i) = (int \<r>) - (int \<Lambda>)"   
    using transform_N_step2_diag_vals(2) ine0 dim_row_is_v by simp
  have "dim_col ?C = \<v>"
    by (simp add: dim_row_is_v) 
  then have alll: "\<And> l. l \<in> set [1..<dim_col ?C] \<Longrightarrow> l < \<v>" by simp
  have cmc: "?C \<in> carrier_mat \<v> \<v>" using cm 
    by (simp add: add_row_to_multiple_carrier)
  have dimgt2: "dim_row ?D \<ge> 2"
    using t_lt_order
    by (simp add: dim_row_is_v)  
  then have fstterm: "0 \<in> { 0 ..< dim_row ?D}" by (simp add: points_list_length)
  have "0 \<notin> set [1..<dim_col ?C]" by simp
  then have "det (N * N\<^sup>T) = det ?D" using add_multiple_cols_det alll cmc
    by (metis detbc) 
  also have "... = prod_list (diag_mat ?D)" using det_upper_triangular
    using transform_upper_triangular by fastforce 
  also have "... = (\<Prod> i = 0 ..< dim_row ?D. ?D $$ (i,i))" using prod_list_diag_prod by blast  
  also have "... = (\<Prod> i = 0 ..< \<v>. ?D $$ (i,i))"  by (simp add: dim_row_is_v)  
  finally have "det (N * N\<^sup>T) = ?D $$ (0, 0) * (\<Prod> i =  1 ..< \<v>. ?D $$ (i,i))" 
    using dimgt2 by (simp add: prod.atLeast_Suc_lessThan v_non_zero) 
  then have "det (N * N\<^sup>T) = ((int \<r>) + (int \<Lambda>) * (\<v> - 1)) * (\<Prod> i = 1 ..< \<v>. ?D $$ (i,i))" 
    using d00 by simp
  then have "det (N * N\<^sup>T) = ((int \<r>) + (int \<Lambda>) * (\<v> - 1)) * (\<Prod> i = 1 ..< \<v>. ((int \<r>) - (int \<Lambda>)))" 
    using diagnon0 by simp
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ((int \<r>) - (int \<Lambda>))^(\<v> - 1)"
    by simp
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ( \<r> - \<Lambda>)^(\<v> - 1)"
    using index_lt_replication
    by (metis (no_types, lifting) less_imp_le_nat of_nat_diff of_nat_mult of_nat_power)
  then show ?thesis by blast 
qed

theorem Fishers_Inequality_BIBD: "\<v> \<le> \<b>"
proof (intro rank_argument_det[of "map_mat real_of_int N" "\<v>" "\<b>"], simp_all)
  show "N \<in> carrier_mat \<v> (length \<B>s)" using blocks_list_length N_carrier_mat by simp
  let ?B = "map_mat (real_of_int) (N * N\<^sup>T)"
  have b_split: "?B = map_mat (real_of_int) N * (map_mat (real_of_int) N)\<^sup>T"
    using semiring_hom.mat_hom_mult  of_int_hom.semiring_hom_axioms transpose_carrier_mat map_mat_transpose
    by (metis (no_types, lifting) N_carrier_mat) 
  have db: "det ?B = (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1)"
    using determinant_inc_mat_square by simp
  have lhn0: "(\<r> + \<Lambda> * (\<v> - 1)) > 0"
    using r_gzero by blast 
  have "(\<r> - \<Lambda>) > 0"
    using index_lt_replication zero_less_diff by blast  
  then have det_not_0:  "det ?B \<noteq> 0" using lhn0 db
    by (metis gr_implies_not0 mult_is_0 of_nat_eq_0_iff power_not_zero) 
  thus "det (of_int_hom.mat_hom N * (of_int_hom.mat_hom N)\<^sup>T) \<noteq> (0:: real)" using b_split by simp
qed


end


context simp_ordered_const_intersect_design
begin

lemma const_intersect_block_size_diff: 
  assumes "j' < \<b>"
  assumes "card (\<B>s ! j') = \<m>"
  assumes "j < \<b>"
  assumes "j \<noteq> j'"
  assumes "\<b> \<ge> 2"
  shows "card (\<B>s ! j) - \<m> > 0"
proof -
  obtain bl1 bl2 where "bl1 \<in># \<B>" and "\<B>s ! j' = bl1" and "bl2 \<in># \<B> - {#bl1#}" and "\<B>s ! j = bl2"
    using assms obtains_two_diff_index
    by fastforce 
  then have "\<m> < card (bl2)" 
    using max_one_block_size_inter assms(2) assms(5) by blast  
  thus ?thesis
    by (simp add: \<open>\<B>s ! j = bl2\<close>) 
qed

lemma sum_split_coeffs_0: 
  fixes c :: "nat \<Rightarrow> real"
  assumes "\<b> \<ge> 2"
  assumes "\<m> > 0"
  assumes "j' < \<b>"
  assumes "0 = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) +
           \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)"
  shows "c j' = 0"
proof (rule ccontr)
  assume cine0: "c j' \<noteq> 0"
  have innerge: "\<And> j . j < \<b>  \<Longrightarrow> (c j)^2 * (card (\<B>s ! j) - (int \<m>))  \<ge> 0" 
    using inter_num_le_block_size assms(1) by simp
  then have lhsge: "(\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) \<ge> 0"
    using sum_bounded_below[of "{0..<\<b>}" "0" "\<lambda> i. (c i)^2 * ((card (\<B>s ! i))- (int \<m>))"] by simp
  have "\<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2) \<ge> 0" by simp
  then have rhs0: "\<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2) = 0" 
    using assms(2) assms(4) lhsge by linarith
  then have "(\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) = 0" 
    using assms by linarith
  then have lhs0inner: "\<And> j . j < \<b>  \<Longrightarrow> (c j)^2 * (card (\<B>s ! j) - (int \<m>)) = 0" 
    using innerge sum_nonneg_eq_0_iff[of "{0..<\<b>}" "\<lambda> j . (c j)^2 * (card (\<B>s ! j) - (int \<m>))"] by simp
  thus False proof (cases "card (\<B>s ! j') = \<m>")
    case True
    then have cj0: "\<And> j. j \<in> {0..<\<b>} - {j'} \<Longrightarrow> (c j) = 0"
      using lhs0inner const_intersect_block_size_diff assms True by auto
    then have "(\<Sum> i \<in> {0..<\<b>} . c i) \<noteq> 0" 
      using sum.remove[of "{0..<\<b>}" "j'" "\<lambda> i. c i"] assms(3) cine0 cj0 by simp
    then show ?thesis using rhs0 assms by simp
  next
    case False
    then have ne: "(card (\<B>s ! j') - (int \<m>)) \<noteq> 0"
      by linarith  
    then have "(c j')^2 * (card (\<B>s ! j') - (int \<m>)) \<noteq> 0" using cine0
      by auto 
    then show ?thesis using lhs0inner assms(3) by auto
  qed
qed

(* BLOCK TOWN STATEMENT: In blocktown, the rule is that no two clubs have identical membership and 
every pair of clubs must share the exact same number, say k, members where k \<ge> 1. Prove: The number of clubs in blocktown is at most n
Based off  *)
theorem general_fishers_inequality:  "\<b> \<le> \<v>"
proof (cases "\<m> = 0 \<or> \<b> = 1")
  case True
  then show ?thesis using empty_inter_implies_b_lt_v v_non_zero
    by linarith
next
  case False
  then have mge: "\<m> > 0"
    by simp 
  then have bge: "\<b> \<ge> 2"
    using b_positive False blocks_list_length by linarith
  define NR where "NR \<equiv> map_mat (real_of_int) N"
  show ?thesis 
  proof (intro lin_bound_argument2[of NR])
    show "distinct (cols NR)" 
      using distinct_cols_N NR_def of_int_hom.vec_hom_set_distinct_iff
      by (metis map_vec_mat_cols) 
    show nrcm: "NR \<in> carrier_mat \<v> \<b>" using N_carrier_mat NR_def by simp
    have scalar_prod_real1: "\<And> i. i \<in> {0..<\<b>} \<Longrightarrow>  ((col NR i) \<bullet> (col NR i)) = card (\<B>s ! i)"
      unfolding NR_def using N_carrier_mat scalar_prod_inc_vec_block_size 
      by (simp) (metis of_int_of_nat_eq of_int_hom.vec_hom_smult le_refl) 
    have scalar_prod_real2: "\<And> i j. i \<in> {0..<\<b>} \<Longrightarrow> j \<in> {0..<\<b>} - {i} \<Longrightarrow> ((col NR i) \<bullet> (col NR j)) = \<m>"
      unfolding NR_def using N_carrier_mat  scalar_prod_inc_vec_const_inter
      by (simp)(metis dim_col of_int_of_nat_eq of_int_hom.vec_hom_smult le_refl) 
    show "\<And>f. vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. f (col NR j) * (col NR j) $ i) = 0\<^sub>v \<v> \<Longrightarrow> \<forall>v\<in>set (cols NR). f v = 0"
    proof (intro ballI)
      fix f v
      assume eq0: "vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. f (col NR j) * col NR j $ i) = 0\<^sub>v \<v>"
      assume vin: "v \<in> set (cols NR)"
      define c where "c \<equiv> (\<lambda> j. f (col NR j))"
      obtain j' where v_def: "col NR j' = v" and jvlt: "j' < dim_col NR"
        using vin by (metis cols_length cols_nth index_less_size_conv nth_index)
      have dim_col: "\<And>j. j \<in> {0..< \<b>} \<Longrightarrow> dim_vec (col NR j) = \<v>" using nrcm by auto
      have sum_simp: "\<And> j1 j2. (\<Sum>l \<in> {0..<\<v>} . c j1 * (col NR j1) $ l * (c j2 * (col NR j2) $ l)) = c j1 * c j2 *(\<Sum>l \<in> {0..<\<v>} .  (col NR j1) $ l * (col NR j2) $ l)"
        by (smt (verit, ccfv_SIG) ideal.scale_left_commute ideal.scale_scale sum.cong sum_distrib_left)
      have "0 = (vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. c j * (col NR j) $ i)) \<bullet> (vec \<v> (\<lambda>i. \<Sum>j = 0..<\<b>. c j * (col NR j) $ i))" 
        using vec_prod_zero eq0 c_def by simp
      also have "... = (\<Sum> l = 0..<\<v>. (\<Sum>j1 = 0..<\<b>. c j1 * (col NR j1) $ l) * (\<Sum>j2 = 0..<\<b>. c j2 * (col NR j2) $ l))"
        unfolding scalar_prod_def by simp
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (\<Sum> j1 \<in> {0..<\<b>} . (\<Sum> j2 \<in> {0..< \<b>}. c j1 * (col NR j1) $ l *  (c j2 * (col NR j2) $ l))))" 
        by (metis (no_types) sum_product)
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (\<Sum> j2 \<in> {0..< \<b>} . (\<Sum>l \<in> {0..<\<v>} . c j1 * (col NR j1) $ l * (c j2 * (col NR j2) $ l))))" 
        using sum_reorder_triple by simp
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (\<Sum> j2 \<in> {0..< \<b>} . c j1 * c j2 * (\<Sum>l \<in> {0..<\<v>} . (col NR j1) $ l * (col NR j2) $ l)))" 
        using sum_simp by simp
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (\<Sum> j2 \<in> {0..< \<b>} . c j1 * c j2 * ((col NR j1) \<bullet> (col NR j2))))" 
        unfolding scalar_prod_def using dim_col by auto
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . c j1 * c j1 * ((col NR j1) \<bullet> (col NR j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
      (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * ((col NR j1) \<bullet> (col NR j2))))" using double_sum_split_case by fastforce
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . c j1 * c j1 * (card (\<B>s ! j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
        (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * ((col NR j1) \<bullet> (col NR j2))))" 
        using scalar_prod_real1 by simp
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (c j1)^2 * (card (\<B>s ! j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
        (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * ((col NR j1) \<bullet> (col NR j2))))"
      by (metis power2_eq_square) 
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (c j1)^2 * (card (\<B>s ! j1))) + (\<Sum> j1 \<in> {0..<\<b>} . 
        (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2 * \<m>))"  using scalar_prod_real2  by auto
      also have "... = (\<Sum> j1 \<in> {0..<\<b>} . (c j1)^2 * (card (\<B>s ! j1))) + 
         \<m> * (\<Sum> j1 \<in> {0..<\<b>} . (\<Sum> j2 \<in> ({0..< \<b>} - {j1}) . c j1 * c j2))" 
        using double_sum_mult_hom[of "\<m>" "\<lambda> i j . c i * c j" "\<lambda> i.{0..<\<b>} - {i}" "{0..<\<b>}"]
        by (metis (no_types, lifting) mult_of_nat_commute sum.cong) 
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2 - (\<Sum> j \<in> {0..<\<b>} . c j * c j))" 
        using double_sum_split_square_diff by auto 
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))) + (-\<m>) * (\<Sum> j \<in> {0..<\<b>} . (c j)^2) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (simp add: algebra_simps power2_eq_square)
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))) + (\<Sum> j \<in> {0..<\<b>} . (-\<m>)* (c j)^2) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (simp add: sum_distrib_left) 
      also have "... = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * (card (\<B>s ! j))+ (-\<m>)* (c j)^2) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (metis (no_types) sum.distrib)
      finally have sum_rep: "0 = (\<Sum> j \<in> {0..<\<b>} . (c j)^2 * ((card (\<B>s ! j))- (int \<m>))) + 
         \<m> * ((\<Sum> j \<in> {0..<\<b>} . c j)^2)" by (simp add: algebra_simps)
      thus "f v = 0" using sum_split_coeffs_0[of "j'" "c"] mge bge jvlt nrcm  c_def v_def by simp
    qed
  qed
qed

end

context ordered_pairwise_balance
begin

corollary general_nonuniform_fishers: (* Only valid on incomplete designs *)
  assumes "\<Lambda> > 0" 
  assumes "\<And> bl. bl \<in># \<B> \<Longrightarrow> incomplete_block bl" (* i.e. not a super trivial design with only complete blocks *)
  shows "\<v> \<le> \<b>"
proof -
  have "mset (\<B>s*) = dual_blocks \<V> \<B>s" using dual_blocks_ordered_eq by simp
  then interpret des: simple_const_intersect_design "set [0..<(length \<B>s)]" "mset (\<B>s*)" \<Lambda> 
    using assms dual_is_simp_const_inter_des by simp
  interpret odes: simp_ordered_const_intersect_design "[0..<length \<B>s]" "\<B>s*" \<Lambda> 
    using distinct_upt des.wellformed by (unfold_locales) (blast)
  have "length (\<B>s*) \<le> length [0..<length \<B>s]" using odes.general_fishers_inequality
    using odes.blocks_list_length odes.points_list_length by presburger
  then have "\<v> \<le> length \<B>s"
    by (simp add: dual_blocks_len points_list_length) 
  then show ?thesis by auto
qed

corollary general_nonuniform_fishers_comp: 
  assumes "\<Lambda> > 0" 
  assumes "count \<B> \<V> < \<Lambda>" (* i.e. not a super trivial design with only complete blocks and single blocks *)
  shows "\<v> \<le> \<b>"
proof -
  define B where "B = (removeAll_mset \<V> \<B>)"
  have b_smaller: "size B \<le> \<b>" using B_def removeAll_size_lt by simp
  then have b_incomp: "\<And> bl. bl \<in># B \<Longrightarrow> card bl < \<v>"
    using wellformed B_def by (simp add: psubsetI psubset_card_mono) 
  have index_gt: "(\<Lambda> - (count \<B> \<V>)) > 0" using assms by simp 
  interpret pbd: pairwise_balance \<V> B "(\<Lambda> - (count \<B> \<V>))"
    using remove_all_complete_blocks_pbd B_def assms(2) by blast 
  obtain Bs where m: "mset Bs = B"
    using ex_mset by blast 
  interpret opbd: ordered_pairwise_balance \<V>s Bs "(\<Lambda> - (count \<B> \<V>))" 
    by (intro pbd.ordered_pbdI) (simp_all add: m distinct)
  have "\<v> \<le> (size B)" using b_incomp opbd.general_nonuniform_fishers
    using index_gt m by blast 
  then show ?thesis using b_smaller m by auto
qed

end
end