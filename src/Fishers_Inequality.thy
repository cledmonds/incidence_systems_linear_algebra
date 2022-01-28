theory Fishers_Inequality imports Rank_Argument_General
begin

(* Basic Fisher's Inequality *)
context ordered_bibd
begin

(* Note, some of this should be generalised *)

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
    by (simp add: points_list_length)
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
proof (intro upper_triangularI)
  fix i j assume a: "j < i" "i < dim_row (add_multiple_cols 1 0 [1..<dim_col M] M)"
  then have ine0: "i \<noteq> 0"
    by fastforce
  have ilt: "i < dim_row (N * N\<^sup>T)" using assms a
    by auto 
  then have jlt: "j < dim_col (N * N\<^sup>T)" using a
    by fastforce
  then have "i \<noteq> j" using a by simp
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = 0" using transform_N_step2_vals(4) ine0 ilt jlt
    using assms by blast 
qed

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
    by (simp add: points_list_length) 
  then have alll: "\<And> l. l \<in> set [1..<dim_col ?C] \<Longrightarrow> l < \<v>" by simp
  have cmc: "?C \<in> carrier_mat \<v> \<v>" using cm 
    by (simp add: add_row_to_multiple_carrier)
  have dimgt2: "dim_row ?D \<ge> 2"
    using t_lt_order
    by (simp add: points_list_length)  
  then have fstterm: "0 \<in> { 0 ..< dim_row ?D}" by (simp add: points_list_length)
  have "0 \<notin> set [1..<dim_col ?C]" by simp
  then have "det (N * N\<^sup>T) = det ?D" using add_multiple_cols_det alll cmc
    by (metis detbc) 
  also have "... = prod_list (diag_mat ?D)" using det_upper_triangular
    using transform_upper_triangular by fastforce 
  also have "... = (\<Prod> i = 0 ..< dim_row ?D. ?D $$ (i,i))" using prod_list_diag_prod by blast  
  also have "... = (\<Prod> i = 0 ..< \<v>. ?D $$ (i,i))"  by (simp add: points_list_length)  
  finally have "det (N * N\<^sup>T) = ?D $$ (0, 0) * (\<Prod> i =  1 ..< \<v>. ?D $$ (i,i))" 
    using dimgt2 by (simp add: prod.atLeast_Suc_lessThan v_non_zero) 
  then have "det (N * N\<^sup>T) = ((int \<r>) + (int \<Lambda>) * (\<v> - 1)) * (\<Prod> i = 1 ..< \<v>. ?D $$ (i,i))" 
    using d00 by simp
  then have "det (N * N\<^sup>T) = ((int \<r>) + (int \<Lambda>) * (\<v> - 1)) * (\<Prod> i = 1 ..< \<v>. ((int \<r>) - (int \<Lambda>)))" 
    using diagnon0 by simp
  then have "det (N * N\<^sup>T) = ((int \<r>) + (int \<Lambda>) * (\<v> - 1)) * ((int \<r>) - (int \<Lambda>))^(\<v> - 1)" by simp
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ((int \<r>) - (int \<Lambda>))^(\<v> - 1)"
    by simp
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ( \<r> - \<Lambda>)^(\<v> - 1)"
    using index_lt_replication
    by (metis (no_types, lifting) less_imp_le_nat of_nat_diff of_nat_mult of_nat_power)
  then show ?thesis by blast 
qed




theorem Fishers_Inequality_BIBD: "\<v> \<le> \<b>"
proof -
  let ?B = "map_mat (real_of_int) (N * N\<^sup>T)"
  have b_split: "?B = map_mat (real_of_int) N * map_mat (real_of_int) N\<^sup>T"
    using of_int_hom.ring_hom_axioms semiring_hom.mat_hom_mult
    using of_int_hom.semiring_hom_axioms transpose_carrier_mat by blast 
  have b_is_square: "dim_col ?B = \<v>"
    using transpose_N_mult_dim(2) by simp
  have b_dim_row: "dim_row ?B = \<v>"
    using dim_row_is_v by simp
  have dim_row_t: "dim_row N\<^sup>T = \<b>"
    by (simp add: dim_col_is_b) 
(* Calculate the determinant of B and show it is (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1) *)
  have db: "det ?B = (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1)"
    using determinant_inc_mat_square by simp
(* Have det(B) \<noteq> 0 as r > \<Lambda> *)
  have lhn0: "(\<r> + \<Lambda> * (\<v> - 1)) > 0"
    using r_gzero by blast 
  have "(\<r> - \<Lambda>) > 0"
    using index_lt_replication zero_less_diff by blast  
  then have det_not_0:  "det ?B \<noteq> 0" using lhn0 db
    by (metis gr_implies_not0 mult_is_0 of_nat_eq_0_iff power_not_zero) 
(* Conclude that B has rank \<v> - over what vector space? *)
  have "?B \<in> carrier_mat \<v> \<v>" using b_is_square by auto
  then have b_rank: "vec_space.rank \<v> ?B = \<v>"
    using vec_space.low_rank_det_zero det_not_0 by blast
(* As the rank of a product of matrices cannot exceed the rank of either factor, we have that thesis *)
  have "vec_space.rank \<v> ?B \<le> min (vec_space.rank \<v> (map_mat (real_of_int) N)) (vec_space.rank \<b> (map_mat (real_of_int) N\<^sup>T))"
    using N_carrier_mat dim_row_t rank_mat_mult_lt_min_rank_factor b_split
    by (metis carrier_mat_triv map_carrier_mat) 
  then have "\<v> \<le> min (vec_space.rank \<v> (map_mat (real_of_int) N)) (vec_space.rank \<b> (map_mat (real_of_int) N\<^sup>T))" 
    using b_rank by simp
  then have "\<v> \<le> vec_space.rank \<v> (map_mat (real_of_int) N)"
    by simp
  thus ?thesis using le_trans vec_space.rank_le_nc N_carrier_mat
    by (metis map_carrier_mat) 
qed

end

context simp_ordered_const_intersect_design
begin

lemma scalar_prod_incidence_vector_sq: 
  assumes "j < \<b>"
  shows "(col N j) \<bullet> (col N j) = card (\<B>s ! j)"
proof -
  have split: "{0..<\<v>} = {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} \<union>{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)}" by auto
  have inter: "{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} \<inter> {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)} = {}" by auto
  have one: "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} \<Longrightarrow> (col N j) $ i = 1"
    using N_col_def_indiv  assms atLeastLessThan_iff by blast  
  have zero: "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)} \<Longrightarrow> (col N j) $ i = 0"
     using N_col_def_indiv  assms atLeastLessThan_iff by blast 
   have "(col N j) \<bullet> (col N j) = (\<Sum> i \<in> {0..<\<v>} . (col N j) $ i * (col N j) $ i)" 
     using assms dim_vec_N_col scalar_prod_def
     by (metis (no_types, lifting) dim_vec_col sum.cong)
  also have "... = (\<Sum> i \<in> {0..<\<v>} . ((col N j) $ i)^2)"
    by (simp add: power2_eq_square) 
  also have "... = (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} . ((col N j) $ i)^2) + (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)} . ((col N j) $ i)^2)" 
    using split inter sum.union_disjoint[of " {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)}" "{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)}" "\<lambda> i . ((col N j) $ i)^2"]
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan) 
  also have "... = (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} . 1) + (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)} . 0)" 
    using one zero by simp
  also have "... = card {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)}"
    by simp 
  finally show ?thesis using card_block_points_filter assms by simp
qed

lemma scalar_prod_incidence_vector_diff: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "(cols N ! j1) \<bullet> (cols N ! j2) = \<m>"
proof -
  have split: "{0..<\<v>} = {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) } \<union> 
    {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j1) \<or> (\<V>s ! x) \<notin> (\<B>s ! j2)}" by auto
  have inter: "{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) } \<inter> 
    {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j1) \<or> (\<V>s ! x) \<notin> (\<B>s ! j2)} = {}" by auto
  have one1: "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2)} \<Longrightarrow> (col N j1) $ i = 1"
    using N_col_def_indiv  assms atLeastLessThan_iff by blast
  have "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2)} \<Longrightarrow> (col N j2) $ i = 1"
    using N_col_def_indiv  assms atLeastLessThan_iff by blast
  then have one: "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2)} \<Longrightarrow> (col N j1) $ i * (col N j2) $ i  = 1"
    using one1 by simp
  have zero: "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j1) \<or> (\<V>s ! x) \<notin> (\<B>s ! j2)} \<Longrightarrow> (col N j1) $ i * (col N j2) $ i = 0"
  proof -
    fix i assume "i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j1) \<or> (\<V>s ! x) \<notin> (\<B>s ! j2)}"
    then have "(col N j1) $ i = 0 \<or> (col N j2) $ i = 0" using N_col_def_indiv  assms atLeastLessThan_iff by blast 
    then show "col N j1 $ i * col N j2 $ i = 0" by simp
  qed
  have "(cols N ! j1) \<bullet> (cols N ! j2) = (\<Sum> i \<in> {0..<\<v>} . (cols N ! j1) $ i * (cols N ! j2) $ i)" using assms dim_vec_N_col scalar_prod_def
    by (metis (full_types)) 
  also have "... = (\<Sum> i \<in> {0..<\<v>} . (col N j1) $ i * (col N j2) $ i)" using assms by simp
  also have "... = (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) } . (col N j1) $ i * (col N j2) $ i) 
      + (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j1) \<or> (\<V>s ! x) \<notin> (\<B>s ! j2)} . (col N j1) $ i * (col N j2) $ i)" 
    using split inter sum.union_disjoint[of "{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) }" 
        "{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j1) \<or> (\<V>s ! x) \<notin> (\<B>s ! j2)}" "\<lambda> i . (col N j1) $ i * (col N j2) $ i"]
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan) 
  also have "... = (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) } . 1) 
      + (\<Sum> i \<in> {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j1) \<or> (\<V>s ! x) \<notin> (\<B>s ! j2)} . 0)" 
    using one zero
    by (metis (no_types, lifting) sum.cong) 
  also have "... = card {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) }"
    by simp 
  finally show ?thesis using inter_num_points_filter_def assms by simp
qed

(* BLOCK TOWN STATEMENT: In blocktown, the rule is that no two clubs have identical membership and 
every pair of clubs must share the exact same number, say k, members where k \<ge> 1. Prove: The number of clubs in blocktown is at most n
Based off  *)
theorem general_fishers_inequality:  "\<b> \<le> \<v>"
(* Question - does it have to be simple ? - yes! *)
proof (cases "\<m> = 0")
  case True
  then show ?thesis using empty_inter_implies_b_lt_v
    by simp 
next
  case False
  then have mge: "\<m> > 0"
    by simp 
  then show ?thesis proof (cases "\<b> = 1")
    case True
    then show ?thesis
      using v_non_zero by linarith 
  next
    case False
    then have bge: "\<b> \<ge> 2"
      using b_positive blocks_list_length by linarith
    have "distinct (cols N)" using distinct_cols_N by simp
    interpret vs: vec_space "TYPE(real)" \<v> .
    have dimv: "vs.dim = \<v>" using vs.dim_is_n by simp
    define NR where "NR \<equiv> map_mat (real_of_int) N"
    have fin: "finite (set (cols NR))"
      by simp
    have cv: "set (cols NR) \<subseteq> carrier_vec \<v>"
      by (metis cols_dim dim_row_is_v NR_def index_map_mat(2)) 
    have distinct_NR: "distinct (cols NR)" using distinct_cols_N NR_def of_int_hom.vec_hom_set_distinct_iff
      by (metis map_vec_mat_cols) 
    have lidpt: "vs.lin_indpt (set (cols NR))"
    proof (rule ccontr)
      assume "\<not> vs.lin_indpt (set (cols NR))"
      then have "vs.lin_dep (set (cols NR))" by simp
      from vs.finite_lin_dep[OF fin this cv]
      obtain a v where comb: "vs.lincomb a (set (cols NR)) = 0\<^sub>v \<v>" and vin: "v \<in> (set (cols NR))" and avne: "a v \<noteq> 0" by auto 
      define c where ceq: "c = (\<lambda> i. a ((cols NR) ! i))"
      then have listcomb: "vs.lincomb_list c (cols NR) = 0\<^sub>v \<v>" using vs.lincomb_as_lincomb_list_distinct[OF cv distinct_NR] comb by simp
      obtain i' where vi: "(cols NR) ! i' = v" and ilt: "i' < length (cols NR)" using vin
        by (metis in_set_conv_nth) 
      then have iin: "i' \<in> {0..<\<b>}" using NR_def index_map_mat by simp 
      then have vi_alt: "v = col NR i'" using vi ilt NR_def index_map_mat by simp
      have cine0: "c i' \<noteq> 0" using ceq avne vi by simp
      have nth: "\<And> j. j < \<b> \<Longrightarrow> map (\<lambda>i. c i \<cdot>\<^sub>v (cols NR) ! i) [0..<\<b>] ! j = c j \<cdot>\<^sub>v (cols NR) ! j"
        by simp
      have inner_sum: "\<And> i f . i \<in> {0..<\<b>} \<Longrightarrow> (\<Sum> j \<in> {0..<\<b>} . f j) = f i + (\<Sum>j \<in> ({0..<\<b>} - {i}). f j)"
        using sum.remove
        by (metis blocks_list_length dual_sys.finite_sets) 
      have "(\<Sum> i \<in> {0..<\<b>} . c i)^2 = (\<Sum> i \<in> {0..<\<b>} . c i * c i) + (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j))" 
        using double_sum_split_case_square by fastforce
      then have alt_rep: "(\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j)) = (\<Sum> i \<in> {0..<\<b>} . c i)^2 - (\<Sum> i \<in> {0..<\<b>} . c i * c i)" 
        by linarith 
      have dim: "\<And> j. j < \<b> \<Longrightarrow>  dim_vec (c j \<cdot>\<^sub>v (col NR j)) = \<v>" using cv
        using carrier_dim_vec nth_mem by (simp add: points_list_length NR_def) 
      then have cv2: "\<And> j. j < \<b> \<Longrightarrow> (col NR j) \<in> carrier_vec \<v>"
        by (simp add: carrier_dim_vec NR_def) 
      then have sum_simp: "\<And> i j . i \<in>{0..<\<b>} \<Longrightarrow> j \<in> {0..<\<b>} \<Longrightarrow> 
        (\<Sum>l \<in> {0..<\<v>} . ((c i \<cdot>\<^sub>v (col NR i)) $ l) *  ((c j \<cdot>\<^sub>v (col NR j)) $ l)) = c i * c j * ((col NR i) \<bullet> (col NR j)) "
      proof - 
        fix i j assume "i \<in>{0..<\<b>}" "j \<in> {0..<\<b>}"
        then show "(\<Sum>l \<in> {0..<\<v>} . ((c i \<cdot>\<^sub>v (col NR i)) $ l) *  ((c j \<cdot>\<^sub>v (col NR j)) $ l)) = c i * c j * ((col NR i) \<bullet> (col NR j))"
          using smult_scalar_prod_sum[of "(col NR i)" "\<v>" "(col NR j)"  "c i" "c j" ]  cv2 by simp
      qed
      have scalar_prod_real1: "\<And> i. i \<in> {0..<\<b>} \<Longrightarrow>  ((col NR i) \<bullet> (col NR i)) = card (\<B>s ! i)"
        unfolding NR_def using N_carrier_mat scalar_prod_incidence_vector_sq 
        by (simp) (metis of_int_of_nat_eq of_int_hom.vec_hom_smult le_refl) 
      have scalar_prod_real2: "\<And> i j. i \<in> {0..<\<b>} \<Longrightarrow> j \<in> {0..<\<b>} - {i} \<Longrightarrow> ((col NR i) \<bullet> (col NR j)) = \<m>"
        unfolding NR_def using N_carrier_mat  scalar_prod_incidence_vector_diff
        by (simp)(metis dim_col of_int_of_nat_eq of_int_hom.vec_hom_smult le_refl )
      have dim2: "\<And> j. j < \<b> \<Longrightarrow>  dim_vec (c j \<cdot>\<^sub>v (cols NR) ! j) = \<v>" using cv
        using carrier_dim_vec nth_mem by (simp add: points_list_length NR_def) 
      have "0 = (vs.lincomb_list c (cols NR)) \<bullet> (vs.lincomb_list c (cols NR))" using vec_prod_zero listcomb by simp
      also have "... = (vs.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (cols NR) ! i) [0..<\<b>])) \<bullet> (vs.sumlist (map (\<lambda>j. c j \<cdot>\<^sub>v (cols NR) ! j) [0..<\<b>]))"
        using vs.lincomb_list_def NR_def index_map_mat(2) by simp
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (vs.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (cols NR) ! i) [0..<\<b>])) $ l * (vs.sumlist (map (\<lambda>j. c j \<cdot>\<^sub>v (cols NR) ! j) [0..<\<b>])) $ l)"
        using scalar_prod_def dim listcomb vs.lincomb_list_def NR_def index_map_mat by auto 
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (sum (\<lambda> i. (c i \<cdot>\<^sub>v (cols NR) ! i) $ l) {0..<\<b>}) * (sum (\<lambda> j. (c j \<cdot>\<^sub>v (cols NR) ! j) $ l) {0..<\<b>}))"
        using vs.sumlist_nth nth dim2 by simp
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> {0..< \<b>}. ((c i \<cdot>\<^sub>v (cols NR) ! i) $ l) *  ((c j \<cdot>\<^sub>v (cols NR) ! j) $ l))))" 
        by (metis (no_types) sum_product)
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> {0..< \<b>}. ((c i \<cdot>\<^sub>v (col NR i)) $ l) *  ((c j \<cdot>\<^sub>v (col NR j)) $ l))))" 
        using cols_nth NR_def index_map_mat by auto
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> {0..< \<b>} . (\<Sum>l \<in> {0..<\<v>} . ((c i \<cdot>\<^sub>v (col NR i)) $ l) *  ((c j \<cdot>\<^sub>v (col NR j)) $ l))))" 
        using sum_reorder_triple by simp
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> {0..< \<b>} . c i * c j * ((col NR i) \<bullet> (col NR j))))" 
        using sum_simp by simp
      also have "... = (\<Sum> i \<in> {0..<\<b>} . c i * c i * ((col NR i) \<bullet> (col NR i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * ((col NR i) \<bullet> (col NR j))))" using double_sum_split_case by fastforce
      also have "... = (\<Sum> i \<in> {0..<\<b>} . c i * c i * (card (\<B>s ! i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * ((col NR i) \<bullet> (col NR j))))" 
        using scalar_prod_real1 by simp
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * ((col NR i) \<bullet> (col NR j))))"
        by (metis power2_eq_square) 
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * \<m>))"  using scalar_prod_real2  by auto
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + 
         \<m> * (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j))" 
        using double_sum_mult_hom[of "\<m>" "\<lambda> i j . c i * c j" "\<lambda> i.{0..<\<b>} - {i}" "{0..<\<b>}"]
        by (metis (no_types, lifting) mult_of_nat_commute sum.cong) 
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + 
         \<m> * ((\<Sum> i \<in> {0..<\<b>} . c i)^2 - (\<Sum> i \<in> {0..<\<b>} . c i * c i))" using alt_rep by simp
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + (-\<m>) * (\<Sum> i \<in> {0..<\<b>} . (c i)^2) + 
         \<m> * ((\<Sum> i \<in> {0..<\<b>} . c i)^2)" by (simp add: algebra_simps power2_eq_square)
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + (\<Sum> i \<in> {0..<\<b>} . (-\<m>)* (c i)^2) + 
         \<m> * ((\<Sum> i \<in> {0..<\<b>} . c i)^2)" by (simp add: sum_distrib_left) 
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))+ (-\<m>)* (c i)^2) + 
         \<m> * ((\<Sum> i \<in> {0..<\<b>} . c i)^2)" by (metis (no_types) sum.distrib)
      finally have sum_rep: "0 = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * ((card (\<B>s ! i))- (int \<m>))) + 
         \<m> * ((\<Sum> i \<in> {0..<\<b>} . c i)^2)" by (simp add: algebra_simps)
      have "\<And> i . i < \<b>  \<Longrightarrow> card (\<B>s ! i) \<ge> (int \<m>)"  using inter_num_le_block_size bge
        by simp 
      then have "\<And> i . i < \<b>  \<Longrightarrow> card (\<B>s ! i) - (int \<m>) \<ge> 0"
        by simp 
      then have innerge: "\<And> i . i < \<b>  \<Longrightarrow> (c i)^2 * (card (\<B>s ! i) - (int \<m>))  \<ge> 0" by simp
      then have lhsge: "(\<Sum> i \<in> {0..<\<b>} . (c i)^2 * ((card (\<B>s ! i))- (int \<m>))) \<ge> 0" 
        using sum_bounded_below[of "{0..<\<b>}" "0" "\<lambda> i. (c i)^2 * ((card (\<B>s ! i))- (int \<m>))"] by simp
      have "\<m> * ((\<Sum> i \<in> {0..<\<b>} . c i)^2) \<ge> 0" by simp
      then have rhs0: "\<m> * ((\<Sum> i \<in> {0..<\<b>} . c i)^2) = 0" using sum_rep lhsge
        by linarith
      then have rhs02: "(\<Sum> i \<in> {0..<\<b>} . c i) = 0" using mge by simp
      then have lhs0: "(\<Sum> i \<in> {0..<\<b>} . (c i)^2 * ((card (\<B>s ! i))- (int \<m>))) = 0" 
        using sum_rep rhs0 by linarith
      then have lhs0inner: "\<And> i . i < \<b>  \<Longrightarrow> (c i)^2 * (card (\<B>s ! i) - (int \<m>)) = 0" 
        using innerge sum_nonneg_eq_0_iff[of "{0..<\<b>}" "\<lambda> i . (c i)^2 * (card (\<B>s ! i) - (int \<m>))"] by simp
      thus False
      proof (cases "card (\<B>s ! i') = \<m>")
        case True
        then have "(c i')^2 * (card (\<B>s ! i') - (int \<m>)) = 0" by simp
        have mlt: "\<And> i. i \<in> {0..<\<b>} \<Longrightarrow> i \<noteq> i' \<Longrightarrow> \<m> < card (\<B>s ! i)" 
          using max_one_block_size_inter bge True
          by (metis atLeastLessThan_iff iin obtains_two_diff_index) 
        then have "\<And> i. i \<in> {0..<\<b>} \<Longrightarrow> i \<noteq> i' \<Longrightarrow> (card (\<B>s ! i) - (int \<m>)) > 0" by simp
        then have "\<And> i. i \<in> {0..<\<b>} \<Longrightarrow> i \<noteq> i' \<Longrightarrow> (c i)^2 = 0" using lhs0inner
          by (smt (verit) mlt atLeastLessThan_iff diff_is_0_eq diffs0_imp_equal less_not_refl 
              less_or_eq_imp_le mult_eq_0_iff of_int_of_nat_eq of_nat_diff of_nat_eq_0_iff)
        then have "\<And> i. i \<in> {0..<\<b>} \<Longrightarrow> i \<noteq> i' \<Longrightarrow> (c i) = 0" by simp
        then have ci0: "\<And> i. i \<in> {0..<\<b>} - {i'} \<Longrightarrow> (c i) = 0" by simp
        have "(\<Sum> i \<in> {0..<\<b>} . c i) = c i' + (\<Sum> i \<in> {0..<\<b>} - {i'} . c i)" using iin
          by (metis inner_sum)
        also have "... = c i' + (\<Sum> i \<in> {0..<\<b>} - {i'} . 0)" using ci0 by simp
        also have "... = c i'" by simp
        finally have "(\<Sum> i \<in> {0..<\<b>} . c i) \<noteq> 0" using cine0 by simp
        then show ?thesis using rhs02 by simp
      next
        case False
        then have ne: "(card (\<B>s ! i') - (int \<m>)) \<noteq> 0"
          by linarith  
        have "(c i')^2 \<noteq>0" using cine0 by simp
        then have "(c i')^2 * (card (\<B>s ! i') - (int \<m>)) \<noteq> 0" using ne
          by auto 
        then show ?thesis using lhs0inner iin by auto
      qed
    qed
    have "distinct ((cols NR))"
      by (simp add: distinct_NR) 
    thus ?thesis using vs.lin_indpt_dim_col_lt_dim[of "NR" "\<b>"] lidpt NR_def N_carrier_mat dimv by simp
  qed
qed

end
(* Can be moved into design ops *)

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