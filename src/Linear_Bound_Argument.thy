theory Linear_Bound_Argument imports Dual_Systems Jordan_Normal_Form.Determinant 
Jordan_Normal_Form.DL_Rank Jordan_Normal_Form.Ring_Hom_Matrix BenOr_Kozen_Reif.More_Matrix
begin

context comm_monoid_add
begin

lemma sum_reorder_triple: "(\<Sum> l \<in> A . (\<Sum> i \<in> B . (\<Sum> j \<in> C . g l i j))) = (\<Sum> i \<in> B . (\<Sum> j \<in> C . (\<Sum> l \<in> A . g l i j)))"
proof -
  have "(\<Sum> l \<in> A . (\<Sum> i \<in> B . (\<Sum> j \<in> C . g l i j))) = (\<Sum>i \<in> B . (\<Sum> l \<in> A  . (\<Sum> j \<in> C . g l i j)))"
    using sum.swap[of "(\<lambda> l i . (\<Sum> j \<in> C . g l i j))"  "B" "A"] by simp
  also have "...  = (\<Sum>i \<in> B . (\<Sum> j \<in> C . (\<Sum>l \<in> A . g l i j)))" using sum.swap by metis
  finally show ?thesis by simp
qed

lemma double_sum_mult_hom: "(\<Sum> i \<in> A . (\<Sum> j \<in> g i . (k ::real) * (f i j))) = k* (\<Sum> i \<in> A . (\<Sum> j \<in> g i . f i j))"
  by (simp add: mult_hom.hom_sum)

lemma double_sum_split_case: 
  assumes "finite A"
  shows "(\<Sum> i \<in> A . (\<Sum> j \<in> A . f i j)) = (\<Sum> i \<in> A . (f i i)) + (\<Sum> i \<in> A . (\<Sum> j \<in> (A - {i}) . f i j))" 
proof -
  have "\<And> i. i \<in> A \<Longrightarrow> (\<Sum> j \<in> A . f i j) = f i i + (\<Sum> j \<in> (A - {i}) . f i j)" using sum.remove assms
    by metis 
  then have "(\<Sum> i \<in> A . (\<Sum> j \<in> A . f i j)) = (\<Sum> i \<in> A . f i i + (\<Sum> j \<in> (A - {i}) . f i j))" by simp
  then show ?thesis
    by (simp add: sum.distrib) 
qed
               
lemma double_sum_split_case2: "(\<Sum> i \<in> A . (\<Sum> j \<in> A . g i j)) = (\<Sum> i \<in> A . (g i i)) + (\<Sum> i \<in> A . (\<Sum> j \<in> {a \<in> A . a \<noteq> i} . g i j)) " 
proof - 
  have "\<And> i. A = {a \<in> A . a = i} \<union> {a \<in> A . a \<noteq> i}" by auto
  then have part: "\<And> i. i \<in> A \<Longrightarrow> A = {i} \<union> {a \<in> A . a \<noteq> i}" by auto
  have empt:"\<And> i. {i} \<inter> {a \<in> A . a \<noteq> i} = {}"
    by simp 
  then have "(\<Sum> i \<in> A . (\<Sum> j \<in> A . g i j)) = (\<Sum> i \<in> A . ((\<Sum> j \<in> {i} . g i j) + (\<Sum> j \<in> {a \<in> A . a \<noteq> i} . g i j)))" using part
    by (smt (verit) finite_Un local.sum.cong local.sum.infinite local.sum.union_disjoint) 
  also have "... = (\<Sum> i \<in> A . ((\<Sum> j \<in> {i} . g i j))) + (\<Sum> i \<in> A . (\<Sum> j \<in> {a \<in> A . a \<noteq> i} . g i j))"
    by (simp add: local.sum.distrib) 
  finally show ?thesis by simp
qed
end

context comm_ring_1
begin

lemma double_sum_split_case_square: 
  assumes "finite A"
  shows "(\<Sum> i \<in> A . f i )^2 = (\<Sum> i \<in> A . (f i * f i)) + (\<Sum> i \<in> A . (\<Sum> j \<in> (A - {i}) . f i * f j))" 
proof -
  have "(\<Sum> i \<in> A . f i )^2 = (\<Sum> i \<in> A . f i) * (\<Sum> i \<in> A . f i)"
    using power2_eq_square by blast
  then have "(\<Sum> i \<in> A . f i) * (\<Sum> i \<in> A . f i) = (\<Sum> i \<in> A . f i) * (\<Sum> j \<in> A . f j)" by simp
  also have "... = (\<Sum> i \<in> A . f i * (\<Sum> j \<in> A . f j))" using sum_distrib_right by simp
  also have "... = (\<Sum> i \<in> A .  (\<Sum> j \<in> A . f i * f j))" using sum_distrib_left by metis 
  finally have "(\<Sum> i \<in> A . f i) * (\<Sum> i \<in> A . f i) = (\<Sum> i \<in> A . (f i * f i)) + (\<Sum> i \<in> A . (\<Sum> j \<in> (A - {i}) . f i * f j))" 
    using assms double_sum_split_case[of "A" "\<lambda> i j . f i * f j"]
    using \<open>(\<Sum>i\<in>A. f i * sum f A) = (\<Sum>i\<in>A. \<Sum>j\<in>A. f i * f j)\<close> \<open>sum f A * sum f A = (\<Sum>i\<in>A. f i * sum f A)\<close> by presburger 
  then show ?thesis
    using power2_eq_square by presburger 
qed

end


(* Additional matrix operation reasoning *)

lemma index_mat_addrow_basic [simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> addrow a k l A $$ (i,j) = (if k = i then 
    ( a * (A $$ (l,j)) + (A $$ (i,j))) else A $$ (i,j))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> addrow a i l A $$ (i,j) = (a * (A $$ (l,j)) + (A $$ (i,j)))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> i \<Longrightarrow> addrow a k l A $$ (i,j) = A $$(i,j)"
  "dim_row (addrow a k l A) = dim_row A" "dim_col (addrow a k l A) = dim_col A"
  unfolding mat_addrow_def by auto

fun add_col_to_multiple :: "'a :: semiring_1 \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
"add_col_to_multiple a [] l A = A" | 
"add_col_to_multiple a (k # ks) l A = (addcol a k l (add_col_to_multiple a ks l A))"

fun add_row_to_multiple :: "'a :: semiring_1 \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
"add_row_to_multiple a [] l A = A" | 
"add_row_to_multiple a (k # ks) l A = (addrow a k l (add_row_to_multiple a ks l A))"

fun add_multiple_rows :: "'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
"add_multiple_rows a k [] A = A" | 
"add_multiple_rows a k (l # ls) A = (addrow a k l (add_multiple_rows a k ls A))"

fun add_multiple_cols :: "'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
"add_multiple_cols a k [] A = A" | 
"add_multiple_cols a k (l # ls) A = (addcol a k l (add_multiple_cols a k ls A))"

lemma add_multiple_rows_dim [simp]: 
"dim_row (add_multiple_rows a k ls A) = dim_row A"
"dim_col (add_multiple_rows a k ls A) = dim_col A"
  by (induct ls) simp_all

lemma add_multiple_rows_index_unchanged [simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> i \<Longrightarrow> add_multiple_rows a k ls A $$ (i,j) = A $$(i,j)"
  by (induct ls) (simp_all)

lemma add_multiple_rows_index_eq: 
  assumes "i < dim_row A" and "j < dim_col A" and "i \<notin> set ls" and "\<And> l . l \<in> set ls \<Longrightarrow> l < dim_row A"
  shows "add_multiple_rows a i ls A $$ (i,j) = (\<Sum>l\<leftarrow>ls. a * A $$(l,j)) + A$$(i,j)"
  using assms
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  then have ne: "i \<noteq> aa"
    by auto 
  have lt: "aa < dim_row A" using assms
    by (simp add: Cons.prems(4))
  have "(add_multiple_rows a i (aa # ls) A) $$ (i, j) = (addrow a i aa (add_multiple_rows a i ls A)) $$ (i, j)" by simp
  also have "... = a * add_multiple_rows a i ls A $$ (aa, j)  + (add_multiple_rows a i ls A) $$ (i, j)" 
    using assms index_mat_addrow_basic(2)[of "i" "(add_multiple_rows a i ls A)" "j" "a" "aa"] by simp
  also have "... = a * A $$(aa, j) + (add_multiple_rows a i ls A) $$ (i, j)" using lt ne
    by (simp add:  assms(2)) 
  also have "... = a * A $$(aa, j) + (\<Sum>l\<leftarrow>ls. a * A $$ (l, j)) + A $$ (i, j)" using Cons.hyps
    by (metis (mono_tags, lifting) Cons.prems(3) Cons.prems(4) ab_semigroup_add_class.add_ac(1) assms(1) assms(2) list.set_intros(2)) 
  finally have "(add_multiple_rows a i (aa # ls) A) $$ (i, j) = (\<Sum>l\<leftarrow>(aa #ls). a * A $$ (l, j)) + A $$ (i, j)"
    by simp 
  then show ?case by simp
qed

lemma add_multiple_cols_dim [simp]: 
"dim_row (add_multiple_cols a k ls A) = dim_row A"
"dim_col (add_multiple_cols a k ls A) = dim_col A"
  by (induct ls) simp_all

lemma add_multiple_cols_index_unchanged [simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> j \<Longrightarrow> add_multiple_cols a k ls A $$ (i,j) = A $$(i,j)"
  by (induct ls) (simp_all)

lemma add_multiple_cols_index_eq: 
  assumes "i < dim_row A" and "j < dim_col A" and "j \<notin> set ls" and "\<And> l . l \<in> set ls \<Longrightarrow> l < dim_col A"
  shows "add_multiple_cols a j ls A $$ (i,j) = (\<Sum>l\<leftarrow>ls. a * A $$(i,l)) + A$$(i,j)"
  using assms
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  then have ne: "j \<noteq> aa"
    by auto 
  have lt: "aa < dim_col A" using assms
    by (simp add: Cons.prems(4))
  have "(add_multiple_cols a j (aa # ls) A) $$ (i, j) = (addcol a j aa (add_multiple_cols a j ls A)) $$ (i, j)" by simp
  also have "... = a * add_multiple_cols a j ls A $$ (i, aa)  + (add_multiple_cols a j ls A) $$ (i, j)" 
    using assms index_mat_addcol by simp
  also have "... = a * A $$(i, aa) + (add_multiple_cols a j ls A) $$ (i, j)" using lt ne
    by (simp add: assms(1))
  also have "... = a * A $$(i, aa) + (\<Sum>l\<leftarrow>ls. a * A $$ (i, l)) + A $$ (i, j)" using Cons.hyps
    by (metis (mono_tags, lifting) Cons.prems(3) Cons.prems(4) ab_semigroup_add_class.add_ac(1) assms(1) assms(2) list.set_intros(2)) 
  finally have "(add_multiple_cols a j (aa # ls) A) $$ (i, j) = (\<Sum>l\<leftarrow>(aa #ls). a * A $$ (i, l)) + A $$ (i, j)"
    by simp 
  then show ?case by simp
qed


lemma add_row_to_multiple_dim [simp]: 
"dim_row (add_row_to_multiple a ks l A) = dim_row A"
"dim_col (add_row_to_multiple a ks l A) = dim_col A"
  by (induct ks) simp_all

lemma add_row_to_multiple_index_unchanged [simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> i \<notin> set ks \<Longrightarrow> add_row_to_multiple a ks l A $$ (i,j) = A $$(i,j)"
  by (induct ks) simp_all

lemma add_row_to_multiple_index_change: 
  assumes "i < dim_row A" and "j < dim_col A" and "i \<in> set ks" and "distinct ks" and "l \<notin> set ks" and "l < dim_row A"
  shows "add_row_to_multiple a ks l A $$ (i,j) = (a * A$$(l, j)) + A$$(i,j)"
  using assms
proof (induct ks)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  then have lnotin: "l \<notin> set ls" using assms by simp
  then show ?case 
  proof (cases "i = aa")
    case True
    then have inotin: "i \<notin> set ls" using assms
      using Cons.prems(4) by fastforce 
    have "add_row_to_multiple a (aa # ls) l A $$ (i, j) = (addrow a aa l (add_row_to_multiple a ls l A)) $$ (i, j)" by simp
    also have "... = (a * ((add_row_to_multiple a ls l A) $$ (l,j)) + ((add_row_to_multiple a ls l A) $$ (i,j)))"
      using True assms(1) assms(2) by auto
    also have "... = a* A $$ (l, j) + ((add_row_to_multiple a ls l A) $$ (i,j))" using assms lnotin
      by simp 
    finally have "add_row_to_multiple a (aa # ls) l A $$ (i, j) = a* A $$ (l,j) + A $$ (i, j)" using inotin assms by simp
    then show ?thesis by simp
  next
    case False
    then have iin: "i \<in> set ls" using assms
      by (meson Cons.prems(3) set_ConsD) 
    have "add_row_to_multiple a (aa # ls) l A $$ (i, j) = (addrow a aa l (add_row_to_multiple a ls l A)) $$ (i, j)" by simp
    also have "... =  ((add_row_to_multiple a ls l A) $$ (i,j))"
      using False assms by auto
    finally have "add_row_to_multiple a (aa # ls) l A $$ (i, j) =  a * A $$ (l, j) + A $$ (i, j)" using Cons.hyps
      by (metis Cons.prems(4) assms(1) assms(2) assms(6) distinct.simps(2) iin lnotin) 
    then show ?thesis by simp
  qed
qed


lemma add_col_to_multiple_dim [simp]: 
"dim_row (add_col_to_multiple a ks l A) = dim_row A"
"dim_col (add_col_to_multiple a ks l A) = dim_col A"
  by (induct ks) simp_all

lemma add_col_to_multiple_index_unchanged [simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> j \<notin> set ks \<Longrightarrow> add_col_to_multiple a ks l A $$ (i,j) = A $$(i,j)"
  by (induct ks) simp_all

lemma add_col_to_multiple_index_change: 
  assumes "i < dim_row A" and "j < dim_col A" and "j \<in> set ks" and "distinct ks" and "l \<notin> set ks" and "l < dim_col A"
  shows "add_col_to_multiple a ks l A $$ (i,j) = (a * A$$(i, l)) + A$$(i,j)"
  using assms
proof (induct ks)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  then have lnotin: "l \<notin> set ls" using assms by simp
  then show ?case 
  proof (cases "j = aa")
    case True
    then have inotin: "j \<notin> set ls" using assms
      using Cons.prems(4) by fastforce 
    have "add_col_to_multiple a (aa # ls) l A $$ (i, j) = (addcol a aa l (add_col_to_multiple a ls l A)) $$ (i, j)" by simp
    also have "... = (a * ((add_col_to_multiple a ls l A) $$ (i,l)) + ((add_col_to_multiple a ls l A) $$ (i,j)))"
      using True assms(1) assms(2) by auto
    also have "... = a* A $$ (i, l) + ((add_col_to_multiple a ls l A) $$ (i,j))" using assms lnotin
      by simp 
    finally have "add_col_to_multiple a (aa # ls) l A $$ (i, j) = a* A $$ (i,l) + A $$ (i, j)" using inotin assms by simp
    then show ?thesis by simp
  next
    case False
    then have iin: "j \<in> set ls" using assms
      by (meson Cons.prems(3) set_ConsD) 
    have "add_col_to_multiple a (aa # ls) l A $$ (i, j) = (addcol a aa l (add_col_to_multiple a ls l A)) $$ (i, j)" by simp
    also have "... =  ((add_col_to_multiple a ls l A) $$ (i,j))"
      using False assms by auto
    finally have "add_col_to_multiple a (aa # ls) l A $$ (i, j) =  a * A $$ (i, l) + A $$ (i, j)" using Cons.hyps
      by (metis Cons.prems(4) assms(1) assms(2) assms(6) distinct.simps(2) iin lnotin) 
    then show ?thesis by simp
  qed
qed


(* Determinant lemmas *)

lemma add_row_to_multiple_carrier: 
  "A \<in> carrier_mat n n \<Longrightarrow> add_row_to_multiple a ks l A \<in> carrier_mat n n"
  by (metis add_row_to_multiple_dim(1) add_row_to_multiple_dim(2) carrier_matD(1) carrier_matD(2) carrier_matI)

lemma add_col_to_multiple_carrier: 
  "A \<in> carrier_mat n n \<Longrightarrow> add_col_to_multiple a ks l A \<in> carrier_mat n n"
  by (metis add_col_to_multiple_dim carrier_matD(1) carrier_matD(2) carrier_matI)

lemma add_multiple_rows_carrier: 
  "A \<in> carrier_mat n n \<Longrightarrow> add_multiple_rows a k ls A \<in> carrier_mat n n"
  by (metis add_multiple_rows_dim carrier_matD(1) carrier_matD(2) carrier_matI)

lemma add_multiple_cols_carrier: 
  "A \<in> carrier_mat n n \<Longrightarrow> add_multiple_cols a k ls A \<in> carrier_mat n n"
  by (metis add_multiple_cols_dim carrier_matD(1) carrier_matD(2) carrier_matI)

lemma add_row_to_multiple_det:
  assumes "l \<notin> set ks" and "l < n" and "A \<in> carrier_mat n n"
  shows "det (add_row_to_multiple a ks l A) = det A"
  using assms
proof (induct ks)
  case Nil
  then show ?case by simp
next
  case (Cons aa ks)
  have ne: "aa \<noteq> l"
    using Cons.prems(1) by auto 
  have "det (add_row_to_multiple a (aa # ks) l A) = det (addrow a aa l (add_row_to_multiple a ks l A))" by simp
  also have "... = det (add_row_to_multiple a ks l A)" by (meson det_addrow add_row_to_multiple_carrier ne assms)
  finally have "det (add_row_to_multiple a (aa # ks) l A) = det A" using Cons.hyps assms by (metis Cons.prems(1) list.set_intros(2))
  then show ?case by simp
qed

lemma add_col_to_multiple_det:
  assumes "l \<notin> set ks" and "l < n" and "A \<in> carrier_mat n n"
  shows "det (add_col_to_multiple a ks l A) = det A"
  using assms
proof (induct ks)
  case Nil
  then show ?case by simp
next
  case (Cons aa ks)
  have ne: "aa \<noteq> l"
    using Cons.prems(1) by auto 
  have "det (add_col_to_multiple a (aa # ks) l A) = det (addcol a aa l (add_col_to_multiple a ks l A))" by simp
  also have "... = det (add_col_to_multiple a ks l A)" by (meson det_addcol add_col_to_multiple_carrier ne assms)
  finally have "det (add_col_to_multiple a (aa # ks) l A) = det A" using Cons.hyps assms by (metis Cons.prems(1) list.set_intros(2))
  then show ?case by simp
qed

lemma add_multiple_cols_det:
  assumes "k \<notin> set ls" and "\<And>l. l \<in> set ls \<Longrightarrow> l < n" and "A \<in> carrier_mat n n"
  shows "det (add_multiple_cols a k ls A) = det A"
  using assms
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  have ne: "aa \<noteq> k"
    using Cons.prems(1) by auto 
  have "det (add_multiple_cols a k (aa # ls) A) = det (addcol a k aa (add_multiple_cols a k ls A))" by simp
  also have "... = det (add_multiple_cols a k ls A)" using det_addcol add_multiple_cols_carrier ne assms
    by (metis Cons.prems(2) list.set_intros(1)) 
  finally have "det (add_multiple_cols a k (aa # ls) A) = det A" 
    using Cons.hyps assms by (metis Cons.prems(1) Cons.prems(2) list.set_intros(2)) 
  then show ?case by simp
qed

lemma add_multiple_rows_det:
  assumes "k \<notin> set ls" and "\<And>l. l \<in> set ls \<Longrightarrow> l < n" and "A \<in> carrier_mat n n"
  shows "det (add_multiple_rows a k ls A) = det A"
  using assms
proof (induct ls)
  case Nil
  then show ?case by simp
next
  case (Cons aa ls)
  have ne: "aa \<noteq> k"
    using Cons.prems(1) by auto 
  have "det (add_multiple_rows a k (aa # ls) A) = det (addrow a k aa (add_multiple_rows a k ls A))" by simp
  also have "... = det (add_multiple_rows a k ls A)" using det_addrow add_multiple_rows_carrier ne assms
    by (metis Cons.prems(2) list.set_intros(1)) 
  finally have "det (add_multiple_rows a k (aa # ls) A) = det A" 
    using Cons.hyps assms by (metis Cons.prems(1) Cons.prems(2) list.set_intros(2)) 
  then show ?case by simp
qed

lemma rank_mat_mult_lt_min_rank_factor: 
  fixes A :: "'a::{conjugatable_ordered_field} mat"
  assumes "A \<in> carrier_mat n m"
  assumes "B \<in> carrier_mat m nc" 
  shows "vec_space.rank n (A * B) \<le> min (vec_space.rank n A) (vec_space.rank m B)"
proof -
  have 1: "vec_space.rank n (A * B) \<le> (vec_space.rank n A)"
    using assms(1) assms(2) vec_space.rank_mat_mul_right
    by blast 
  have "vec_space.rank n (A* B) \<le> vec_space.rank m B" 
    by (meson assms(1) assms(2) rank_mat_mul_left) 
  thus ?thesis using 1 by simp
qed
context vec_space
begin 
lemma lin_indpt_set_card_lt_dim: 
  fixes A :: "'a vec set"
  assumes "A \<subseteq> carrier_vec n"
  assumes "lin_indpt A"
  shows "card A \<le> dim"
  using assms(1) assms(2) fin_dim li_le_dim(2) by blast

lemma lin_indpt_dim_col_lt_dim: 
  fixes A :: "'a mat"
  assumes "A \<in> carrier_mat n nc"
  assumes "distinct (cols A)"
  assumes "lin_indpt (set (cols A))"
  shows "nc \<le> dim"
proof -
  have b: "card (set (cols A)) = dim_col A" using cols_length assms(2)
    by (simp add: distinct_card) 
  have "set (cols A) \<subseteq> carrier_vec n" using assms(1) cols_dim by blast
  thus ?thesis using lin_indpt_set_card_lt_dim assms b by auto
qed

lemma lin_comb_imp_lin_dep_fin: 
  fixes A :: "'a vec set"
  assumes "finite A"
  assumes "A \<subseteq> carrier_vec n"
  assumes "lincomb c A = 0\<^sub>v n"
  assumes "\<exists> a. a \<in> A \<and> c a \<noteq> 0"
  shows "lin_dep A"
  apply (simp add: assms lin_dep_def)
  using assms(1) assms(3) assms(4) by auto

end

(* Vector *)

lemma smult_scalar_prod_sum: 
  fixes x :: "real" 
  assumes "vx \<in> carrier_vec n"
  assumes "vy \<in> carrier_vec n"
  shows "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = x * y * (vx \<bullet> vy)"
proof -
  have "\<And> i . i < n \<Longrightarrow> ((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i) = x * y * (vx $ i) * (vy $ i)" using assms by simp
  then have "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = (\<Sum> i \<in> {0..<n} .x * y * (vx $ i) * (vy $ i))" by simp
  also have "... = x * y * (\<Sum> i \<in> {0..<n} . (vx $ i) * (vy $ i))"
    using sum_distrib_left[of "x * y" "(\<lambda> i. (vx $ i) * (vy $ i))" "{0..<n}"]
    by (metis (no_types, lifting) mult.assoc sum.cong) 
  finally have "(\<Sum> i \<in> {0..<n} .((x \<cdot>\<^sub>v vx) $ i) * ((y \<cdot>\<^sub>v vy) $ i)) = x * y * (vx \<bullet> vy)" using scalar_prod_def assms
    by (metis carrier_vecD) 
  thus ?thesis by simp
qed

(* Basic Fisher's Inequality *)
context ordered_bibd
begin


(* lemma max_rank_inc_mat: rank (N) \<le> \<b>" *)

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
  shows "i = 0 \<Longrightarrow> j = 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (real \<r>)"
  and "i \<noteq> 0 \<Longrightarrow> j = 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (real \<Lambda>) - (real \<r>)" 
  and "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (real \<Lambda>)"
  and "i \<noteq> 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> i = j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (real \<r>) - (real \<Lambda>)"
  and "i \<noteq> 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> i \<noteq> j \<Longrightarrow> (add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = 0"
proof - 
  let ?M = "(N * N\<^sup>T)"
  assume a: "j = 0" "i=0"
  then have "(add_row_to_multiple (-1) [1..<dim_col (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (N* N\<^sup>T) $$ (i, j)" using assms by simp
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (real \<r>)"  using transpose_N_mult_diag v_non_zero assms
    by (simp add: a)
next
  let ?M = "(N * N\<^sup>T)"
  assume a: "j = 0" "i\<noteq>0"
  then have ail: "((-1) * ?M $$(0, j)) = -(real \<r>)" 
    by (simp add: a assms transpose_N_mult_diag v_non_zero) 
  then have ijne: "j \<noteq> i" using a by simp
  then have aij: "?M $$ (i, j) = (real \<Lambda>)" using  assms transpose_N_mult_off_diag a v_non_zero
    by (metis transpose_N_mult_dim(1)) 
  then have "add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M $$ (i, j) = (-1)*(real \<r>) + (real \<Lambda>)" using ail transform_N_step1 assms a by simp
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (real \<Lambda>) - (real \<r>)"
    by linarith 
next
  let ?M = "(N * N\<^sup>T)"
  assume a: "i = 0" "j \<noteq> 0"
  have ijne: "i \<noteq> j" using a by simp
  then have "(add_row_to_multiple (-1) [1..<dim_row (N * N\<^sup>T)] 0 (N * N\<^sup>T)) $$ (i, j) = (N* N\<^sup>T) $$ (i, j)" using a assms by simp
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (real \<Lambda>)" using transpose_N_mult_off_diag v_non_zero assms ijne
    by (metis a(1) transpose_N_mult_dim(2)) 
next 
  let ?M = "(N * N\<^sup>T)"
  assume a: "i \<noteq> 0" "j \<noteq> 0" "i = j"
  have ail: "((-1) * ?M $$(0, j)) = -(real \<Lambda>)" 
    using assms transpose_N_mult_off_diag a v_non_zero transpose_N_mult_dim(1) by auto  
  then have aij: "?M $$ (i, j) = (real \<r>)" using  assms transpose_N_mult_diag a v_non_zero
    by (metis transpose_N_mult_dim(1)) 
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = (real \<r>) - (real \<Lambda>)"
    using ail aij transform_N_step1 assms a
    by (metis uminus_add_conv_diff) 
next 
  let ?M = "(N * N\<^sup>T)"
  assume a: "i \<noteq> 0" "j \<noteq> 0" "i \<noteq> j"
  have ail: "((-1) * ?M $$(0, j)) = -(real \<Lambda>)" 
    using assms transpose_N_mult_off_diag a v_non_zero transpose_N_mult_dim(1) by auto  
  then have aij: "?M $$ (i, j) = (real \<Lambda>)" using  assms transpose_N_mult_off_diag a v_non_zero
    by (metis transpose_N_mult_dim(1) transpose_N_mult_dim(2)) 
  then show "(add_row_to_multiple (-1) [1..<dim_row ?M] 0 ?M) $$ (i, j) = 0" using aij ail transform_N_step1 assms a
    by (metis add.commute add.right_inverse)
qed

(* Add multiple rows *)

(* lemma add_multiple_rows_index_unchanged [simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> i \<Longrightarrow> add_multiple_rows a k ls A $$ (i,j) = A $$(i,j)"
  by (induct ls) (simp_all)

lemma add_multiple_rows_index_eq: 
  assumes "i < dim_row A" and "j < dim_col A" and "i \<notin> set ls" and "\<And> l . l \<in> set ls \<Longrightarrow> l < dim_row A"
  shows "add_multiple_rows a i ls A $$ (i,j) = (\<Sum>l\<leftarrow>ls. a * A $$(l,j)) + A$$(i,j)"
  using assms*)



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
  shows "i = 0 \<Longrightarrow> j = 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (real \<r>) + (real \<Lambda>) * (\<v> - 1)"
  and "i = 0 \<Longrightarrow> j \<noteq> 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = (real \<Lambda>)" 
  and "i \<noteq> 0 \<Longrightarrow> i = j \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (real \<r>) - (real \<Lambda>)"
  and "i \<noteq> 0 \<Longrightarrow> i \<noteq> j \<Longrightarrow>  add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = 0"
proof -
  assume a: "i = 0" "j =0"
  have dim_eq: "dim_col M = dim_col (N * N\<^sup>T) " using assms by simp
  then have "dim_col M = \<v>"
    by (simp add: points_list_length)
  then have size: "card {1..<dim_col M} = \<v> - 1" by simp 
  have val: "\<And> l . l \<in> {1..<dim_col M} \<Longrightarrow> M $$ (i, l) = (real \<Lambda>)" using assms(3) transform_N_step1_vals(3)
    by (metis dim_eq a(1) assms(1) atLeastLessThan_iff not_one_le_zero)  
  have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l\<in>{1..<dim_col M}.  M $$(i,l)) + M$$(i,0)" using a assms transform_N_step2 by simp
  also have "... = (\<Sum>l\<in>{1..<dim_col M}.  (real \<Lambda>)) + M$$(i,0)" using val by simp
  also have "... = (\<v> - 1) * (real \<Lambda>) + M$$(i,0)" using size
    by (metis sum_constant) 
  also have "... = (\<v> - 1) * (real \<Lambda>) + (real \<r>)" using transform_N_step1_vals(1)
    using a(1) a(2) assms(1) assms(2) assms(3) by presburger 
  finally show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (real \<r>) + (real \<Lambda>) * (\<v> - 1)" by simp
next 
  assume a: "i = 0" "j \<noteq> 0"
  then have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = M $$ (i, j)" using transform_N_step2 assms a by simp
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j)  = (real \<Lambda>)" using assms a transform_N_step1_vals(3) by simp
next 
  assume a: "i \<noteq> 0" "i = j"
  then have jne: "j \<noteq> 0" by simp
  then have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = M $$ (i, j)" using transform_N_step2 assms a by simp
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (real \<r>) - (real \<Lambda>)" using assms a jne transform_N_step1_vals(4) by simp
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
    have val2: "M $$ (i, i) = (real \<r>) - (real \<Lambda>)" using assms(3) transform_N_step1_vals(4) a True
      by (metis assms(1) transpose_N_mult_dim(1) transpose_N_mult_dim(2)) 
    have val3: "M$$ (i, 0) = (real \<Lambda>) - (real \<r>)" using assms(3) transform_N_step1_vals(2) a True assms(1) assms(2) by blast 
    have "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, j) = (\<Sum>l\<in>{1..<dim_col M}.  M $$(i,l)) + M$$(i,0)" 
      using assms transform_N_step2 True by blast
    also have "... = M $$ (i, i)  + (\<Sum>l\<in>{1..<dim_col M} - {i}.  M $$(i,l)) + M$$(i,0)"
      by (metis iin finite_atLeastLessThan sum.remove)
    also have "... = (real \<r>) - (real \<Lambda>) + (real \<Lambda>) - (real \<r>)" using val val2 val3 by simp
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
  shows "i = 0 \<Longrightarrow> add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i) = (real \<r>) + (real \<Lambda>) * (\<v> - 1)"
  and "i \<noteq> 0 \<Longrightarrow>  add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i)  = (real \<r>) - (real \<Lambda>)" 
proof -
  assume a: "i = 0" 
  then have "i < dim_col (N * N\<^sup>T)"
    using transpose_N_mult_dim(2) v_non_zero by linarith 
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i) = (real \<r>) + (real \<Lambda>) * (\<v> - 1)"
    using transform_N_step2_vals(1) assms a by blast 
next
  assume a: "i \<noteq> 0"
  then have "i < dim_col (N * N\<^sup>T)"
    using transpose_N_mult_dim(2) v_non_zero assms(1) transpose_N_mult_dim(1) by linarith
  then show "add_multiple_cols 1 0 [1..<dim_col M] M $$ (i, i)  = (real \<r>) - (real \<Lambda>)" 
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
  have d00: "?D $$ (0, 0) = ((real \<r>) + (real \<Lambda>) * (\<v> - 1))" using transform_N_step2_diag_vals(1) 
    by (metis transpose_N_mult_dim(1) v_non_zero) 
  have ine0: "\<And> i. i \<in> {1..<dim_row ?D} \<Longrightarrow> i \<noteq> 0" by simp
  have "\<And> i. i \<in> {1..<dim_row ?D} \<Longrightarrow> i < dim_row (N * N\<^sup>T)" by simp       
  then have diagnon0: "\<And> i. i \<in> {1..<\<v>} \<Longrightarrow> ?D $$ (i, i) = (real \<r>) - (real \<Lambda>)"   
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
  then have "det (N * N\<^sup>T) = ((real \<r>) + (real \<Lambda>) * (\<v> - 1)) * (\<Prod> i = 1 ..< \<v>. ?D $$ (i,i))" 
    using d00 by simp
  then have "det (N * N\<^sup>T) = ((real \<r>) + (real \<Lambda>) * (\<v> - 1)) * (\<Prod> i = 1 ..< \<v>. ((real \<r>) - (real \<Lambda>)))" 
    using diagnon0 by simp
  then have "det (N * N\<^sup>T) = ((real \<r>) + (real \<Lambda>) * (\<v> - 1)) * ((real \<r>) - (real \<Lambda>))^(\<v> - 1)" by simp
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ((real \<r>) - (real \<Lambda>))^(\<v> - 1)"
    by simp
  then have "det (N * N\<^sup>T) = (\<r> + \<Lambda> * (\<v> - 1)) * ( \<r> - \<Lambda>)^(\<v> - 1)"
    using index_lt_replication
    by (metis (no_types, lifting) less_imp_le_nat of_nat_diff of_nat_mult of_nat_power)
  then show ?thesis by blast 
qed

theorem Fishers_Inequality_BIBD: "\<v> \<le> \<b>"
proof -
  let ?B = "N * N\<^sup>T"
  have b_is_square: "dim_col ?B = \<v>"
    using transpose_N_mult_dim(2) by blast 
  have b_dim_row: "dim_row ?B = \<v>"
    using dim_row_is_v by simp
  have dim_row_t: "dim_row N\<^sup>T = \<b>"
    by (simp add: dim_col_is_b) 
(* Calculate the determinant of B and show it is (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1) *)
  have "det ?B = (\<r> + \<Lambda> * (\<v> - 1))* (\<r> - \<Lambda>)^(\<v> - 1)"
    using determinant_inc_mat_square by simp
(* Have det(B) \<noteq> 0 as r > \<Lambda> *)
  have lhn0: "(\<r> + \<Lambda> * (\<v> - 1)) > 0"
    using r_gzero by blast 
  have "(\<r> - \<Lambda>) > 0"
    using index_lt_replication zero_less_diff by blast  
  then have det_not_0:  "det ?B \<noteq> 0" using lhn0
    by (metis determinant_inc_mat_square mult_eq_0_iff of_nat_eq_0_iff power_eq_0_iff zero_less_iff_neq_zero)
(* Conclude that B has rank \<v> - over what vector space? *)
  have "?B \<in> carrier_mat \<v> \<v>" using b_is_square by auto
  then have b_rank: "vec_space.rank \<v> ?B = \<v>"
    using vec_space.low_rank_det_zero det_not_0 by blast
(* As the rank of a product of matrices cannot exceed the rank of either factor, we have that thesis *)
  have "vec_space.rank \<v> ?B \<le> min (vec_space.rank \<v> N) (vec_space.rank \<b> N\<^sup>T)"
    using N_carrier_mat dim_row_t rank_mat_mult_lt_min_rank_factor by blast
  then have "\<v> \<le> min (vec_space.rank \<v> N) (vec_space.rank \<b> N\<^sup>T)" using b_rank by simp
  then have "\<v> \<le> vec_space.rank \<v> N"
    by simp
  thus ?thesis 
    by (meson le_trans vec_space.rank_le_nc N_carrier_mat transpose_carrier_mat) 
qed

end

(* Even town Problem *)
lemma intersect_num_same_eq_size[simp]: "bl |\<inter>| bl = card bl"
  by (simp add: intersection_number_def)

locale ordered_simple_design = ordered_design \<V>s \<B>s + simple_design "(set \<V>s)" "mset \<B>s" for \<V>s \<B>s
begin

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

lemma blocks_list_distinct: "distinct \<B>s"
  using block_mset_distinct by auto
  

lemma distinct_cols_N: "distinct (cols N)"
proof -
  have "inj_on (\<lambda> bl . inc_vec_of \<V>s bl) (set \<B>s)" using inc_vec_eq_iff_blocks 
    by (simp add: inc_vec_eq_iff_blocks inj_on_def) 
  then show ?thesis using distinct_map inc_mat_of_cols_inc_vecs blocks_list_distinct
    by (simp add: distinct_map inc_mat_of_cols_inc_vecs ) 
qed
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

end

sublocale odd_town \<subseteq> ordered_simple_design
  using odd_town_no_repeat_clubs by (unfold_locales) (meson distinct_mset_def) 


context odd_town 
begin



lemma upper_bound_clubs: "\<b> \<le> \<v>"
proof -
  interpret v: vec_space "TYPE(real)" \<v> . 
  have dimv: "v.dim = \<v>" using v.dim_is_n by simp
  have lidpt: "v.lin_indpt (set (cols N))" (* Easy set to relate to *)
    sorry
  have "distinct ((cols N))" using distinct_cols_N by simp

  thus ?thesis using v.lin_indpt_dim_col_lt_dim[of "N" "\<b>"] lidpt N_carrier_mat dimv by simp
qed


end

lemma vec_prod_zero: "(0\<^sub>v n) \<bullet> (0\<^sub>v n) = 0"
  by simp



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


lemma dim_vec_N_col: 
  assumes "j < \<b>"
  shows "dim_vec (cols N ! j) = \<v>"
proof -
  have "cols N ! j = col N j" using assms by simp
  then have "dim_vec (cols N ! j) = dim_vec (col N j)" by simp
  thus ?thesis using dim_col assms
    by (simp add: points_list_length) 
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

lemma points_inter_num_rep: 
  assumes "b1 \<in># \<B>" and "b2 \<in># \<B> - {#b1#}"
  shows "card {v \<in> \<V> . v \<in> b1 \<and> v \<in> b2} = \<m>"
proof -
  have "\<And> x. x \<in> b1 \<inter> b2 \<Longrightarrow> x \<in> \<V>" using wellformed assms by auto
  then have "{v \<in> \<V> . v \<in> (b1 \<inter> b2)} = (b1 \<inter> b2)"
    by blast 
  then have "card {v \<in> \<V> . v \<in> b1 \<and> v \<in> b2} = card (b1 \<inter> b2)"
    by simp 
  thus ?thesis using assms const_intersect intersection_number_def
    by metis 
qed

lemma inter_num_points_filter_def: 
  assumes "j1 < \<b>" "j2 < \<b>" "j1 \<noteq> j2"
  shows "card {x \<in> {0..<\<v>} . ((\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2)) } = \<m>"
proof - 
  have inter: "\<And> v. v \<in> \<V> \<Longrightarrow> v \<in> (\<B>s ! j1) \<and> v \<in> (\<B>s ! j2) \<longleftrightarrow> v \<in> (\<B>s ! j1) \<inter> (\<B>s ! j2)"
    by simp 
  obtain bl1 bl2 where bl1in: "bl1 \<in># \<B>" and bl1eq: "\<B>s ! j1 = bl1" and bl2in: "bl2 \<in># \<B> - {#bl1#}" and bl2eq: "\<B>s ! j2 = bl2" 
    using assms obtains_two_diff_index by metis
  have "card {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j1) \<and> (\<V>s ! x) \<in> (\<B>s ! j2) } = card {v \<in> \<V> . v \<in> (\<B>s ! j1) \<and> v \<in> (\<B>s ! j2) }" 
    using card_filter_point_indices by simp
  also have "... = card {v \<in> \<V> . v \<in> bl1 \<and> v \<in> bl2 }" using bl1eq bl2eq by simp
  finally show ?thesis using points_inter_num_rep bl1in bl2in
    by blast
qed

lemma scalar_prod_incidence_vector_sq: 
  assumes "j < \<b>"
  shows "(cols N ! j) \<bullet> (cols N ! j) = card (\<B>s ! j)"
proof -
  have split: "{0..<\<v>} = {x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} \<union>{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)}" by auto
  have inter: "{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} \<inter> {x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)} = {}" by auto
  have one: "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<in> (\<B>s ! j)} \<Longrightarrow> (col N j) $ i = 1"
    using N_col_def_indiv  assms atLeastLessThan_iff by blast  
  have zero: "\<And> i. i \<in>{x \<in> {0..<\<v>} . (\<V>s ! x) \<notin> (\<B>s ! j)} \<Longrightarrow> (col N j) $ i = 0"
     using N_col_def_indiv  assms atLeastLessThan_iff by blast 
  have "(cols N ! j) \<bullet> (cols N ! j) = (\<Sum> i \<in> {0..<\<v>} . (cols N ! j) $ i * (cols N ! j) $ i)" using assms dim_vec_N_col scalar_prod_def
    by (metis (full_types)) 
  also have "... = (\<Sum> i \<in> {0..<\<v>} . ((cols N ! j) $ i)^2)"
    by (simp add: power2_eq_square) 
  also have "... = (\<Sum> i \<in> {0..<\<v>} . ((col N j) $ i)^2)" using assms by simp
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
    have fin: "finite (set (cols N))"
      by simp
    have cv: "set (cols N) \<subseteq> carrier_vec \<v>"
      by (metis cols_dim dim_row_is_v) 
    have lidpt: "vs.lin_indpt (set (cols N))"
    proof (rule ccontr)
      assume "\<not> vs.lin_indpt (set (cols N))"
      then have "vs.lin_dep (set (cols N))" by simp
      from vs.finite_lin_dep[OF fin this cv]
      obtain a v where comb: "vs.lincomb a (set (cols N)) = 0\<^sub>v \<v>" and vin: "v \<in> (set (cols N))" and avne: "a v \<noteq> 0" by auto 
      define c where ceq: "c = (\<lambda> i. a ((cols N) ! i))"
      then have listcomb: "vs.lincomb_list c (cols N) = 0\<^sub>v \<v>" using vs.lincomb_as_lincomb_list_distinct[OF cv distinct_cols_N] comb by simp
      obtain i' where vi: "(cols N) ! i' = v" and ilt: "i' < length (cols N)" using vin
        by (metis in_set_conv_nth) 
      then have iin: "i' \<in> {0..<\<b>}"by simp 
      have cine0: "c i' \<noteq> 0" using ceq avne vi by simp
      have nth: "\<And> j. j < \<b> \<Longrightarrow> map (\<lambda>i. c i \<cdot>\<^sub>v (cols N) ! i) [0..<\<b>] ! j = c j \<cdot>\<^sub>v (cols N) ! j"
        by simp
      have inner_sum: "\<And> i f . i \<in> {0..<\<b>} \<Longrightarrow> (\<Sum> j \<in> {0..<\<b>} . f j) = f i + (\<Sum>j \<in> ({0..<\<b>} - {i}). f j)"
        using sum.remove
        by (metis blocks_list_length dual_sys.finite_sets) 
      have "(\<Sum> i \<in> {0..<\<b>} . c i)^2 = (\<Sum> i \<in> {0..<\<b>} . c i * c i) + (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j))" 
        using double_sum_split_case_square by fastforce
      then have alt_rep: "(\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j)) = (\<Sum> i \<in> {0..<\<b>} . c i)^2 - (\<Sum> i \<in> {0..<\<b>} . c i * c i)" 
        by linarith 
      have dim: "\<And> j. j < \<b> \<Longrightarrow>  dim_vec (c j \<cdot>\<^sub>v (cols N) ! j) = \<v>" using cv
        using carrier_dim_vec nth_mem by (simp add: points_list_length) 
      then have "\<And> j. j < \<b> \<Longrightarrow> ((cols N) ! j) \<in> carrier_vec \<v>"
        by (simp add: carrier_dim_vec) 
      then have sum_simp: "\<And> i j . i \<in>{0..<\<b>} \<Longrightarrow> j \<in> {0..<\<b>} \<Longrightarrow> 
        (\<Sum>l \<in> {0..<\<v>} . ((c i \<cdot>\<^sub>v (cols N) ! i) $ l) *  ((c j \<cdot>\<^sub>v (cols N) ! j) $ l)) = c i * c j * (((cols N) ! i) \<bullet> ((cols N) ! j)) "
        using smult_scalar_prod_sum
        by (meson atLeastLessThan_iff) 
      then have "0 = (vs.lincomb_list c (cols N)) \<bullet> (vs.lincomb_list c (cols N))" using vec_prod_zero listcomb by simp
      also have "... = (vs.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (cols N) ! i) [0..<\<b>])) \<bullet> (vs.sumlist (map (\<lambda>j. c j \<cdot>\<^sub>v (cols N) ! j) [0..<\<b>]))"
        using vs.lincomb_list_def by simp
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (vs.sumlist (map (\<lambda>i. c i \<cdot>\<^sub>v (cols N) ! i) [0..<\<b>])) $ l * (vs.sumlist (map (\<lambda>j. c j \<cdot>\<^sub>v (cols N) ! j) [0..<\<b>])) $ l)"
        using scalar_prod_def dim listcomb vs.lincomb_list_def by auto 
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (sum (\<lambda> i. (c i \<cdot>\<^sub>v (cols N) ! i) $ l) {0..<\<b>}) * (sum (\<lambda> j. (c j \<cdot>\<^sub>v (cols N) ! j) $ l) {0..<\<b>}))"
        using vs.sumlist_nth nth dim by simp
      also have "... = (\<Sum> l \<in> {0..<\<v>} . (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> {0..< \<b>}. ((c i \<cdot>\<^sub>v (cols N) ! i) $ l) *  ((c j \<cdot>\<^sub>v (cols N) ! j) $ l))))" 
        by (metis (no_types) sum_product)
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> {0..< \<b>} . (\<Sum>l \<in> {0..<\<v>} . ((c i \<cdot>\<^sub>v (cols N) ! i) $ l) *  ((c j \<cdot>\<^sub>v (cols N) ! j) $ l))))" 
        using sum_reorder_triple by simp
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> {0..< \<b>} . c i * c j * (((cols N) ! i) \<bullet> ((cols N) ! j))))" 
        using sum_simp by simp
      also have "... = (\<Sum> i \<in> {0..<\<b>} . c i * c i * (((cols N) ! i) \<bullet> ((cols N) ! i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * (((cols N) ! i) \<bullet> ((cols N) ! j))))" using double_sum_split_case by fastforce
      also have "... = (\<Sum> i \<in> {0..<\<b>} . c i * c i * (card (\<B>s ! i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * (((cols N) ! i) \<bullet> ((cols N) ! j))))" using scalar_prod_incidence_vector_sq by auto
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * (((cols N) ! i) \<bullet> ((cols N) ! j))))"
        by (metis power2_eq_square) 
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + (\<Sum> i \<in> {0..<\<b>} . 
        (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j * \<m>))"  using scalar_prod_incidence_vector_diff by auto
      also have "... = (\<Sum> i \<in> {0..<\<b>} . (c i)^2 * (card (\<B>s ! i))) + 
         \<m> * (\<Sum> i \<in> {0..<\<b>} . (\<Sum> j \<in> ({0..< \<b>} - {i}) . c i * c j))" 
        using double_sum_mult_hom[of "real \<m>" "\<lambda> i j . c i * c j" "\<lambda> i.{0..<\<b>} - {i}" "{0..<\<b>}"]
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
    have "distinct ((cols N))"
      by (simp add: distinct_cols_N) 
    thus ?thesis using vs.lin_indpt_dim_col_lt_dim[of "N" "\<b>"] lidpt N_carrier_mat dimv by simp
  qed
qed

end

context ordered_pairwise_balance
begin



corollary general_nonuniform_fishers: 
  assumes "\<Lambda> > 0" 
  shows "\<v> \<le> \<b>"
proof -
  have "mset \<B>s* = dual_blocks \<V> \<B>s" using dual_blocks_ordered_eq by simp
  then interpret des: const_intersect_design "set [0..<(length \<B>s)]" "mset \<B>s*" \<Lambda> 
    using assms dual_is_const_intersect_des by simp
  interpret odes: ordered_const_intersect_design "[0..<length \<B>s]" "\<B>s*" \<Lambda> 
    using distinct_upt des.wellformed by (unfold_locales) (blast)
  have "length \<B>s* \<le> length [0..<length \<B>s]" using odes.general_fishers_inequality
    using odes.blocks_list_length odes.points_list_length by presburger
  then have "length \<B>s* \<le> \<b>"
    by simp 
  then show ?thesis by (simp add: dual_blocks_len points_list_length)
qed

end

end