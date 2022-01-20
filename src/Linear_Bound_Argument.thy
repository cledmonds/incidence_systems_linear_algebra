theory Linear_Bound_Argument imports Dual_Systems Jordan_Normal_Form.Determinant 
Jordan_Normal_Form.DL_Rank Jordan_Normal_Form.Ring_Hom_Matrix BenOr_Kozen_Reif.More_Matrix
Berlekamp_Zassenhaus.Finite_Field
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

lemma double_sum_mult_hom: "(\<Sum> i \<in> A . (\<Sum> j \<in> g i . (k ::int) * (f i j))) = k* (\<Sum> i \<in> A . (\<Sum> j \<in> g i . f i j))"
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
  fixes x :: "int" 
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

lemma obtain_set_list_item: 
  assumes "x \<in> set xs"
  obtains i where "i < length xs" and "xs ! i = x"
  by (meson assms in_set_conv_nth)

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
      have "0 = (vs.lincomb_list c (cols N)) \<bullet> (vs.lincomb_list c (cols N))" using vec_prod_zero listcomb by simp
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
(* Can be moved into design ops *)

context incidence_system
begin

lemma del_block_b: 
  "bl \<in># \<B> \<Longrightarrow> size (del_block bl) = \<b> - 1"
  "bl \<notin># \<B> \<Longrightarrow> size (del_block bl) = \<b>"
  by (simp_all add: del_block_def size_Diff_singleton)

lemma del_block_points_index: 
  assumes "ps \<subseteq> \<V>"
  assumes "card ps = 2"
  assumes "bl \<in># \<B>"
  shows "ps \<subseteq> bl \<Longrightarrow> points_index (del_block bl) ps = points_index \<B> ps - 1"
        "\<not> (ps \<subseteq> bl) \<Longrightarrow> points_index (del_block bl) ps = points_index \<B> ps"
proof -
  assume "ps \<subseteq> bl"
  then show "points_index (del_block bl) ps = points_index \<B> ps - 1"
    using point_index_diff del_block_def
    by (metis assms(3) insert_DiffM2 points_index_singleton) 
next
  assume "\<not> ps \<subseteq> bl"
  then show "del_block bl index ps = \<B> index ps"
    using point_index_diff del_block_def
    by (metis add_block_def add_block_index_not_in assms(3) insert_DiffM2) 
qed

end

context finite_incidence_system
begin

lemma complete_block_size_eq_points: "bl \<in># \<B> \<Longrightarrow> card bl = \<v> \<Longrightarrow> bl = \<V>"
  using wellformed by (simp add:  card_subset_eq finite_sets) 

lemma complete_block_all_subsets: "bl \<in># \<B> \<Longrightarrow> card bl = \<v> \<Longrightarrow> ps \<subseteq> \<V> \<Longrightarrow> ps \<subseteq> bl"
  using complete_block_size_eq_points by auto

lemma del_block_complete_points_index: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> card bl = \<v> \<Longrightarrow> 
  points_index (del_block bl) ps = points_index \<B> ps - 1"
  using complete_block_size_eq_points del_block_points_index(1) by blast

end

context proper_design
begin

lemma del_block_proper: 
  assumes "\<b> > 1"
  shows "proper_design \<V> (del_block bl)"
proof -
  interpret d: design \<V> "(del_block bl)"
    using delete_block_design by simp
  have "d.\<b> > 0" using del_block_b assms
    by (metis b_positive zero_less_diff) 
  then show ?thesis by(unfold_locales) (auto)
qed

end

context pairwise_balance
begin

lemma remove_complete_block_pbd: 
  assumes "\<b> \<ge> 2"
  assumes "bl \<in># \<B>"
  assumes "card bl = \<v>"
  shows "pairwise_balance \<V> (del_block bl) (\<Lambda> - 1)"
proof -
  interpret pd: proper_design \<V> "(del_block bl)" using assms(1) del_block_proper by simp
  show ?thesis using t_lt_order assms del_block_complete_points_index 
    by (unfold_locales) (simp_all)
qed

lemma remove_complete_block_pbd_alt: 
  assumes "\<b> \<ge> 2"
  assumes "bl \<in># \<B>"
  assumes "bl = \<V>"
  shows "pairwise_balance \<V> (del_block bl) (\<Lambda> - 1)"
  using remove_complete_block_pbd assms by blast 

lemma b_gt_index:"\<b> \<ge> \<Lambda>"
proof (rule ccontr)
  assume blt: "\<not> \<b> \<ge> \<Lambda>"
  obtain ps where "card ps = 2" and "ps \<subseteq> \<V>" using t_lt_order
    by (meson obtain_t_subset_points) 
  then have "size {#bl \<in># \<B>. ps \<subseteq> bl#} = \<Lambda>" using balanced by (simp add: points_index_def)
  thus False using blt by auto 
qed

lemma remove_complete_blocks_set_pbd:
  assumes "x < \<Lambda>"
  assumes "size A = x"
  assumes "A \<subset># \<B>"
  assumes "\<And> a. a \<in># A \<Longrightarrow> a = \<V>"
  shows "pairwise_balance \<V> (\<B> - A) (\<Lambda> - x)"
using assms proof (induct "x" arbitrary: A)
  case 0
  then have beq: "\<B> - A = \<B>" by simp
  have "pairwise_balance \<V> \<B> \<Lambda>" by (unfold_locales)
  then show ?case using beq by simp
next
  case (Suc x)
  then have "size A > 0" by simp
  let ?A' = "A - {#\<V>#}"
  have ss: "?A' \<subset># \<B>"
    using Suc.prems(3) by (metis diff_subset_eq_self subset_mset.le_less_trans)
  have sx: "size ?A' = x"
    by (metis Suc.prems(2) Suc.prems(4) Suc_inject size_Suc_Diff1 size_eq_Suc_imp_elem)
  have xlt: "x < \<Lambda>"
    by (simp add: Suc.prems(1) Suc_lessD) 
  have av: "\<And> a. a \<in># ?A' \<Longrightarrow> a = \<V>" using Suc.prems(4)
    by (meson in_remove1_mset_neq)
  then interpret pbd: pairwise_balance \<V> "(\<B> - ?A')" "(\<Lambda> - x)" using Suc.hyps sx ss xlt by simp
  have "Suc x < \<b>" using Suc.prems(3)
    by (metis Suc.prems(2) mset_subset_size) 
  then have "\<b> - x \<ge> 2"
    by linarith 
  then have bgt: "size (\<B> - ?A') \<ge> 2" using ss size_Diff_submset
    by (metis subset_msetE sx)
  have ar: "add_mset \<V> (remove1_mset \<V> A) = A" using Suc.prems(2) Suc.prems(4)
    by (metis insert_DiffM size_eq_Suc_imp_elem) 
  then have db: "pbd.del_block \<V> = \<B> - A" by(simp add: pbd.del_block_def)
  then have "\<B> - ?A' = \<B> - A + {#\<V>#}" using Suc.prems(2) Suc.prems(4)
    by (metis (no_types, lifting) Suc.prems(3) ar add_diff_cancel_left' add_mset_add_single add_right_cancel 
        pbd.del_block_def remove_1_mset_id_iff_notin ss subset_mset.lessE trivial_add_mset_remove_iff) 
  then have "\<V> \<in># (\<B> - ?A')" by simp 
  then have "pairwise_balance \<V> (\<B> - A) (\<Lambda> - (Suc x))" using db bgt diff_Suc_eq_diff_pred 
      diff_commute pbd.remove_complete_block_pbd_alt by presburger
  then show ?case by simp
qed

lemma remove_all_complete_blocks_pbd:
  assumes "count \<B> \<V> < \<Lambda>"
  shows "pairwise_balance \<V> (removeAll_mset \<V> \<B>) (\<Lambda> - (count \<B> \<V>))" (is "pairwise_balance \<V> ?B ?\<Lambda>")
proof -
  let ?A = "replicate_mset (count \<B> \<V>) \<V>"
  let ?x = "size ?A"
  have blt: "count \<B> \<V> \<noteq> \<b>" using b_gt_index assms
    by linarith 
  have xeq: "?x = count \<B> \<V>" by simp
  have av: "\<And> a. a \<in># ?A \<Longrightarrow> a = \<V>"
    by (metis in_replicate_mset)
  have "?A \<subseteq># \<B>"
    by (meson count_le_replicate_mset_subset_eq le_eq_less_or_eq)
  then have "?A \<subset># \<B>" using blt
    by (metis subset_mset.nless_le xeq) 
  thus ?thesis using assms av xeq remove_complete_blocks_set_pbd
    by presburger 
qed

(*
lemma "count \<B> \<V> = \<Lambda> \<longleftrightarrow> (\<forall>bl \<in># \<B> . card bl = \<v> \<or> card bl = 1)" 
proof (intro iffI)
  assume "local.multiplicity \<V> = \<Lambda>"
  show "\<forall>bl\<in>#\<B>. card bl = \<v> \<or> card bl = 1"
  proof (auto)
    fix bl assume "bl \<in># \<B>" and "card bl \<noteq> Suc 0"
    show "card bl = \<v>"
      sorry
  qed
next
  assume "\<forall>bl\<in>#\<B>. card bl = \<v> \<or> card bl = 1"
  show "local.multiplicity \<V> = \<Lambda>"
    sorry
qed

*)
end


lemma removeAll_size_lt: "size (removeAll_mset C M) \<le> size M"
  by (simp add: size_mset_mono)

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

definition non_empty_col :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> bool" where
"non_empty_col M j \<equiv> \<exists> k. k \<noteq> 0 \<and> k \<in>$ col M j"

definition proper_inc_mat :: "('a :: {ring, one, zero}) mat \<Rightarrow> bool" where
"proper_inc_mat M \<equiv> (dim_row M > 0 \<and> dim_col M > 0)"

definition mat_rep_num :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_rep_num M i \<equiv> count_vec (row M i) 1"

definition mat_point_index :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat set \<Rightarrow> nat" where
"mat_point_index M I \<equiv> card {j . j < dim_col M \<and> (\<forall> i \<in> I. M $$ (i, j) = 1)}"

definition mat_inter_num :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_inter_num M j1 j2 \<equiv> card {i . i < dim_row M \<and> M $$ (i, j1) = M $$ (i, j2) \<and> M $$ (i, j1) \<noteq> 0}"

definition mat_block_size :: "('a :: {ring, one, zero}) mat \<Rightarrow> nat \<Rightarrow> nat" where
"mat_block_size M j \<equiv> dim_row M - count_vec (col M j) 0"

lemma vCons_set_contains_in: "a \<in> set\<^sub>v v \<Longrightarrow> set\<^sub>v (vCons a v) = set\<^sub>v v"
  by (metis remdups_mset_singleton_sum set_mset_remdups_mset vec_mset_set vec_mset_vCons)

lemma vCons_set_contains_add: "a \<notin> set\<^sub>v v \<Longrightarrow> set\<^sub>v (vCons a v) = set\<^sub>v v \<union> {a}"
  using vec_mset_set vec_mset_vCons
  by (metis insert_union set_mset_add_mset_insert) 

lemma setv_vec_mset_not_in_iff: "a \<notin> set\<^sub>v v \<longleftrightarrow> a \<notin># vec_mset v"
  by (simp add: vec_mset_set)

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
      by (metis Diff_not_in) 
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

lemma count_vec_sum_0_pair: 
  assumes "set\<^sub>v (col M j) \<subseteq> {0, x}"
  assumes "x \<noteq> 0"
  shows "mat_block_size M j = count_vec (col M j) x"
proof -
  have "dim_vec (col M j) = (\<Sum> i \<in> set\<^sub>v (col M j). count_vec (col M j) i) " using sum_count_vec
    by (simp add: mset_vec_same_size size_multiset_overloaded_eq vec_mset_set) 
  also have "... = (\<Sum> i \<in> {0, x}. count_vec (col M j) i)" using assms  sum_setv_subset_eq
    by (metis finite.emptyI finite.insertI)
  finally have "dim_vec (col M j) = count_vec (col M j) 0 + count_vec (col M j) x"
    by (simp add: assms(2)) 
  thus ?thesis by (simp add: mat_block_size_def)
qed

lemma row_map_mat[simp]:
  assumes "i < dim_row A" shows "row (map_mat f A) i = map_vec f (row A i)"
  unfolding map_mat_def map_vec_def using assms by auto

context zero_one_matrix 
begin



lemma mat_block_size_01: 
  assumes "j < dim_col M"
  shows "mat_block_size M j = count_vec (col M j) 1"
  using count_vec_sum_0_pair
  by (metis assms col_elems_ss01 less_numeral_extra(1) less_numeral_extra(3))

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

lemma mat_inter_num_01: 
  assumes "j1 < dim_col M" "j2 < dim_col M"
  shows "mat_inter_num M j1 j2 = card {i . i < dim_row M \<and> M $$ (i, j1) = 1 \<and> M $$ (i, j2) = 1}"
proof -
  have "mat_inter_num M j1 j2 = card {i . i < dim_row M \<and> M $$ (i, j1) = M $$ (i, j2) \<and> M $$ (i, j1) \<noteq> 0}" 
    by (simp add: mat_inter_num_def)
  also have "... = card {i . i < dim_row M \<and> M $$ (i, j1) = M $$ (i, j2) \<and> M $$ (i, j1) = 1}" using assms
    by (metis (mono_tags, opaque_lifting) zero_neq_one zero_one_matrix.elems_are_one_zero zero_one_matrix_axioms)
  finally show ?thesis
    by (smt (verit) Collect_cong) 
qed


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

end

abbreviation to_int_mat :: "'a :: finite mod_ring mat \<Rightarrow> int mat" where
  "to_int_mat \<equiv> map_mat to_int_mod_ring"

lemma map_mat_compose: "map_mat f (map_mat g A) = map_mat (f \<circ> g) A"
  by (auto)

lemma map_vec_compose: "map_vec f (map_vec g v) = map_vec (f \<circ> g) v"
  by auto

locale mat_mod = fixes m :: int
assumes non_triv_m: "m > 1"
begin 

definition vec_mod :: "int vec \<Rightarrow> int vec" where
"vec_mod v \<equiv> map_vec (\<lambda> x . x mod m) v"

lemma vec_mod_dim[simp]: "dim_vec (vec_mod v) = dim_vec v"
  using vec_mod_def by simp

lemma vec_mod_index[simp]: "i < dim_vec v \<Longrightarrow> (vec_mod v) $ i = (v $ i) mod m"
  using vec_mod_def by simp

lemma vec_mod_index_same[simp]: "i < dim_vec v \<Longrightarrow> v $ i < m \<Longrightarrow> v $ i \<ge> 0 \<Longrightarrow> (vec_mod v) $ i = v $ i"
  by simp

lemma vec_setI2:
  assumes "i < dim_vec v "
  shows "v $ i \<in> set\<^sub>v v"
  using assms
  by (simp add: vec_setI) 

lemma vec_mod_vec_same: 
  assumes "set\<^sub>v v \<subseteq> {0..<m}"
  shows "vec_mod v = v"
  apply (intro eq_vecI, simp_all)
  using assms vec_setI2 vec_mod_index_same
  by (metis atLeastLessThan_iff subset_iff zmod_trivial_iff) 

lemma vec_mod_set_vec_same:
  assumes "set\<^sub>v v \<subseteq> {0..<m}"
  shows "set\<^sub>v (vec_mod v) = set\<^sub>v v"
  using vec_mod_vec_same assms by auto

definition mat_mod :: "int mat \<Rightarrow> int mat"  where 
"mat_mod M \<equiv> map_mat (\<lambda> x. x mod m) M"

lemma mat_mod_dim[simp]: "dim_row (mat_mod M) = dim_row M" "dim_col (mat_mod M) = dim_col M"
  using mat_mod_def by simp_all

lemma mat_mod_index[simp]: 
  assumes "i < dim_row M" "j < dim_col M"
  assumes "M $$ (i, j) < m"
  assumes "M $$ (i, j) \<ge> 0"
  shows "mat_mod M $$ (i, j) = M $$ (i, j)"
  by (simp add: assms mat_mod_def)

lemma elements_matI2:
  assumes "i < dim_row A" "j < dim_col A"
  shows "A $$ (i, j) \<in> elements_mat A"
  using assms by auto

lemma mat_mod_eq_cond:
  assumes "elements_mat M \<subseteq> {0..<m}"
  shows "mat_mod M = M"
proof (intro eq_matI, simp_all)
  fix i j assume "i < dim_row M" "j < dim_col M"
  then have "M $$ (i, j) \<in> {0..<m}"
    using assms elements_matI2 by blast 
  then show "local.mat_mod M $$ (i, j) = M $$ (i, j)"
    using mat_mod_index
    by (simp add: \<open>i < dim_row M\<close> \<open>j < dim_col M\<close>) 
qed

lemma mat_mod_eq_elements_cond:
  assumes "elements_mat M \<subseteq> {0..<m}"
  shows "elements_mat (mat_mod M) = elements_mat M"
  using mat_mod_eq_cond assms by auto

end


locale inc_mat_mod = zero_one_matrix + mat_mod
  
begin

abbreviation inc_mat_mod :: "int mat" ("M\<^sub>m") where 
"M\<^sub>m \<equiv> mat_mod M"

lemma floor_M_01: "i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> \<lfloor>M $$ (i, j)\<rfloor> = 0 \<or> \<lfloor>M $$ (i, j)\<rfloor> = 1"
by (metis elems_are_one_zero floor_one floor_zero)

lemma inc_mat_mod_index: assumes "i < dim_row M" "j < dim_col M"
  shows "M\<^sub>m $$ (i, j) = M $$ (i, j)"
  using mat_mod_index assms(1) assms(2) elems_are_one_zero non_triv_m by fastforce 

lemma mat_mod_elems: "elements_mat M\<^sub>m \<subseteq> {0, 1}"
  using inc_mat_mod_index
  by (metis (no_types, lifting) elements_matD floor_M_01 floor_of_int insert_iff inc_mat_mod_dim(1) inc_mat_mod_dim(2) subsetI)

lemma mat_mod_non_empty_col_iff: 
  assumes "i < dim_row M\<^sub>m" "j < dim_col M\<^sub>m"
  shows "non_empty_col M\<^sub>m j \<longleftrightarrow> non_empty_col M j"
proof (intro iffI)
  assume "non_empty_col M\<^sub>m j"
  then obtain k where kn0: "k \<noteq> 0" and kin: "k \<in>$ col M\<^sub>m j" using non_empty_col_def by auto
  then have "k \<in> elements_mat M\<^sub>m" using vec_contains_col_elements_mat assms
    by metis 
  then have "k = 1" using kn0
    using mat_mod_elems by blast 
  then have "1 \<in>$ col M\<^sub>m j" using kin by simp
  then have "1 \<in>$ col M j" using inc_mat_mod_index
    by (metis assms(2) dim_col index_col inc_mat_mod_dim of_int_hom.hom_one vec_setE vec_setI) 
  thus "non_empty_col M j" using non_empty_col_01 assms
    by (simp) 
next
  assume "non_empty_col M j"
  then have "1 \<in>$ col M j" using non_empty_col_01 assms mat_mod_dim by simp
  then have "1 \<in>$ col M\<^sub>m j" using inc_mat_mod_index
    by (metis assms(2) dim_col index_col inc_mat_mod_dim of_int_eq_1_iff vec_setE vec_setI)  
  then show "non_empty_col M\<^sub>m j" using assms non_empty_col_def
    by (metis zero_neq_one) 
qed

lemma mat_mod_proper_iff:  "proper_inc_mat M\<^sub>m  \<longleftrightarrow> proper_inc_mat M"
  by (simp add: proper_inc_mat_def)

lemma mat_mod_count_row_eq: 
  assumes "i < dim_row M"
  shows "count_vec (row M\<^sub>m i) x = count_vec (row M i) x"
proof - 
  have inj: "inj real_of_int"
    by (simp add: of_int_hom.inj_f) 
  have eq: "\<And> j. j \<in>{..<dim_col  M\<^sub>m} \<Longrightarrow> (row M\<^sub>m i) $ j = M\<^sub>m $$(i, j)" using assms
    by (simp)
  have eq2: "\<And> j. j \<in>{..<dim_col  M} \<Longrightarrow> (row M i) $ j = M $$(i, j)" using assms
    by (simp)
  have eq3: "\<And> j. j \<in># mset_set {..<dim_col M} \<Longrightarrow> M\<^sub>m $$ (i, j) = M $$ (i, j)" using assms inc_mat_mod_index by simp
  then have "image_mset (\<lambda> j. M\<^sub>m $$(i, j)) (mset_set {..<dim_col M}) = (image_mset (\<lambda> j. M $$(i, j)) (mset_set {..<dim_col M}))"
    by (meson multiset.map_cong0)
  then have img_eq: "image_mset (real_of_int) (image_mset (\<lambda> j. M\<^sub>m $$(i, j)) (mset_set {..<dim_col M})) = (image_mset (\<lambda> j. M $$(i, j)) (mset_set {..<dim_col M}))"
    by simp
  have "count_vec (row M\<^sub>m i) x = count (vec_mset (row M\<^sub>m i)) x" by simp
  also have "... = count (image_mset (vec_index (row M\<^sub>m i)) (mset_set {..<dim_vec (row M\<^sub>m i)})) x" using vec_mset_def
    by metis 
  also have "... = count (image_mset (vec_index (row M\<^sub>m i)) (mset_set {..<dim_col  M\<^sub>m })) x" using assms by simp
  also have t: "... = count (image_mset (\<lambda> j. M\<^sub>m $$(i, j)) (mset_set {..<dim_col  M\<^sub>m})) x" using eq assms
    by (metis (no_types, lifting) count_greater_zero_iff count_mset_set(3) image_mset_cong2 less_numeral_extra(3))
  also have "... = count (image_mset (\<lambda> j. M\<^sub>m $$(i, j)) (mset_set {..<dim_col M})) x" using mat_mod_dim by simp 
  also have 2: "... = count (image_mset (\<lambda> j. M $$(i, j)) (mset_set {..<dim_col M})) x" using img_eq inj count_image_mset_inj
    by metis 
  also have 1: "... = count (image_mset (\<lambda> j. (row M i) $ j) (mset_set {..<dim_col M})) x" using assms eq2
    by (metis (no_types, lifting) count_greater_zero_iff count_mset_set(3) image_mset_cong2 less_numeral_extra(3))
  also have "... = count (image_mset (vec_index (row M i)) (mset_set {..<dim_vec (row M i)})) x" using assms by simp
  finally show ?thesis using vec_mset_def
    by (metis 1 2 index_row(2) inc_mat_mod_dim(2) t) 
qed

lemma mat_mod_count_col_eq: 
  assumes "j < dim_col M"
  shows "count_vec (col M\<^sub>m j) x = count_vec (col M j) x"
proof - 
  have inj: "inj real_of_int"
    by (simp add: of_int_hom.inj_f) 
  have eq: "\<And> i. i \<in>{..<dim_row  M\<^sub>m} \<Longrightarrow> (col M\<^sub>m j) $ i = M\<^sub>m $$(i, j)" using assms
    by (simp) 
  have eq2: "\<And> i. i \<in>{..<dim_row  M} \<Longrightarrow> (col M j) $ i = M $$(i, j)" using assms
    by (simp) 
  have eq3: "\<And> i. i \<in># mset_set {..<dim_row M} \<Longrightarrow> M\<^sub>m $$ (i, j) = M $$ (i, j)" 
    using assms inc_mat_mod_index by simp
  then have "image_mset (\<lambda> i. M\<^sub>m $$(i, j)) (mset_set {..<dim_row M}) = (image_mset (\<lambda> i. M $$(i, j)) (mset_set {..<dim_row M}))"
    by (meson multiset.map_cong0)
  then have img_eq: "image_mset (real_of_int) (image_mset (\<lambda> i. M\<^sub>m $$(i, j)) (mset_set {..<dim_row M})) = (image_mset (\<lambda> i. M $$(i, j)) (mset_set {..<dim_row M}))"
    by simp
  have "count_vec (col M\<^sub>m j) x = count (vec_mset (col M\<^sub>m j)) x" by simp
  also have "... = count (image_mset (vec_index (col M\<^sub>m j)) (mset_set {..<dim_vec (col M\<^sub>m j)})) x" using vec_mset_def
    by metis 
  also have "... = count (image_mset (vec_index (col M\<^sub>m j)) (mset_set {..<dim_row  M\<^sub>m })) x" using assms by simp
  also have t: "... = count (image_mset (\<lambda> i. M\<^sub>m $$(i, j)) (mset_set {..<dim_row  M\<^sub>m})) x" using eq assms
    by (metis (no_types, lifting) count_greater_zero_iff count_mset_set(3) image_mset_cong2 less_numeral_extra(3))
  also have "... = count (image_mset (\<lambda> i. M\<^sub>m $$(i, j)) (mset_set {..<dim_row M})) x" using mat_mod_dim by simp 
  also have 2: "... = count (image_mset (\<lambda> i. M $$(i, j)) (mset_set {..<dim_row M})) x" using img_eq inj count_image_mset_inj
    by metis 
  also have 1: "... = count (image_mset (\<lambda> i. (col M j) $ i) (mset_set {..<dim_row M})) x" using assms eq2
    by (metis (no_types, lifting) count_greater_zero_iff count_mset_set(3) image_mset_cong2 less_numeral_extra(3))
  also have "... = count (image_mset (vec_index (col M j)) (mset_set {..<dim_vec (col M j)})) x" using assms by simp
  finally show ?thesis using vec_mset_def
    by (metis "1" "2" dim_col inc_mat_mod_dim(1) t)
qed

lemma mat_mod_rep_num_eq: 
  assumes "i < dim_row M"
  shows "mat_rep_num M\<^sub>m i = mat_rep_num M i"
  by (simp add: mat_mod_count_row_eq mat_rep_num_def assms)

lemma mat_point_index_eq: 
  assumes "\<And> i. i\<in> I \<Longrightarrow> i < dim_row M"
  shows "mat_point_index M\<^sub>m I = mat_point_index M I"
proof - 
  have "\<And> j. j < dim_col M\<^sub>m \<Longrightarrow> j < dim_col M"
    by (simp)
  then have "\<And> j. j < dim_col M\<^sub>m \<Longrightarrow> ((\<forall> i \<in> I. M\<^sub>m $$ (i, j) = 1) \<longleftrightarrow> (\<forall> i \<in> I. M $$ (i, j) = 1))"
    by (metis assms inc_mat_mod_index of_int_eq_1_iff)
  then have eq: "\<And> j. ((j < dim_col M\<^sub>m \<and> (\<forall> i \<in> I. M\<^sub>m $$ (i, j) = 1)) \<longleftrightarrow> (j < dim_col M \<and> (\<forall> i \<in> I. M $$ (i, j) = 1)))"
    by (metis inc_mat_mod_dim(2))
  then show ?thesis by (simp add: mat_point_index_def)
qed

lemma mod_mat_inter_num_eq: 
  assumes "j1 < dim_col M" "j2 < dim_col M"
  shows "mat_inter_num M\<^sub>m j1 j2 = mat_inter_num M j1 j2"
proof -
  have "\<And> i. i < dim_row M\<^sub>m \<longleftrightarrow> i < dim_row M"
    by (simp)
  then have "\<And> i. i < dim_row M \<Longrightarrow> (M\<^sub>m $$ (i, j1) = M\<^sub>m $$ (i, j2) \<and> M\<^sub>m $$ (i, j1) \<noteq> 0) \<longleftrightarrow> (M $$ (i, j1) = M $$ (i, j2) \<and> M $$ (i, j1) \<noteq> 0)"
    by (metis assms(1) assms(2) inc_mat_mod_index of_int_eq_iff of_int_hom.hom_zero)
  then have "\<And> i. (i < dim_row M\<^sub>m \<and> M\<^sub>m $$ (i, j1) = M\<^sub>m $$ (i, j2) \<and> M\<^sub>m $$ (i, j1) \<noteq> 0) \<longleftrightarrow> (i < dim_row M \<and> M $$ (i, j1) = M $$ (i, j2) \<and> M $$ (i, j1) \<noteq> 0)"
    by (metis inc_mat_mod_dim(1))
  thus ?thesis by (simp add: mat_inter_num_def)
qed

lemma mod_mat_block_size: 
  assumes "j < dim_col M"
  shows "mat_block_size M\<^sub>m j = mat_block_size M j"
proof -
  have  "set\<^sub>v (col M\<^sub>m j) \<subseteq> {0, 1}" using mat_mod_elems assms
    by (simp add: mat_mod_dim(2) subset_eq vec_contains_col_elements_mat) 
  then have "mat_block_size M\<^sub>m j = count_vec (col M\<^sub>m j) 1"
    using count_vec_sum_0_pair
    by (metis zero_neq_one)
  also have "... = count_vec (col M j) 1" using mat_mod_count_col_eq
    by (simp add: assms)
  finally show ?thesis by (simp add: assms mat_block_size_01)
qed

lemma inc_mat_mod_alt_def: 
"M\<^sub>m = map_mat (\<lambda> x. \<lfloor>x\<rfloor> mod m) M"
proof -
  have fn: "(\<lambda> x. x mod m) \<circ> floor = (\<lambda> x. (floor x) mod m)" by auto
  have  "M\<^sub>m = mat_mod (map_mat (floor) M)"
    by simp
  also have "... = map_mat (\<lambda> x. x mod m) (map_mat floor M)" by (simp add: mat_mod_def)
  also have "... = map_mat ((\<lambda> x. x mod m) \<circ> floor) M" using map_mat_compose by auto
  finally show ?thesis using fn
    by (simp add: \<open>M\<^sub>m = map_mat (\<lambda>x. x mod m) (map_mat floor M)\<close> mat_eq_iff) 
qed

lemma inc_mat_mod_map_col: 
  assumes "j < dim_col M"
  shows "col M\<^sub>m j = map_vec (\<lambda> x. \<lfloor>x\<rfloor> mod m) (col M j)"
  using inc_mat_mod_alt_def assms  by simp

lemma inc_mat_mod_map_row: 
  assumes "i < dim_row M"
  shows "row M\<^sub>m i = map_vec (\<lambda> x. \<lfloor>x\<rfloor> mod m) (row M i)"
  using  inc_mat_mod_alt_def assms by simp

lemma inc_mat_mod_map_inv: 
  shows "M = map_mat (\<lambda> x. real_of_int x) M\<^sub>m"
  using  inc_mat_mod_alt_def inc_mat_mod_index by auto 

lemma inc_mat_mod_map_col_inv: 
  assumes "j < dim_col M"
  shows "col M j = map_vec (real_of_int) (col M\<^sub>m j)"
  using inc_mat_mod_map_inv assms
  by (metis col_map_mat inc_mat_mod_dim(2)) 

lemma inc_mat_mod_map_row_inv: 
  assumes "i < dim_row M"
  shows "row M i = map_vec (real_of_int) (row M\<^sub>m i)"
  using inc_mat_mod_map_inv assms
  by (metis row_map_mat inc_mat_mod_dim(1)) 

(* CHECK WEIRD AUTO TRANSFER INDUCT RULE *)
(* 
lemma distinct_map:
  "distinct(map f xs) = (distinct xs \<and> inj_on f (set xs))"*)
lemma mat_mod_distinct_cols_iff: 
"distinct (cols M) \<longleftrightarrow> distinct (cols M\<^sub>m)"
proof (rule iffI)
  assume "distinct (cols M)"
  have map: "cols M\<^sub>m = map (map_vec (\<lambda> x. \<lfloor>x\<rfloor> mod m)) (cols M)"
    using list_eq_iff_nth_eq inc_mat_mod_map_col inc_mat_mod_dim
    by (metis (mono_tags, lifting) cols_length cols_nth length_map nth_map)
  have "inj_on (map_vec (\<lambda> x. \<lfloor>x\<rfloor> mod m)) (set (cols M))" 
    using inc_mat_mod_map_col by (intro inj_onI) (metis cols_length cols_nth inc_mat_mod_map_col_inv obtain_set_list_item) 
  thus "distinct (cols M\<^sub>m)" using distinct_map map
    using \<open>distinct (cols M)\<close> by auto 
next
  assume a2: "distinct (cols M\<^sub>m)"
  have map: "cols M = map (map_vec (real_of_int)) (cols M\<^sub>m)"
    using list_eq_iff_nth_eq inc_mat_mod_map_col_inv inc_mat_mod_dim
    by (metis (mono_tags, lifting) cols_length cols_nth length_map nth_map)
  have "inj_on (map_vec (real_of_int)) (set (cols M\<^sub>m))" 
    by (intro inj_onI, simp add: of_int_hom.vec_hom_inj) 
  thus "distinct (cols M)"
    using a2 map distinct_map by auto
qed

end

interpretation to_int_hom: inj_semiring_hom to_int_mod_ring
  apply unfold_locales

locale map_mat_inj_zero_hom = base: inj_zero_hom
begin
  sublocale inj_zero_hom "map_mat hom"
  proof (unfold_locales)
    fix p q :: "'a poly" assume "map_poly hom p = map_poly hom q"
    from cong[of "\<lambda>p. coeff p _", OF refl this] show "p = q" by (auto intro: poly_eqI)
  qed simp
end
locale mat_mod_type = mat_mod m
  for m and ty :: "'a :: nontriv itself" +
  assumes m: "m = CARD('a)"
begin


definition MM_Rel :: "int mat \<Rightarrow> 'a mod_ring mat \<Rightarrow> bool"
  where "MM_Rel f f' \<equiv> (mat_mod f = to_int_mat f')"

lemma eq_dim_row_MM_Rel[transfer_rule]: "(MM_Rel ===> (=)) dim_row dim_row "
  by (metis (mono_tags) MM_Rel_def index_map_mat(2) mat_mod_dim(1) rel_funI)

lemma eq_dim_col_MM_Rel[transfer_rule]: "(MM_Rel ===> (=)) dim_col dim_col "
  unfolding MM_Rel_def rel_fun_def
  by (metis index_map_mat(3) mat_mod_dim(2)) 

lemma eq_MM_Rel[transfer_rule]: "(MM_Rel ===> MM_Rel ===> (=)) (\<lambda> f f' . mat_mod f = mat_mod f') (=) "
  unfolding MM_Rel_def rel_fun_def apply (auto)
  apply (intro eq_matI)
apply (metis index_map_mat(1) index_map_mat(2) index_map_mat(3) to_int_mod_ring_hom.injectivity)
  apply (metis index_map_mat(2))
  by (metis index_map_mat(3))
  
lemma proper_inc_mat_MM_Rel[transfer_rule]: "(MM_Rel ===>  (=) ) (proper_inc_mat ) (proper_inc_mat)"
  unfolding MM_Rel_def rel_fun_def
  by (metis index_map_mat(2) index_map_mat(3) mat_mod_dim(1) mat_mod_dim(2) proper_inc_mat_def)  

lemma mat_rep_num_MM_Rel[transfer_rule]: "(MM_Rel ===>  (=) ) (\<lambda> A. mat_rep_num (mat_mod A)  i = x) (\<lambda> B. mat_rep_num B i = x)"
  unfolding MM_Rel_def rel_fun_def mat_rep_num_def

end



(* Include lemmas like 
- count is the same
- 
*)



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
  interpret vs: vec_space "TYPE('b::{prime_card} mod_ring)" \<v> . 
  define N2 :: "'b mod_ring mat" where "N2 \<equiv> mat \<v> \<b> (\<lambda> (i, j). if (N $$ (i, j) = 1) then 1 else 0)"
  have "\<And>i j. i < dim_row N \<Longrightarrow> j < dim_col N \<Longrightarrow> (N $$ (i, j)) = (to_int_mod_ring (N2 $$ (i, j)))"
  proof -
    fix i j
    assume bounds: "i < dim_row N" "j < dim_col N"
    thus "(N $$ (i, j)) = (to_int_mod_ring (N2 $$ (i, j)))"
    proof (cases "N $$ (i, j) = 1")
      case True
      then have "N2 $$ (i, j) = 1" using N2_def bounds
        using dim_row_is_v by fastforce
      then show ?thesis
        by (simp add: True) 
    next
      case False
      then have "N $$ (i, j) = 0"
        using bounds(1) bounds(2) elems_are_one_zero by blast
      then have "N2 $$ (i, j) = 0" using N2_def bounds dim_row_is_v by fastforce
      then show ?thesis
        by (simp add: \<open>N $$ (i, j) = 0\<close>) 
    qed
  qed
  have N2_elems_01: "elements_mat N2 \<subseteq> {0, 1}" apply (auto simp add: N2_def elements_matI)
    using dim_row_mat(1) elements_matD by fastforce  
  have dimv: "vs.dim  = \<v>" using vs.dim_is_n by simp
  have N2_carrier_mat: "N2 \<in> carrier_mat \<v> \<b>" 
    using N2_def by simp
  then have length_cols: "length (cols (N2)) = \<b>" by simp
  then have dim_col: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> dim_vec ((cols N2) ! j) = \<v>" 
    using N2_carrier_mat by simp
  have fin: "finite (set (cols N2))"
    by simp
  have distinct_cols_N2: "distinct (cols N2)"

    sorry
  have cv: "set (cols N2) \<subseteq> carrier_vec \<v>"
    using cols_dim dim_row_is_v N2_def
    by (metis N2_carrier_mat carrier_matD(1)) 
  have lidpt: "vs.lin_indpt (set (cols N2))" (* Easy set to relate to *)
  proof (rule vs.finite_lin_indpt2, simp_all add: cv)
    fix a assume comb: "vs.lincomb a (set (cols N2)) = 0\<^sub>v \<v>"
    define c where ceq: "c = (\<lambda> i. a ((cols N2) ! i))"
    then have listcomb: "vs.lincomb_list c (cols N2) = 0\<^sub>v \<v>" using vs.lincomb_as_lincomb_list_distinct[OF cv distinct_cols_N2] comb by simp
    have dim: "\<And> j. j < \<b> \<Longrightarrow>  dim_vec (c j \<cdot>\<^sub>v (cols N2) ! j) = \<v>" using cv
      using carrier_dim_vec nth_mem N2_carrier_mat by (simp) 
    have "\<And> v. v \<in> set (cols N2) \<Longrightarrow> a v = 0"
    proof -
      fix v assume vin: "v \<in> set (cols N2)"
      then obtain i where v_def: "cols N2 ! i = v" and ilt: "i < length (cols N2)"
        by (metis in_set_conv_nth)
      then have iin: "i \<in> {0..<\<b>}" using length_cols by simp
      have int_num_0: "\<And> j. j \<in> {0..<\<b>} \<Longrightarrow> i \<noteq> j \<Longrightarrow> v \<bullet> (c j \<cdot>\<^sub>v (cols N2) ! j) = 0" sorry
      have "(1 :: 'b :: {prime_card} mod_ring) \<noteq> 0"
        by simp 
      have "set\<^sub>v v \<subseteq> {0, 1}" using N2_elems_01 vin col_elems_subset_mat
        by (metis cols_length cols_nth dual_order.trans ilt v_def) 
      then have "\<And> i. i < \<v> \<Longrightarrow> v $ i = 0 \<or> v $ i = 1" 
        apply auto 
      have split : "{0..<\<v>} = {i . i <\<v> \<and> v $ i = 1} \<union> {i . i <\<v> \<and> v $ i = 0}" 
      have same_1: "v \<bullet> v = 1"
      proof (transfer)
        have "v \<bullet> v = (\<Sum>l \<in> {0..<\<v>} . v $ l * v $ l)" using dim_col scalar_prod_def
          by (metis (full_types) iin v_def) 
        also have "... = (\<Sum>l \<in> {0..<\<v>} . v $ l * v $ l)
        also have "... = (\<Sum> l \<in> {i . i <\<v> \<and> v $ i = 1}. v $ l * v $ l) + (\<Sum> l \<in> {i . i <\<v> \<and> v $ i = 0}. v $ l * v $ l)" using sum.split 
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