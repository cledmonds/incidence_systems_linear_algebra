(* Title: Rank_Argument_General.thy
   Author: Chelsea Edmonds
*)

theory Rank_Argument_General imports Dual_Systems Jordan_Normal_Form.Determinant
Jordan_Normal_Form.DL_Rank Jordan_Normal_Form.Ring_Hom_Matrix BenOr_Kozen_Reif.More_Matrix
begin

section \<open>Row/Column Operations \<close>

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

section \<open>Rank and Linear Independence\<close>

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

abbreviation "rank v M \<equiv> vec_space.rank v M"

lemma rank_argument: 
  fixes M :: "('c :: {conjugatable_ordered_field}) mat"
  assumes "M \<in> carrier_mat x y"
  assumes "vec_space.rank x (M* M\<^sup>T) = x"
  shows "x \<le> y"
proof -
  let ?B = "(M * M\<^sup>T)"
  have Mt_car: "M\<^sup>T \<in> carrier_mat y x" using assms by simp
  have b_car: "?B \<in> carrier_mat x x"
    using transpose_carrier_mat assms by simp
  then have "rank x ?B \<le> min (rank x M) (rank y M\<^sup>T)" 
    using rank_mat_mult_lt_min_rank_factor Mt_car b_car assms(1) by blast
  thus ?thesis using le_trans vec_space.rank_le_nc 
    by (metis assms(1) assms(2) min.bounded_iff)
qed

lemma rank_argument_det: 
  fixes M :: "('c :: {conjugatable_ordered_field}) mat"
  assumes "M \<in> carrier_mat x y"
  assumes "det (M* M\<^sup>T) \<noteq> 0"
  shows "x \<le> y"
proof -
  let ?B = "(M * M\<^sup>T)"
  have Mt_car: "M\<^sup>T \<in> carrier_mat y x" using assms by simp
  have b_car: "?B \<in> carrier_mat x x"
    using transpose_carrier_mat assms by simp
  then have b_rank: "vec_space.rank x ?B = x"
    using vec_space.low_rank_det_zero assms(2) by blast
  then have "rank x ?B \<le> min (rank x M) (rank y M\<^sup>T)" 
    using rank_mat_mult_lt_min_rank_factor Mt_car b_car assms(1) by blast
  thus ?thesis using le_trans vec_space.rank_le_nc 
    by (metis assms(1) b_rank min.bounded_iff)
qed

end