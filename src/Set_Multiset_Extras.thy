theory Set_Multiset_Extras imports Design_Theory.Multisets_Extras "HOL-Combinatorics.Multiset_Permutations" 
begin

section \<open>Micellaneous Multset/Set Extras \<close>

(* SET THEORY *)
lemma equal_card_inter_fin_eq_sets: "finite A \<Longrightarrow> finite B \<Longrightarrow> card A = card B \<Longrightarrow> card (A \<inter> B) = card A \<Longrightarrow> A = B"
  by (metis Int_lower1 Int_lower2 card_subset_eq)

lemma insert_filter_set_true: "P x \<Longrightarrow> {a \<in> (insert x A) . P a} = insert x {a \<in> A . P a}"
  by auto

lemma insert_filter_set_false: "\<not> P x \<Longrightarrow> {a \<in> (insert x A) . P a} = {a \<in> A . P a}"
  by auto  


(* MULTISET *)

lemma obtain_two_items_mset: 
  assumes "size A > 1"
  obtains x y where "x \<in># A" and "y \<in># A - {#x#}"
proof -
  obtain x where "x \<in># A"
    by (metis assms gr_implies_not_zero multiset_nonemptyE size_empty) 
  have "size (A - {#x#}) > 0"
    by (metis \<open>x \<in># A\<close> assms insert_DiffM less_irrefl_nat nonempty_has_size size_single)
  then obtain bl2 where "bl2 \<in># A - {#x#}"
    by (metis less_not_refl multiset_nonemptyE size_empty)
  thus ?thesis
    using \<open>x \<in># A\<close> that by blast 
qed

lemma obtain_two_items_mset_filter: 
  assumes "size {#a \<in># A . P a #} > 1"
  obtains x y where "x \<in># A" and "y \<in># A - {#x#}" and "P x" and "P y"
proof -
  obtain x y where xin: "x \<in># {#a \<in># A . P a #}" and yin: "y \<in># {#a \<in># A . P a #} - {#x#}"
    using obtain_two_items_mset assms by blast
  then have xdets: "x \<in># A" "P x" by auto
  then have "y \<in># {#a \<in># (A - {#x#}) . P a #}" using yin
    by force 
  then have "y \<in># (A - {#x#})" "P y"
    by (metis multiset_partition union_iff) (meson \<open>y \<in># filter_mset P (remove1_mset x A)\<close> filter_mset_eq_conv) 
  thus ?thesis using xdets that by blast
qed

lemma size_count_mset_ss: 
  assumes "finite B"
  assumes "(set_mset A) \<subseteq> B"
  shows "size A = (\<Sum> x \<in> B . count A x)"
proof -
  obtain C where cdef: "B - (set_mset A) = C" using assms
    by simp
  have fin: "finite (set_mset A)" using assms by auto
  have un: "C \<union> (set_mset A) = B"
    using Diff_partition \<open>B - set_mset A = C\<close> assms by blast 
  have disj: "C \<inter> (set_mset A) = {}"
    using \<open>B - set_mset A = C\<close> by auto 
  have zero: "\<And> x . x\<in> C \<Longrightarrow> count A x = 0"
    by (meson count_eq_zero_iff disj disjoint_iff_not_equal) 
  then have "(\<Sum> x \<in> B . count A x) = (\<Sum> x \<in> (C \<union> set_mset A) . count A x)" using un by simp
  also have "... = (\<Sum> x \<in> C . count A x) + (\<Sum> x \<in> (set_mset A) . count A x) " 
    using disj fin assms cdef sum.subset_diff by (metis un) 
  also have "... = (\<Sum> x \<in> (set_mset A) . count A x)" using zero by auto
  finally have "(\<Sum> x \<in> B . count A x) = size A"
    by (simp add: size_multiset_overloaded_eq)
  thus ?thesis by simp
qed

lemma mset_list_by_index: "mset (xs) = image_mset (\<lambda> i . (xs ! i)) (mset_set {..<length xs})"
  by (metis map_nth mset_map mset_set_upto_eq_mset_upto)

lemma count_mset_split_image_filter: 
  assumes "\<And> x. x \<in>#A \<Longrightarrow> a \<noteq> g x"
  shows "count (image_mset (\<lambda>x. if P x then a else g x) A ) a = size (filter_mset P A)"
using image_mset_If by (smt (verit) assms count_size_set_repr filter_mset_cong image_mset_filter_swap size_image_mset) 

lemma count_mset_split_image_filter_not: 
  assumes "\<And> x. x \<in>#A \<Longrightarrow> b \<noteq> f x"
  shows "count (image_mset (\<lambda>x. if P x then f x else b) A ) b = size (filter_mset (\<lambda> x. \<not> P x) A)"
  using image_mset_If by (smt (verit) assms count_size_set_repr filter_mset_cong image_mset_filter_swap size_image_mset) 

(* Permutations of Sets Extras *)

lemma elem_permutation_of_set_empty_iff: "finite A \<Longrightarrow> xs \<in> permutations_of_set A \<Longrightarrow> 
    xs = [] \<longleftrightarrow> A = {}"
  using permutations_of_setD(1) by fastforce

lemma elem_permutation_of_mset_empty_iff: "xs \<in> permutations_of_multiset A \<Longrightarrow> xs = [] \<longleftrightarrow> A = {#}"
  using permutations_of_multisetD by fastforce

(* Filter Image *)

lemma mset_image_eq_filter_eq: "A = image_mset f B \<Longrightarrow> 
  filter_mset P A = (image_mset f (filter_mset (\<lambda> x. P (f x)) B))"
  by (simp add: filter_mset_image_mset)

(* List Extras *)

lemma count_distinct_mset_list_index:
  assumes "i1 < length xs"
  assumes "i2 < length xs"
  assumes "i1 \<noteq> i2"
  assumes "distinct_mset (mset xs)"
  shows "xs ! i1 \<noteq> xs ! i2"
proof -
  have "distinct xs" using assms by auto
  show ?thesis
    by (simp add: \<open>distinct xs\<close> assms(1) assms(2) assms(3) nth_eq_iff_index_eq) 
qed

lemma index_remove1_mset_ne: 
  assumes "x \<in># (mset xs)"
  assumes "y \<in># remove1_mset x (mset xs)"
  assumes "xs ! j1 = x"
  assumes "j1 < length xs"
  obtains j2 where "xs ! j2 = y" and "j2 < length xs" and "j1 \<noteq> j2"
proof (cases "x = y")
  case True
  then have "count (mset xs) x \<ge> 2"
    using assms(2) count_eq_zero_iff by fastforce 
  then have crm: "count (remove1_mset x (mset xs)) x \<ge> 1"
    by (metis True assms(2) count_greater_eq_one_iff)  
  obtain ys zs where xseq: "xs = ys @ (x # zs)" and yseq: "ys = take j1 xs" and zseq: "zs = drop (Suc j1) xs"
    using  assms(1) assms(3) id_take_nth_drop in_mset_conv_nth assms(4) by blast 
  have "mset xs = mset ys + mset (x # zs)"
    by (simp add: xseq)
  then have "remove1_mset x (mset xs) = mset (ys) + mset (zs)"
    using assms by simp  
  then have "y \<in># (mset ys + mset zs)" using crm
    using True \<open>remove1_mset x (mset xs) = mset ys + mset zs\<close> assms(2) by presburger 
  then have yinor: "y \<in># mset ys \<or> y \<in># mset zs" by simp
  then show ?thesis proof (cases "y \<in># mset ys")
    case True
    then obtain j2 where yeq: "ys ! j2 = y" and j2lt: "j2 < length ys"
      by (meson in_mset_conv_nth)
    then have 1: "xs ! j2 = y" using yseq by simp 
    have "j2 < j1" using yseq j2lt by simp
    then show ?thesis using that 1 j2lt xseq by simp
  next
    case False
    then have "y \<in># mset zs" using yinor by simp
    then obtain j2 where zsy: "zs ! j2 = y" and j2lt: "j2 < length zs"
      by (meson in_mset_conv_nth) 
    then have 1: "xs ! ((Suc j1) + j2) = y" using zseq zsy assms(4) by simp
    have "length xs = (Suc j1) + length zs" using zseq xseq
      by (metis Suc_diff_Suc add_Suc_shift add_diff_inverse_nat assms(4) length_drop less_imp_not_less) 
    then have 2: "(Suc j1) + j2 < length xs" using j2lt by simp
    then show ?thesis using 1 that by simp
  qed
next
  case False
  then show ?thesis
    by (metis that assms(2) assms(3) in_diffD in_mset_conv_nth) 
qed

lemma count_list_mset: "count_list xs x = count (mset xs) x"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case proof (cases "a = x")
    case True
    have mset_add_split: "count (mset (a # xs)) x = count (add_mset a (mset xs)) x"
      by simp
    then have "count (mset (a # xs)) x = count (mset xs) x + 1"
      by (metis True Suc_eq_plus1 count_add_mset) 
    then show ?thesis using True Cons.hyps by simp
  next
    case False
    then show ?thesis using Cons.hyps by simp
  qed
qed

lemma count_min_2_indices_lt: 
  assumes "i1 < i2"
  assumes "xs ! i1 = x"
  assumes "xs ! i2 = x"
  assumes "i1 < length xs" "i2 < length xs"
  shows "count (mset xs) x \<ge> 2"
proof -
  obtain xs1 xs2 where xse: "xs = xs1 @ xs2" and xs1: "xs1 = take i2 xs" and xs2: "xs2 = drop i2 xs"
    by simp
  have "i1 < length xs1" using assms length_take
    by (simp add: assms(4) \<open>xs1 = take i2 xs\<close>) 
  then have xs1in:  "xs ! i1 \<in># mset xs1"
    by (simp add: nth_append xse) 
  have "i2 \<ge> length xs1" using assms length_take xs1 by simp
  then have xs2in: "xs ! i2 \<in># mset xs2" using xse nth_append
    by (metis (no_types, lifting) assms(5) in_mset_conv_nth leD leI take_all_iff take_append)
  have "count (mset xs) x = count ((mset xs1) + (mset xs2)) x"
    by (simp add: xse) 
  then have "count (mset xs) x = count (mset xs1) x + count (mset xs2) x" by simp
  thus ?thesis using xs1in xs2in
    by (metis add_mono assms(2) assms(3) count_greater_eq_one_iff nat_1_add_1) 
qed

lemma count_min_2_indices: 
  assumes "i1 \<noteq> i2"
  assumes "xs ! i1 = x"
  assumes "xs ! i2 = x"
  assumes "i1 < length xs" "i2 < length xs"
  shows "count (mset xs) x \<ge> 2"
  apply (cases "i1 < i2")
   apply (simp add: assms count_min_2_indices_lt)
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) count_min_2_indices_lt linorder_cases) 

end