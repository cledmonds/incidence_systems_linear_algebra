theory Incidence_Matrices imports "Design_Theory.BIBD" Jordan_Normal_Form.Matrix "List-Index.List_Index"
"HOL-Combinatorics.Multiset_Permutations" "Groebner_Bases.Macaulay_Matrix" "Design_Theory.Design_Isomorphisms"
begin
(*
lemma obtain_subset_with_card_n_with_x:
  assumes "n \<le> card S"
  assumes "x \<in> S"
  assumes "n \<ge> 1"
  assumes "finite S"
  obtains T where "T \<subseteq> S" "card T = n" "finite T" "x \<in> T"
proof -
  have ne: "S \<noteq> {}" using assms(2) by auto
  obtain n' where "card S = n + n'" 
    by (metis assms(1) le_add_diff_inverse)
  with that show thesis using assms
  proof (induct n arbitrary: S)
    case 0 
    then show ?case by auto 
  next
    case Suc 
    then show ?case 
      apply (simp add: card_Suc_eq) 
      using subset_insertI2 
  qed
qed

*)

lemma equal_card_inter_fin_eq_sets: "finite A \<Longrightarrow> finite B \<Longrightarrow> card A = card B \<Longrightarrow> card (A \<inter> B) = card A \<Longrightarrow> A = B"
  by (metis Int_lower1 Int_lower2 card_subset_eq)

lemma inter_num_max_bound: 
  assumes "finite b1" "finite b2"
  shows "b1 |\<inter>| b2 \<le> card b1" "b1 |\<inter>| b2 \<le> card b2"
  by(simp_all add: assms intersection_number_def card_mono)

lemma inter_eq_blocks_eq_card: 
  assumes "card b1 = card b2"
  assumes "finite b1" "finite b2"
  assumes "b1 |\<inter>| b2 = card b1"
  shows "b1 = b2"
  using equal_card_inter_fin_eq_sets intersection_number_def assms by (metis) 

lemma inter_num_of_eq_blocks: "b1 = b2 \<Longrightarrow> b1 |\<inter>| b2 = card b1"
  by (simp add: intersection_number_def)

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
    apply (metis multiset_partition union_iff)
    by (meson \<open>y \<in># filter_mset P (remove1_mset x A)\<close> filter_mset_eq_conv) 
  thus ?thesis using xdets that by blast
qed

context design
begin

lemma block_num_rep_bound: "\<b> \<le> (\<Sum> x \<in> \<V>. \<B> rep x)"
proof -
  have exists: "\<And> bl. bl \<in># \<B> \<Longrightarrow> (\<exists> x \<in> \<V> . bl \<in># {#b \<in># \<B>. x \<in> b#})" using wellformed
    using blocks_nempty by fastforce 
  then have bss: "\<B> \<subseteq># \<Sum>\<^sub># (image_mset (\<lambda> v. {#b \<in># \<B>. v \<in> b#}) (mset_set \<V>))"
  proof (intro  mset_subset_eqI)
    fix bl
    show "count \<B> bl \<le> count (\<Sum>v\<in>#mset_set \<V>. filter_mset ((\<in>) v) \<B>) bl"
    proof (cases "bl \<in># \<B>")
      case True
      then obtain x where xin: "x \<in> \<V>" and blin: "bl \<in># filter_mset ((\<in>) x) \<B>" using exists by auto
      then have eq: "count \<B> bl = count (filter_mset ((\<in>) x) \<B>) bl"
        by simp 
      have "(\<Sum>v\<in>#mset_set \<V>. filter_mset ((\<in>) v) \<B>) = (filter_mset ((\<in>) x) \<B>) + 
        (\<Sum>v\<in>#(mset_set \<V>) - {#x#}. filter_mset ((\<in>) v) \<B>)"
        using xin by (simp add: finite_sets mset_set.remove) 
      then have "count (\<Sum>v\<in>#mset_set \<V>. filter_mset ((\<in>) v) \<B>) bl = count (filter_mset ((\<in>) x) \<B>) bl + 
        count (\<Sum>v\<in>#(mset_set \<V>) - {#x#}. filter_mset ((\<in>) v) \<B>) bl"
        by simp
      then show ?thesis using eq
        by linarith 
    next
      case False
      then show ?thesis
        by (metis count_eq_zero_iff le0)
    qed
  qed
  have "(\<Sum> x \<in> \<V>. \<B> rep x) = (\<Sum> x \<in> \<V>. size ({#b \<in># \<B>. x \<in> b#}))" 
    by (simp add: point_replication_number_def)
  also have "... = (\<Sum> x \<in># (mset_set \<V>). size ({#b \<in># \<B>. x \<in> b#}))"
    by (simp add: sum_unfold_sum_mset) 
  also have "... = (\<Sum> x \<in># (image_mset (\<lambda> v. {#b \<in># \<B>. v \<in> b#}) (mset_set \<V>)) . size x)"
    by auto  
  finally have "(\<Sum> x \<in> \<V>. \<B> rep x) = size (\<Sum>\<^sub># (image_mset (\<lambda> v. {#b \<in># \<B>. v \<in> b#}) (mset_set \<V>)))" 
    using size_big_union_sum
    by metis 
  then show ?thesis using bss
    by (simp add: size_mset_mono)
qed

end

locale const_intersect_design = proper_design + 
  fixes \<m> :: nat
  assumes const_intersect: "b1 \<in># \<B> \<Longrightarrow> b2 \<in># (\<B> - {#b1#}) \<Longrightarrow> b1 |\<inter>| b2 = \<m>"

sublocale symmetric_bibd \<subseteq> const_intersect_design \<V> \<B> \<Lambda>
  by (unfold_locales) (simp)

context simple_design 
begin

lemma inter_num_lt_block_size_strict: 
  assumes "bl1 \<in># \<B>"
  assumes "bl2 \<in># \<B>"
  assumes "bl1 \<noteq> bl2"
  assumes "card bl1 = card bl2"
  shows "bl1 |\<inter>| bl2 < card bl1" "bl1 |\<inter>| bl2 < card bl2"
proof -
  have lt: "bl1 |\<inter>| bl2 \<le> card bl1" using finite_blocks
    by (simp add: \<open>bl1 \<in># \<B>\<close> \<open>bl2 \<in># \<B>\<close> inter_num_max_bound(1)) 
  have ne: "bl1 |\<inter>| bl2 \<noteq> card bl1" 
  proof (rule ccontr, simp)
    assume "bl1 |\<inter>| bl2 = card bl1"
    then have "bl1 = bl2" using assms(4) inter_eq_blocks_eq_card assms(1) assms(2) finite_blocks 
      by blast 
    then show False using assms(3) by simp
  qed
  then show "bl1 |\<inter>| bl2 < card bl1" using lt by simp
  have "bl1 |\<inter>| bl2 \<noteq> card bl2" using ne by (simp add: assms(4)) 
  then show "bl1 |\<inter>| bl2 < card bl2" using lt assms(4) by simp
qed

end

context const_intersect_design
begin

lemma inter_num_le_block_size: 
  assumes "bl \<in># \<B>"
  assumes "\<b> \<ge> 2"
  shows "\<m> \<le> card bl"
proof (rule ccontr)
  assume a: "\<not> (\<m> \<le> card bl)"
  obtain bl' where blin: "bl' \<in># \<B> - {#bl#}"
    using assms
    by (metis add_mset_add_single diff_add_inverse2 diff_is_0_eq' multiset_nonemptyE nat_1_add_1 remove1_mset_eqE size_single zero_neq_one)
  then have const: "bl |\<inter>| bl' = \<m>" using const_intersect assms by auto
  thus False using inter_num_max_bound(1) finite_blocks 
    by (metis a blin assms(1) finite_blocks in_diffD) 
qed

lemma const_inter_multiplicity_one: 
  assumes "bl \<in># \<B>"
  assumes "\<m> < card bl"
  shows "multiplicity bl = 1"
proof (rule ccontr)
  assume "multiplicity bl \<noteq> 1"
  then have "multiplicity bl > 1" using assms
    by (simp add: le_neq_implies_less)
  then obtain bl2 where "bl = bl2" and "bl2 \<in># \<B> - {#bl#}"
    by (metis count_single in_diff_count)
  then have "bl |\<inter>| bl2 = card bl"
    using inter_num_of_eq_blocks by blast  
  thus False using assms const_intersect
    by (simp add: \<open>bl2 \<in># remove1_mset bl \<B>\<close>) 
qed

lemma mult_blocks_const_inter: 
  assumes "bl \<in># \<B>"
  assumes "multiplicity bl > 1"
  assumes "\<b> \<ge> 2"
  shows "\<m> = card bl"
proof (rule ccontr)
  assume "\<m> \<noteq> card bl"
  then have "\<m> < card bl" using inter_num_le_block_size assms
    using nat_less_le by blast 
  then have "multiplicity bl = 1" using const_inter_multiplicity_one assms by simp
  thus False using assms(2) by simp
qed

lemma simple_const_inter_block_size: 
  assumes "(\<And> bl. bl \<in># \<B> \<Longrightarrow> \<m> < card bl)"
  shows "simple_design \<V> \<B>"
  using const_inter_multiplicity_one assms by (unfold_locales) (simp)

lemma simple_const_inter_iff: 
  assumes "\<b> \<ge> 2"
  shows "size {#bl \<in># \<B> . card bl = \<m>  #} \<le> 1 \<longleftrightarrow> simple_design \<V> \<B>"
proof (intro iffI)
  assume a: "size {#bl \<in># \<B>. card bl = \<m>#} \<le> 1"
  show "simple_design \<V> \<B>" 
  proof (unfold_locales)
    fix bl assume blin: "bl \<in># \<B>"
    show "multiplicity bl = 1"
    proof (cases "card bl = \<m>")
      case True
      then have m: "multiplicity bl = size {#b \<in># \<B> . b = bl#}"
        by (simp add: count_size_set_repr)
      then have "{#b \<in># \<B> . b = bl#} \<subseteq># {#bl \<in># \<B>. card bl = \<m>#}" using True
        by (simp add: mset_subset_eqI)
      then have "size {#b \<in># \<B> . b = bl#} \<le> size {#bl \<in># \<B>. card bl = \<m>#}"
        by (simp add: size_mset_mono) 
      then show ?thesis using a blin
        by (metis count_eq_zero_iff le_neq_implies_less le_trans less_one m) 
    next
      case False
      then have "\<m> < card bl" using assms
        by (simp add: blin inter_num_le_block_size le_neq_implies_less) 
      then show ?thesis using const_inter_multiplicity_one
        by (simp add: blin) 
    qed
  qed
next
  assume simp: "simple_design \<V> \<B>"
  then have mult: "\<And> bl. bl \<in># \<B> \<Longrightarrow> multiplicity bl = 1"
    using simple_design.axioms(2) simple_incidence_system.simple_alt_def_all by blast 
  show "size {#bl \<in># \<B> . card bl = \<m> #} \<le> 1"
  proof (rule ccontr)
    assume "\<not> size {#bl \<in># \<B>. card bl = \<m>#} \<le> 1"
    then have "size {#bl \<in># \<B> . card bl = \<m> #} > 1" by simp
    then obtain bl1 bl2 where blin: "bl1 \<in># \<B>" and "bl2 \<in># \<B> - {#bl1#}" and "card bl1 = \<m>" and "card bl2 = \<m>"
      using obtain_two_items_mset_filter by blast 
    then have "bl1 |\<inter>| bl2 = \<m>" using const_intersect by simp
    then have "bl1 = bl2"
      by (metis \<open>bl1 \<in># \<B>\<close> \<open>bl2 \<in># remove1_mset bl1 \<B>\<close> \<open>card bl1 = \<m>\<close> \<open>card bl2 = \<m>\<close> finite_blocks in_diffD inter_eq_blocks_eq_card)
    then have "multiplicity bl1 > 1"
      using \<open>bl2 \<in># remove1_mset bl1 \<B>\<close> count_eq_zero_iff by force 
    thus False using mult blin by simp
  qed
qed

lemma empty_inter_implies_rep_one: 
  assumes "\<m> = 0"
  assumes "x \<in> \<V>"
  shows "\<B> rep x \<le> 1"
proof (rule ccontr)
  assume "\<not> \<B> rep x \<le> 1"
  then have gt1: "\<B> rep x > 1" by simp
  then obtain bl1 where blin1: "bl1 \<in># \<B>" and xin1: "x \<in> bl1"
    by (metis gr_implies_not0 linorder_neqE_nat rep_number_g0_exists) 
  then have "(\<B> - {#bl1#}) rep x > 0" using gt1
    by (metis \<open>\<not> \<B> rep x \<le> 1\<close> add_0 eq_imp_le neq0_conv point_rep_number_split point_rep_singleton_val remove1_mset_eqE) 
  then obtain bl2 where blin2: "bl2 \<in># (\<B> - {#bl1#})" and xin2: "x \<in> bl2" 
    by (metis rep_number_g0_exists) 
  then have "x \<in> (bl1 \<inter> bl2)" using xin1 by simp
  then have "bl1 |\<inter>| bl2 \<noteq> 0"
    by (metis blin1 empty_iff finite_blocks intersection_number_empty_iff) 
  thus False using const_intersect assms blin1 blin2 by simp
qed

lemma empty_inter_implies_b_lt_v: 
  assumes "\<m> = 0"
  shows "\<b> \<le> \<v>"
proof -
  have le1: "\<And> x. x \<in> \<V> \<Longrightarrow> \<B> rep x \<le> 1" using empty_inter_implies_rep_one assms by simp
  have disj: "{v \<in> \<V> . \<B> rep v = 0} \<inter> {v \<in> \<V> . \<not> (\<B> rep v = 0)} = {}" by auto
  have eqv: "\<V> = ({v \<in> \<V> . \<B> rep v = 0} \<union> {v \<in> \<V> . \<not> (\<B> rep v = 0)})" by auto
  have "\<b> \<le> (\<Sum> x \<in> \<V> . \<B> rep x)" using block_num_rep_bound by simp
  also have 1: "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<B> rep v = 0} \<union> {v \<in> \<V> . \<not> (\<B> rep v = 0)}) . \<B> rep x)" using eqv by simp
  also have "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<B> rep v = 0}) . \<B> rep x) + (\<Sum> x \<in> ({v \<in> \<V> . \<not> (\<B> rep v = 0)}) . \<B> rep x)"
    using sum.union_disjoint finite_sets eqv disj
    by (metis (no_types, lifting) 1 finite_Un) 
  also have "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<not> (\<B> rep v = 0)}) . \<B> rep x)" by simp
  also have "... \<le> (\<Sum> x \<in> ({v \<in> \<V> . \<not> (\<B> rep v = 0)}) . 1)" using le1
    by (metis (mono_tags, lifting) mem_Collect_eq sum_mono)
  also have "... \<le> card {v \<in> \<V> . \<not> (\<B> rep v = 0)}" by simp
  also have "... \<le> card \<V>" using finite_sets
    using card_mono eqv by blast 
  finally show ?thesis by simp
qed

end

lemma insert_filter_set_true: "P x \<Longrightarrow> {a \<in> (insert x A) . P a} = insert x {a \<in> A . P a}"
  by auto

lemma insert_filter_set_false: "\<not> P x \<Longrightarrow> {a \<in> (insert x A) . P a} = {a \<in> A . P a}"
  by auto  

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

lemma index_lt_rep_general: 
  assumes "x \<in> ps"
  shows " B index ps \<le> B rep x"
  apply (simp add: points_index_def point_replication_number_def)
  by (metis assms filter_filter_mset_cond_simp size_filter_mset_lesseq subset_iff)

lemma (in constant_rep_design) index_lt_const_rep: 
  assumes "ps \<subseteq> \<V>"
  assumes "ps \<noteq> {}"
  shows "\<B> index ps \<le> \<r>"
proof -
  obtain x where xin: "x \<in> ps" using assms by auto
  then have "\<B> rep x = \<r>"
    by (meson assms(1) in_mono rep_number_alt_def_all) 
  thus ?thesis using index_lt_rep_general xin by auto
qed

lemma (in t_wise_balance) obtain_t_subset_with_point: 
  assumes "x \<in> \<V>"
  obtains ps where "ps \<subseteq> \<V>" and "card ps = \<t>" and "x \<in> ps"
proof (cases "\<t> = 1")
  case True
  have "{x} \<subseteq> \<V>" "card {x} = 1" "x \<in> {x}"
    using assms by simp_all
  then show ?thesis
    using True that by blast 
next
  case False
  have "\<t> - 1 \<le> card (\<V> - {x})"
    by (simp add: assms diff_le_mono finite_sets t_lt_order) 
  then obtain ps' where psss: "ps' \<subseteq> (\<V> - {x})" and psc: "card ps' = \<t> - 1" by (meson obtain_subset_with_card_n)
  then have xs: "(insert x ps') \<subseteq> \<V>"
    using assms by blast 
  have xnotin: "x \<notin> ps'" using psss
    by blast 
  then have "card (insert x ps') = Suc (card ps')"
    by (meson \<open>insert x ps' \<subseteq> \<V>\<close> finite_insert card_insert_disjoint finite_sets finite_subset) 
  then have "card (insert x ps') = card ps' + 1"
    by presburger 
  then have xc: "card (insert x ps') = \<t>" using psc
    using add.commute add_diff_inverse t_non_zero by linarith 
  have "x \<in> (insert x ps')" by simp
  then show ?thesis using xs xc that by blast 
qed

context t_wise_balance
begin
lemma const_index_lt_rep: 
  assumes "x \<in> \<V>"
  shows "\<Lambda>\<^sub>t \<le> \<B> rep x"
proof -
  obtain ps where psin: "ps \<subseteq> \<V>" and "card ps = \<t>" and xin: "x \<in> ps" using assms t_lt_order obtain_t_subset_with_point by auto
  then have "\<B> index ps = \<Lambda>\<^sub>t " using balanced by simp
  thus ?thesis using index_lt_rep_general xin 
    by (meson) 
qed

end
context pairwise_balance
begin

lemma index_zero_iff: "\<Lambda> = 0 \<longleftrightarrow> (\<forall> bl \<in># \<B> . card bl = 1)"
proof (auto)
  fix bl assume l0: "\<Lambda> = 0" assume blin: "bl \<in># \<B>"
  have "card bl = 1"
  proof (rule ccontr)
    assume "card bl \<noteq> 1"
    then have "card bl \<ge> 2" using block_size_gt_0
      by (metis Suc_1 Suc_leI blin less_one nat_neq_iff) 
    then obtain ps where psss: "ps \<subseteq> bl" and pscard: "card ps = 2"
      by (meson obtain_subset_with_card_n)
    then have psin: "\<B> index ps \<ge> 1"
      using blin points_index_count_min by auto
    have "ps \<subseteq> \<V>" using wellformed psss blin by auto
    then show False using balanced l0 psin pscard by auto
  qed
  thus "card bl = (Suc 0)" by simp
next
  assume a: "\<forall>bl\<in>#\<B>. card bl = Suc 0"
  obtain ps where psss: "ps \<subseteq> \<V>" and ps2: "card ps = 2"
    by (meson obtain_t_subset_points) 
  then have "\<And> bl. bl \<in># \<B> \<Longrightarrow> (card ps > card bl)" using a
    by simp 
  then have cond: "\<And> bl. bl \<in># \<B> \<Longrightarrow> \<not>( ps \<subseteq>  bl)"
    by (metis card_mono finite_blocks le_antisym less_imp_le_nat less_not_refl3) 
  have "\<B> index ps = size {# bl \<in># \<B> . ps \<subseteq> bl #}" by (simp add:points_index_def)
  then have "\<B> index ps = size {#}" using cond
    by (metis points_index_0_iff size_empty) 
  thus "\<Lambda> = 0" using psss ps2 balanced by simp
qed


end

(* Extra vector lemmas *)
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
  assumes "\<And> i. i < dim_vec (vCons a v) \<Longrightarrow> (vCons a v) $ i \<le> (n ::real)"
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
  assumes "\<And> i. i < dim_vec (v :: real vec) \<Longrightarrow> v $ i \<le> (1 ::real)"
  shows "sum_vec v \<le> dim_vec v"
  using assms 
proof (induct v)
  case vNil
  then show ?case by simp
next
  case (vCons a v)
  then have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i \<le> (1 ::real))"
    using vCons.prems by force
  then have lt: "sum_vec v \<le> real (dim_vec v)" by (simp add: vCons.hyps)  
  then show ?case using sum_vec_vCons_lt lt vCons.prems by simp
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

lemma vec_mset_vNil: "vec_mset vNil = {#}" 
  by (simp add: vec_mset_def)

lemma vec_mset_vCons: "vec_mset (vCons x v) = add_mset x (vec_mset v)"
proof -
  have "vec_mset (vCons x v) = mset (list_of_vec (vCons x v))"
    by (simp add: mset_vec_eq_mset_list)
  then have "mset (list_of_vec (vCons x v)) = add_mset x (mset (list_of_vec v))"
    by simp 
  thus ?thesis
    by (metis mset_vec_eq_mset_list) 
qed

lemma vec_mset_set: "vec_set v = set_mset (vec_mset v)"
  by (simp add: mset_vec_eq_mset_list set_list_of_vec)

abbreviation "count_vec v a \<equiv> count (vec_mset v) a"

lemma vec_count_lt_dim: "count_vec v a \<le> dim_vec v"
  by (metis mset_vec_same_size order_refl set_count_size_min)

lemma count_vec_empty: "dim_vec v = 0 \<Longrightarrow> count_vec v a = 0"
  by (simp add: mset_vec_same_size)

lemma count_vec_vNil: "count_vec vNil a = 0"
  by (simp add: vec_mset_def)

lemma count_vec_vCons: "count_vec (vCons aa v) a = (if (aa = a) then count_vec v a + 1 else count_vec v a)"
  by(simp add: vec_mset_vCons)

lemma elem_exists_count_min: "\<exists> i \<in>{..<dim_vec v}. v $ i = x \<Longrightarrow> count_vec v x \<ge> 1"
  by (simp add: vec_elem_exists_mset)

lemma mset_list_by_index: "mset (xs) = image_mset (\<lambda> i . (xs ! i)) (mset_set {..<length xs})"
  by (metis dim_vec_of_list image_mset_cong list_vec mset_vec_eq_mset_list vec_mset_def vec_of_list_index)

lemma count_vec_count_mset:
  assumes "vec_mset v = image_mset f A"
  shows "count_vec v a = count (image_mset f A) a"
  by (simp add: assms)

lemma count_vec_alt_list: "count_vec v a = length (filter (\<lambda>y. a = y) (list_of_vec v))"
proof -
  have "count_vec v a = count (mset (list_of_vec v)) a" by (simp add: mset_vec_eq_mset_list)
  thus ?thesis by (metis count_mset) 
qed

lemma count_vec_alt: "count_vec v x = card { i. v $ i = x \<and> i< dim_vec v}"
proof -
  have "count_vec v x = count (image_mset (($) v) (mset_set {..<dim_vec v})) x" by (simp add: vec_mset_def)
  also have "... = size {#a \<in># (image_mset (($) v) (mset_set {..<dim_vec v})) . x = a#}"
    by (simp add: filter_mset_eq)
  also have "... = size {#a \<in># (mset_set {..<dim_vec v}) . x = (v $ a) #}"
    by (simp add: filter_mset_image_mset)
  finally have "count_vec v x = card {a \<in> {..<dim_vec v} . x = (v $ a)}" by simp
  thus ?thesis by (smt (verit) Collect_cong lessThan_iff) 
qed

lemma count_vec_sum_ones: 
  assumes "\<And> i. i < dim_vec (v :: real vec) \<Longrightarrow> v $ i = 1 \<or> v $ i = 0"
  shows "count_vec v 1 = sum_vec v"
  using assms 
proof (induct v)
  case vNil 
  then show ?case
     by (simp add: vec_mset_vNil)  
 next
  case (vCons a v)
  then have lim: "dim_vec (vCons a v) \<ge> 1"
    by simp 
  have "(\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v$ i = 0)"
    using vCons.prems by force
  then have hyp: "count_vec v 1 = sum_vec v"
    by (simp add: vCons.hyps) 
  have "sum (($) (vCons a v)) {0..<dim_vec (vCons a v)} = sum_vec (vCons a v)" by (simp add: sum_vec_def)
  then have sv: "sum (($) (vCons a v)) {0..<dim_vec (vCons a v)} = sum_vec (v) + a" by (simp add: sum_vec_vCons)
  then show ?case
    by (metis add.commute add.left_neutral count_vec_vCons dim_vec_vCons_ne_0 hyp of_nat_1 of_nat_add sum_vec_vCons vCons.prems vec_index_vCons_0)
qed

lemma count_vec_two_elems: 
  assumes "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = (1 ::real) \<or> v $ i = 0"
  shows "count_vec v 1 + count_vec v 0 = dim_vec v"
proof -
  have ss: "vec_set v \<subseteq> {0, 1}" using assms by (auto simp add: vec_set_def)
  have "dim_vec v = size (vec_mset v)"
    by (simp add: mset_vec_same_size) 
  have "size (vec_mset v) = (\<Sum> x \<in> (vec_set v) . count (vec_mset v) x)"
    by (simp add: vec_mset_set size_multiset_overloaded_eq) 
  also have  "... = (\<Sum> x \<in> {0, 1} . count (vec_mset v) x)"
    using size_count_mset_ss ss
    by (metis calculation finite.emptyI finite.insertI vec_mset_set)
  finally have "size (vec_mset v) = count (vec_mset v) 0 + count (vec_mset v) 1" by simp
  thus ?thesis
    by (simp add: \<open>dim_vec v = size (vec_mset v)\<close>) 
qed

lemma count_vec_sum_zeros: 
  assumes "\<And> i. i < dim_vec (v :: real vec) \<Longrightarrow> v $ i = 1 \<or> v $ i = 0"
  shows "count_vec v 0 = dim_vec v - sum_vec v"
  using count_vec_two_elems assms count_vec_sum_ones
  by force 

lemma count_vec_sum_ones_alt: 
  assumes "vec_set v \<subseteq> {0::real, 1}"
  shows "count_vec v 1 = sum_vec v"
proof -
  have "\<And> i. i < dim_vec v \<Longrightarrow> v $ i = 1 \<or> v $ i = 0" using assms
    by (meson insertE singletonD subsetD vec_setI) 
  thus ?thesis by (simp add: count_vec_sum_ones)
qed

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

definition all_ones_vec ::  "nat \<Rightarrow> 'a :: {zero,one} vec" ("u\<^sub>v") where
  "u\<^sub>v n \<equiv> vec n (\<lambda> i. 1)"

lemma dim_vec_all_ones[simp]: "dim_vec (u\<^sub>v n) = n"
  by (simp add: all_ones_vec_def)

lemma all_ones_index [simp]: "i < n \<Longrightarrow> u\<^sub>v n $ i = 1"
  by (simp add: all_ones_vec_def)

lemma dim_vec_mult_vec_mat [simp]: "dim_vec (v \<^sub>v* A) = dim_col A"
  unfolding mult_vec_mat_def by simp

lemma all_ones_vec_smult[simp]: "i < n \<Longrightarrow> ((k :: ('a :: {one, zero, monoid_mult})) \<cdot>\<^sub>v (u\<^sub>v n)) $ i = k"
  by (simp add: smult_vec_def)

(* Matrix extras *)

definition all_ones_mat :: "nat \<Rightarrow> 'a :: {zero,one} mat" ("J\<^sub>m") where
  "J\<^sub>m n \<equiv> mat n n (\<lambda> (i,j). 1)"

lemma all_ones_mat_index[simp]: "i < dim_row (J\<^sub>m n) \<Longrightarrow> j < dim_col (J\<^sub>m n) \<Longrightarrow> J\<^sub>m n $$ (i, j)= 1"
  by (simp add: all_ones_mat_def)

lemma all_ones_mat_dim_row[simp]: "dim_row (J\<^sub>m n) = n"
  by (simp add: all_ones_mat_def)

lemma all_ones_mat_dim_col[simp]: "dim_col (J\<^sub>m n) = n"
  by (simp add: all_ones_mat_def)

lemma index_mult_vec_mat[simp]: "j < dim_col A \<Longrightarrow> (v \<^sub>v* A) $ j = v \<bullet> col A j"
  by (auto simp: mult_vec_mat_def)

lemma transpose_mat_mult_entries: 
  assumes "i < dim_row A" and "j < dim_row A"
  shows "(A * A\<^sup>T) $$ (i, j) = (\<Sum>k\<in> {0..<(dim_col A)}. (A $$ (i, k)) * (A $$ (j, k)))"
  using assms by (simp add: times_mat_def scalar_prod_def)

lemma transpose_mat_elems: "elements_mat A = elements_mat A\<^sup>T"
  apply (auto simp add: transpose_mat_def)
   apply (metis elements_matD elements_matI index_transpose_mat(1) mat_carrier transpose_mat_def)
  by fastforce

lemma row_elems_subset_mat: "i < dim_row N \<Longrightarrow> vec_set (row N i) \<subseteq> elements_mat N"
  by (auto simp add: vec_set_def elements_matI)

lemma col_elems_subset_mat: "i < dim_col N \<Longrightarrow> vec_set (col N i) \<subseteq> elements_mat N"
  by (auto simp add: vec_set_def elements_matI)

(* Permutations of Sets Extras *)

lemma elem_permutation_of_set_empty_iff: "finite A \<Longrightarrow> xs \<in> permutations_of_set A \<Longrightarrow> 
    xs = [] \<longleftrightarrow> A = {}"
  using permutations_of_setD(1) by fastforce

lemma elem_permutation_of_mset_empty_iff: "xs \<in> permutations_of_multiset A \<Longrightarrow> xs = [] \<longleftrightarrow> A = {#}"
  using permutations_of_multisetD by fastforce


(* Incidence vectors *)
definition inc_vec_of :: "'a list \<Rightarrow> 'a set \<Rightarrow> real vec" where
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

definition inc_mat_of :: "'a list \<Rightarrow> 'a set list \<Rightarrow> real mat" where
"inc_mat_of Vs Bs \<equiv> mat (length Vs) (length Bs) (\<lambda> (i,j) . if (Vs ! i) \<in> (Bs ! j) then 1 else 0)"

lemma inc_mat_one_zero_elems: "elements_mat (inc_mat_of Vs Bs) \<subseteq> {0, 1}"
  by (auto simp add: inc_mat_of_def elements_mat_def)

lemma fin_incidence_mat_elems: "finite (elements_mat (inc_mat_of Vs Bs))"
  using finite_subset inc_mat_one_zero_elems by auto 

lemma inc_matrix_elems_max_two: "card (elements_mat (inc_mat_of Vs Bs)) \<le> 2"
proof -
  have "card {0 ::real , 1} = 2" by auto
  thus ?thesis using card_mono inc_mat_one_zero_elems
    by (metis finite.emptyI finite.insertI) 
qed

lemma inc_mat_of_index [simp]: "i < dim_row (inc_mat_of Vs Bs) \<Longrightarrow> j < dim_col (inc_mat_of Vs Bs) \<Longrightarrow> 
  inc_mat_of Vs Bs $$ (i, j) = (if (Vs ! i) \<in> (Bs ! j) then 1 else 0)"
  by (simp add: inc_mat_of_def)

lemma inc_mat_dim_row [simp]: "dim_row (inc_mat_of Vs Bs) = length Vs"
  by (simp add: inc_mat_of_def)

lemma inc_mat_dim_vec_row: "dim_vec (row (inc_mat_of Vs Bs) i) = length Bs"
  by (simp add:  inc_mat_of_def)

lemma inc_mat_dim_col [simp]: "dim_col (inc_mat_of Vs Bs) = length Bs"
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
  by(intro eq_vecI) (simp_all add: inc_mat_col_list_map_elem assms index_vec_of_list)

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
  by (intro eq_vecI) (simp_all add: inc_mat_row_list_map_elem assms index_vec_of_list)


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


context finite_incidence_system
begin

definition indexes:: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"indexes f \<equiv> bij_betw f {0..< \<v>} \<V>"

end

(* Most incidence matrices are 0, 1 representations *)
locale zero_one_matrix = 
  fixes matrix :: "real mat" ("M")
  assumes elems01: "elements_mat M \<subseteq> {0, 1}"
begin

definition map_to_points:: "nat set" where
"map_to_points \<equiv> {0..<dim_row M}"

lemma map_to_points_card: "card (map_to_points) = dim_row M"
  by (simp add: map_to_points_def)

definition map_col_to_block :: "real vec  \<Rightarrow> nat set" where
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

definition map_block_to_col :: "nat set \<Rightarrow> real vec" where
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

interpretation zero_one_matrix "inc_mat_of Vs Bs"
  by (unfold_locales) (simp add: inc_mat_one_zero_elems) 

lemma inc_mat_ordered_points_Vs: "map ((!) Vs) (map_to_points_ordered inc_mat Vs Bs) = Vs"
  by (auto simp add: map_to_points_ordered_def  map_nth)

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
  obtains bl1 bl2 where "bl1 \<in># \<B>" and "\<B>s ! j1 = bl1" and "bl2 \<in># \<B> - {#bl1#}" and "\<B>s ! j2 = bl2"
proof -
  obtain bl1 where bl1in: "bl1 \<in># \<B>" and bl1eq: "\<B>s ! j1 = bl1"
    using assms(1) valid_blocks_index by blast
  then obtain xs ys where "\<B>s = xs @ (bl1 # ys)" using split_list
    by (metis bl1in in_multiset_in_set) 
  thus ?thesis sorry
qed

(* Incidence Matrix *)

abbreviation N :: "real mat" where
"N \<equiv> inc_mat_of \<V>s \<B>s"

lemma N_alt_def_dim: "N = mat \<v> \<b> (\<lambda> (i,j) . if (incident (\<V>s ! i) (\<B>s ! j)) then 1 else 0) " 
  using incidence_cond_indexed inc_mat_of_def 
  by (intro eq_matI) (simp_all add: inc_matrix_point_in_block_one inc_matrix_point_not_in_block_zero 
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
  by (simp add: points_list_length)

lemma dim_vec_col: "dim_vec (col N i) = \<v>"
  by (simp add: N_alt_def_dim)

lemma mat_row_elems: "i < \<v> \<Longrightarrow> vec_set (row N i) \<subseteq> {0, 1}"
  using points_list_length
  by (simp add: dim_row_is_v dim_row_length row_elems_ss01) 

lemma mat_col_elems: "j < \<b> \<Longrightarrow> vec_set (col N j) \<subseteq> {0, 1}"
  using blocks_list_length
  by (metis col_elems_ss01 dim_col_is_b)

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
  shows "\<B>s ! j = (\<lambda> k . \<V>s ! k) ` map_col_to_block (col N j)"
  using matrix_col_to_block map_col_to_block_def assms
  by (simp add: points_list_length)

lemma matrix_col_in_blocks: "j < \<b> \<Longrightarrow> (!) \<V>s ` map_col_to_block (col N j) \<in># \<B>"
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
  have "\<And>bl. bl \<in># \<B> \<Longrightarrow> (\<lambda>x .0 ::real) bl \<noteq> 1" using zero_neq_one 
    by simp 
  then have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: real )) \<B>) 1 = 
    size (filter_mset (\<lambda> x . (\<V>s ! i) \<in> x) \<B>)"
    using count_mset_split_image_filter[of "\<B>" "1" "\<lambda> x . (0 :: real)" "\<lambda> x . (\<V>s ! i) \<in> x"] by simp
  then have "count (image_mset (\<lambda> x . if ((\<V>s ! i) \<in> x) then 1 else (0 :: real )) \<B>) 1
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
  have "\<And> x. x \<in># mset_set \<V> \<Longrightarrow> (\<lambda>x . (0 :: real)) x \<noteq> 1" using zero_neq_one by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: real)) (mset_set \<V>)) 1 = 
    size (filter_mset (\<lambda> x . x \<in> (\<B>s ! j)) (mset_set \<V>))"
    using count_mset_split_image_filter [of "mset_set \<V>" "1" "(\<lambda> x . (0 :: real))" "\<lambda> x . x \<in> \<B>s ! j"] by simp
  then have "count (image_mset (\<lambda> x. if (x \<in> (\<B>s ! j)) then 1 else (0 :: real)) (mset_set \<V>)) 1 = card (\<B>s ! j)"
    using val_b block_size_alt by (simp add: finite_sets)
  thus ?thesis by (simp add: 1)
qed

lemma block_size_mat_rep_sum: 
  assumes "j < \<b>"
  shows "sum_vec (col N j) = card (\<B>s ! j)"
  using count_vec_sum_ones_alt block_size_mat_rep assms
  by (metis mat_col_elems) 

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
    by (simp add: scalar_prod_def points_list_length)
  also have "... = sum_vec (col N j)" using dim_row_is_v by (simp add: sum_vec_def)
  finally have "((u\<^sub>v \<v>) \<^sub>v* N) $ j = card (\<B>s ! j)" using block_size_mat_rep_sum assms by simp
  thus ?thesis by simp
qed

lemma transpose_N_mult_dim: "dim_row (N * N\<^sup>T) = \<v>" "dim_col (N * N\<^sup>T) = \<v>"
  by (simp_all add: points_list_length)
  
lemma inc_matrix_points: "(\<lambda> x. \<V>s ! x) ` (map_to_points inc_mat \<V>s \<B>s) = \<V>"
  apply (simp add: map_to_points_def)
  by (metis points_list_length lessThan_atLeast0 points_set_image)

lemma inc_matrix_col_block: 
  assumes "c \<in> set (cols N)"
  shows "(\<lambda> x. \<V>s ! x) ` (map_col_to_block c) \<in># \<B>"
proof -
  obtain j where "c = col N j" and "j < \<b>" using assms
    by (metis cols_length cols_nth in_mset_conv_nth ordered_incidence_system.dim_col_b_lt_iff 
        ordered_incidence_system_axioms set_mset_mset) 
  thus ?thesis
    using matrix_col_in_blocks by blast 
qed

lemma inc_mat_ordered_blocks_Bs: "map (\<lambda> x. ((!) \<V>s) ` x) (map_to_blocks_ordered inc_mat \<V>s \<B>s) = \<B>s"
proof (auto simp add: list_eq_iff_nth_eq)
  show lengtheq: "length (zero_one_matrix.map_to_blocks_ordered N) = length \<B>s"
    by (simp add: dim_col_length) 
  show "\<And>j i.
       j < length (zero_one_matrix.map_to_blocks_ordered N) \<Longrightarrow> i \<in> zero_one_matrix.map_to_blocks_ordered N ! j \<Longrightarrow> \<V>s ! i \<in> \<B>s ! j"
  proof -
    fix j i
    assume jlt: "j < length (zero_one_matrix.map_to_blocks_ordered N)"
    assume "i \<in> zero_one_matrix.map_to_blocks_ordered N ! j"
    then have "i \<in> map (\<lambda> c . map_col_to_block c) (cols N) ! j" by (simp add: map_to_blocks_ordered_def)
    then have "i \<in> map_col_to_block (cols N ! j)"
      by (metis jlt length_map map_to_blocks_ordered_def nth_map) 
    then have xain: "i \<in> map_col_to_block (col N j)" using jlt
      by (metis cols_length cols_nth length_map map_to_blocks_ordered_def) 
    then have "N $$ (i, j) = 1" using M_def_from_lists
      by (metis dim_col_length in_map_col_valid_index_M jlt map_blocks_ordered_nth map_points_ordered_nth) 
    then show "\<V>s ! i \<in> \<B>s ! j"
      by (metis lengtheq xain dim_col_length in_map_col_valid_index_M inc_mat_dim_row inc_matrix_point_in_block jlt) 
  qed
  show "\<And>i x. i < length (zero_one_matrix.map_to_blocks_ordered N) \<Longrightarrow>
           x \<in> \<B>s ! i \<Longrightarrow> x \<in> (!) \<V>s ` zero_one_matrix.map_to_blocks_ordered N ! i"
  proof -
    fix j x
    assume jl:"j < length (zero_one_matrix.map_to_blocks_ordered N)"
    then have jlt: "j < \<b>"
      using blocks_list_length lengtheq by metis
    assume "x \<in> \<B>s ! j"
    then have xin:  "x \<in> ((!) \<V>s) ` (map_col_to_block (col N j))" using matrix_col_to_block_v2 jlt by simp
    then have "(!) \<V>s ` (zero_one_matrix.map_to_blocks_ordered N ! j) = (!) \<V>s ` ((map (\<lambda> c . map_col_to_block c) (cols N)) !j)" 
      by (simp add: map_to_blocks_ordered_def)
    also have "... = (!) \<V>s ` ( map_col_to_block (cols N ! j))" 
      by (metis jl length_map map_to_blocks_ordered_def nth_map) 
    finally have "(!) \<V>s ` (zero_one_matrix.map_to_blocks_ordered N ! j) = (!) \<V>s ` (map_col_to_block (col N j))" using jl
      by (metis cols_length cols_nth length_map map_to_blocks_ordered_def) 
    then show "x \<in> (!) \<V>s ` zero_one_matrix.map_to_blocks_ordered N ! j"
      by (simp add: xin) 
  qed
qed

lemma inc_matrix_blocks: "image_mset (\<lambda> bl. ((!) \<V>s) ` bl) (map_to_blocks inc_mat \<V>s \<B>s) = \<B>"
proof -
  have "image_mset (\<lambda> bl. ((!) \<V>s) ` bl) (map_to_blocks inc_mat \<V>s \<B>s) = mset (map (\<lambda> x. ((!) \<V>s) ` x) (map_to_blocks_ordered inc_mat \<V>s \<B>s)) "
    by (simp add: map_to_blocks_ordered_set)
  also have "... = mset (\<B>s)"using inc_mat_ordered_blocks_Bs by simp
  finally have "image_mset (\<lambda> bl. ((!) \<V>s) ` bl) (map_to_blocks inc_mat \<V>s \<B>s) = \<B>"
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
    by (simp add: ordered_comp.points_list_length)
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

(* Lemma exists incidence matrix *)

definition is_incidence_matrix :: "real mat \<Rightarrow> 'a set \<Rightarrow> 'a set multiset \<Rightarrow> bool" where
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
end

locale ordered_proper_design = ordered_design \<V>s \<B>s + proper_design "set \<V>s" "mset \<B>s" 
  for \<V>s and \<B>s

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
    by (simp add: points_list_length dim_col_is_b) 
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
    by (simp add: points_list_length dim_col_is_b)
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

locale regular_t_wise_balance = t_wise_balance + constant_rep_design
begin

lemma reg_index_lt_rep: 
  shows "\<Lambda>\<^sub>t \<le> \<r>"
proof -
  obtain ps where psin: "ps \<subseteq> \<V>" and pst: "card ps = \<t>"
    by (metis obtain_t_subset_points) 
  then have ne: "ps \<noteq> {}" using t_non_zero by auto
  then have "\<B> index ps = \<Lambda>\<^sub>t" using balanced pst psin by simp
  thus ?thesis using index_lt_const_rep
    using ne psin by auto 
qed

end

locale regular_pairwise_balance = regular_t_wise_balance \<V> \<B> 2 \<Lambda> \<r> + pairwise_balance \<V> \<B> \<Lambda>
  for \<V> and \<B> and \<Lambda> and \<r>
begin 

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
  assume ilt: "i < dim_row (real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)" 
    and jlt: "j < dim_col (real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
  then have "(real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = 
    (real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) + (real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j)" 
    by simp
  then have split: "(real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = 
    (real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) + (\<r> - \<Lambda>) * ((1\<^sub>m \<v>) $$ (i, j))"
    using ilt jlt by simp
  have lhs: "(real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v>) $$(i, j) = \<Lambda>" using ilt jlt by simp
  show "(N * N\<^sup>T) $$ (i, j) = (real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j)"
  proof (cases "i = j")
    case True
    then have rhs: "(real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = (\<r> - \<Lambda>)" using ilt by fastforce 
    have "(real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = \<Lambda> + (\<r> - \<Lambda>)"
      using True jlt by auto
    then have "(real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>) $$ (i, j) = \<r>" 
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
  show "dim_row (N * N\<^sup>T) = dim_row (real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
    using transpose_N_mult_dim(1) by auto
next
  show "dim_col (N * N\<^sup>T) = dim_col (real \<Lambda> \<cdot>\<^sub>m J\<^sub>m \<v> + real (\<r> - \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m \<v>)"
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

locale ordered_const_intersect_design = ordered_proper_design \<V>s \<B>s + const_intersect_design "set \<V>s" "mset \<B>s" m
  for \<V>s \<B>s m

context zero_one_matrix
begin

sublocale ordered_incidence_sys: ordered_incidence_system map_to_points_ordered map_to_blocks_ordered
  by (unfold_locales) (simp_all add: map_to_blocks_ordered_set map_to_points_ordered_set 
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
  obtain i where "x = (map_to_points_ordered ! i)" and "i < dim_row M"
    using assms(2) ordered_incidence_sys.valid_points_index_cons local.map_to_points_card map_to_points_ordered_set by auto 
  then have eq: "map_to_blocks rep x = sum_vec (row M i)" using ordered_incidence_sys.point_rep_mat_row_sum
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
  obtain x1 x2 where "x1 \<in> map_to_points" and "x2 \<in> map_to_points" and "ps = {x1, x2}"
    using assms(2) assms(3) by (metis card_2_iff insert_subset) 
  then have neqx: "x1 \<noteq> x2" using assms(3)
    by fastforce
  then obtain i1 i2 where "map_to_points_ordered ! i1 = x1" and "map_to_points_ordered ! i2 = x2" and "i1 < dim_row M" and "i2 < dim_row M"
    by (metis \<open>x1 \<in> local.map_to_points\<close> \<open>x2 \<in> local.map_to_points\<close> local.map_to_points_card 
        local.map_to_points_ordered_set ordered_incidence_sys.valid_points_index_cons)
  then have neqi: "i1 \<noteq> i2" using neqx
    by blast 
  have cond: "\<And> j i. j \<noteq> i \<Longrightarrow> i < dim_row (M * (M\<^sup>T)) \<Longrightarrow> j < dim_row (M * (M\<^sup>T)) \<Longrightarrow> (M * (M\<^sup>T)) $$ (i, j) = \<Lambda>"
    using assms(1) by simp
  then have "map_to_blocks index ps = card {j \<in> {0..<dim_col M} . M $$(i1, j) = 1 \<and> M $$ (i2, j) = 1}"
    using ordered_incidence_sys.incidence_mat_two_index \<open>Vs ! i1 = x1\<close> \<open>Vs ! i2 = x2\<close> \<open>i1 < dim_row M\<close> 
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
  interpret pdes: ordered_design "map_to_points_ordered" "map_to_blocks_ordered"
    using assms(2) mat_is_design assms(3)
    by (simp add: local.map_to_blocks_ordered_set local.map_to_points_ordered_set ordered_design_def ordered_incidence_sys.ordered_incidence_system_axioms)  
  show ?thesis proof (unfold_locales, simp_all)
    show "Bs \<noteq> []"
      using assms(2) local.rev_map_points_blocks ordered_incidence_sys.dim_col_is_b by auto 
    show "2 \<le> ordered_incidence_sys.\<v>" using assms
      by (simp add: local.map_to_points_card local.map_to_points_ordered_set) 
    show "\<And>ps. ps \<subseteq> ordered_incidence_sys.\<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> ordered_incidence_sys.\<B> index ps = \<Lambda>"
      using assms  trans_cond_implies_map_index
      by (simp add: local.map_to_blocks_ordered_set local.map_to_points_ordered_set) 
    show "\<And>x. x \<in> ordered_incidence_sys.\<V> \<Longrightarrow> ordered_incidence_sys.\<B> rep x = r" 
      using assms trans_cond_implies_map_rep_num by (simp add: local.map_to_blocks_ordered_set local.map_to_points_ordered_set) 
  qed
qed

lemma col_ones_sum_eq_block_size: 
  assumes "j < dim_col M"
  shows "card (map_col_to_block (col M j)) = sum_vec (col M j)"
  using assms zero_one_matrix.map_blocks_ordered_nth ordered_incidence_sys.block_size_mat_rep_sum local.zero_one_matrix_axioms local.map_to_blocks_size local.rev_map_points_blocks
  by (metis local.dim_col_length ordered_incidence_sys.blocks_list_length)

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
  interpret ipbd: ordered_regular_pairwise_balance map_to_points_ordered map_to_blocks_ordered \<Lambda> r
    using rpbd_exists assms by simp
  show ?thesis proof (unfold_locales, simp_all add: assms)
    show "\<And>bl. bl \<in> set Bs \<Longrightarrow> card bl = k"
      using vec_k_impl_uniform_block_size assms
      by (metis local.map_to_blocks_ordered_set set_mset_mset) 
    show "k < ordered_incidence_sys.\<v>"
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
(* bij_betw_nth  bij_betw_index *)

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

(* 
lemma ones_incidence_mat_block_size: 
  assumes "j < \<b>"
  shows "((u\<^sub>v \<v>) \<^sub>v* N) $ j = card (\<B>s ! j)
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
*)

(* Reasoning on incidence matrices outside of locale context *)



(*

I need something on equivalence of incidence matrices (isomorphic elems etc)
(* Theorem 1.15 *)
lemma incidence_sys_exists_iff_matrix: 
  assumes "incidence_matrix M"
  assumes "dim_row M = v"
  assumes "dim_col M = b"
  shows "ordered_regular_pairwise_balance V B Vs Bs \<Lambda> r \<and> is_incidence_matrix M Vs Bs  \<longleftrightarrow> M * (M\<^sup>T) = \<Lambda> \<cdot>\<^sub>m (J\<^sub>m v) + (r - \<Lambda>) \<cdot>\<^sub>m (1\<^sub>m v)"
proof (intro iffI conjI)
  show " ordered_regular_pairwise_balance V B Vs Bs \<Lambda> r \<and> is_incidence_matrix M Vs Bs \<Longrightarrow> M * M\<^sup>T = int \<Lambda> \<cdot>\<^sub>m J\<^sub>m v + (int r - int \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m v"
  proof -
    assume a: "ordered_regular_pairwise_balance V B Vs Bs \<Lambda> r \<and> is_incidence_matrix M Vs Bs"
    then have a1: "ordered_regular_pairwise_balance V B Vs Bs \<Lambda> r" by (rule conjunct1)
    have a2: "is_incidence_matrix M Vs Bs" using a by (rule conjunct2)
    interpret rpb: ordered_regular_pairwise_balance V B Vs Bs \<Lambda> r using a1 by simp
    have "rpb.N = M"
      by (metis a2 is_incidence_matrix_def) 
    then show "M * M\<^sup>T = int \<Lambda> \<cdot>\<^sub>m J\<^sub>m v + (int r - int \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m v"
      using rpb.rpbd_incidence_matrix_cond assms
      by (metis of_nat_diff rpb.dim_row_is_v rpb.reg_index_lt_rep) 
  qed
  show "M * M\<^sup>T = int \<Lambda> \<cdot>\<^sub>m J\<^sub>m v + (int r - int \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m v \<Longrightarrow> ordered_regular_pairwise_balance V B Vs Bs \<Lambda> r"
    sorry
  show "M * M\<^sup>T = int \<Lambda> \<cdot>\<^sub>m J\<^sub>m v + (int r - int \<Lambda>) \<cdot>\<^sub>m 1\<^sub>m v \<Longrightarrow> is_incidence_matrix M Vs Bs "

*)
end