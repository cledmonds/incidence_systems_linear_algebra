theory Dual_Systems imports Incidence_Matrices
begin

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

definition dual_blocks :: "'a set \<Rightarrow> 'a set list \<Rightarrow> nat set multiset" where
"dual_blocks \<V> \<B>s \<equiv> {# {y . y < length \<B>s \<and> x \<in> \<B>s ! y} . x \<in># (mset_set \<V>)#}"

lemma dual_blocks_wf: "b \<in># dual_blocks V Bs \<Longrightarrow> b \<subseteq> {0..<length Bs}"
  by (auto simp add: dual_blocks_def)

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

context incidence_system
begin

lemma point_in_block_rep_min_iff:
  assumes "x \<in> \<V>" 
  shows "\<exists> bl . bl \<in># \<B> \<and> x \<in> bl \<longleftrightarrow> (\<B> rep x > 0)"
  using rep_number_g0_exists
  by (metis block_complement_elem_iff block_complement_inv wellformed)

end


context ordered_incidence_system
begin

definition dual_blocks_ordered :: "nat set list" ("\<B>s*") where
"dual_blocks_ordered \<equiv> map (\<lambda> x . {y . y < length \<B>s \<and> x \<in> \<B>s ! y}) \<V>s"

lemma dual_blocks_ordered_eq: "dual_blocks \<V> \<B>s= mset (\<B>s*)"
  by (auto simp add: distinct dual_blocks_def dual_blocks_ordered_def mset_set_set)

lemma dual_blocks_len: "length \<B>s* = length \<V>s"
  by (simp add: dual_blocks_ordered_def)

sublocale dual_sys: finite_incidence_system "{0..<length \<B>s}" "dual_blocks \<V> \<B>s"
  using dual_blocks_wf by(unfold_locales) (auto)

lemma dual_is_ordered_inc_sys:  "ordered_incidence_system [0..<length \<B>s] \<B>s*"
  by (metis atLeastLessThan_upt distinct_upt dual_blocks_ordered_eq dual_sys.incidence_system_axioms inc_sys_orderedI)

interpretation ordered_dual_sys: ordered_incidence_system "[0..<length \<B>s]" "\<B>s*"
  using dual_is_ordered_inc_sys by simp 

lemma ord_dual_blocks_b: "ordered_dual_sys.\<b> = \<v>"
  using dual_blocks_len by (simp add: points_list_length) 

lemma dual_blocks_b: "dual_sys.\<b> = \<v>"
  using points_list_length
  by (simp add: dual_blocks_len dual_blocks_ordered_eq) 

lemma dual_blocks_v: "dual_sys.\<v> = \<b>"
  by fastforce

lemma ord_dual_blocks_v: "ordered_dual_sys.\<v> = \<b>"
  by fastforce

lemma dual_point_block: "i < \<v> \<Longrightarrow> \<B>s* ! i = {y. y < length \<B>s \<and> (\<V>s ! i) \<in> \<B>s ! y}"
  by (simp add: dual_blocks_ordered_def points_list_length)

lemma dual_incidence_iff: 
  assumes "i < \<v>" and "j < \<b>" and  "\<B>s ! j = bl" and "\<V>s ! i = x"
  shows "(x \<in> bl \<longleftrightarrow> j \<in> \<B>s* ! i)"
proof (intro iffI)
  show "x \<in> bl \<Longrightarrow> j \<in> \<B>s* ! i" using dual_point_block assms by simp
  show "j \<in> \<B>s* ! i \<Longrightarrow> x \<in> bl" using dual_point_block assms by simp
qed

lemma dual_incidence_iff2: 
  assumes "i < \<v>" and "j < \<b>"
  shows "(\<V>s ! i \<in> \<B>s ! j  \<longleftrightarrow> j \<in> \<B>s* ! i)"
  using dual_incidence_iff assms by auto

lemma N_trans_index_val: "i < dim_col N \<Longrightarrow> j < dim_row N \<Longrightarrow> N\<^sup>T $$ (i, j) = (if (\<V>s ! j) \<in> (\<B>s ! i) then 1 else 0)"
  by (simp add: inc_mat_of_def)

lemma dual_incidence_mat_eq_trans: "ordered_dual_sys.N = N\<^sup>T"
proof (intro eq_matI)
  show dimr: "dim_row ordered_dual_sys.N = dim_row N\<^sup>T" using dual_blocks_v
    by (simp add: dim_col_is_b ordered_dual_sys.dim_row_is_v) 
  show dimc: "dim_col ordered_dual_sys.N = dim_col N\<^sup>T" using ord_dual_blocks_b 
    by (simp add: points_list_length ordered_dual_sys.dim_col_is_b)
  show "\<And>i j. i < dim_row N\<^sup>T \<Longrightarrow> j < dim_col N\<^sup>T \<Longrightarrow> ordered_dual_sys.N $$ (i, j) = N\<^sup>T $$ (i, j)" 
  proof -
    fix i j assume ilt: "i < dim_row N\<^sup>T" assume jlt: "j < dim_col N\<^sup>T"
    then have ilt2: "i < length \<B>s"using dimr
      using blocks_list_length ord_dual_blocks_v ilt ordered_dual_sys.dim_row_is_v by linarith
    then have ilt3: "i < \<b>" by simp
    have jlt2: "j < \<v>" using jlt
      using dim_row_is_v by fastforce 
    have "ordered_dual_sys.N $$ (i, j) =  (if ([0..<length \<B>s] ! i) \<in> (\<B>s* ! j) then 1 else 0)"
      by (metis dimr dual_blocks_len ilt inc_mat_dim_row inc_matrix_elems_one_zero inc_matrix_point_in_block_iff index_transpose_mat(3) jlt)
    then have "ordered_dual_sys.N $$ (i, j) = (if \<V>s ! j \<in> \<B>s ! i then 1 else 0)" using ilt3 jlt2 dual_incidence_iff2 by simp 
    thus "ordered_dual_sys.N $$ (i, j) = N\<^sup>T $$ (i, j)" using ilt3 jlt2 dim_row_is_v dim_col_is_b N_trans_index_val by simp
  qed
qed

lemma dual_blocks_point_exists: "bl \<in># dual_blocks \<V> \<B>s \<Longrightarrow> \<exists> x. x \<in> \<V> \<and> bl = {y . y < length \<B>s \<and> x \<in> \<B>s ! y}"
  by (auto simp add: dual_blocks_def)

lemma dual_blocks_nempty:
  assumes "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x > 0)"
  assumes "bl \<in># dual_blocks \<V> \<B>s"
  shows "bl \<noteq> {}"
proof -
  have "bl \<in># {# {y . y < length \<B>s \<and> x \<in> \<B>s ! y} . x \<in># (mset_set \<V>)#}" using assms dual_blocks_def
    by metis 
  then obtain x where xin: "x \<in># (mset_set \<V>)" and blval: "bl = {y . y < length \<B>s \<and> x \<in> \<B>s ! y}"
    by blast 
  then have "x \<in> \<V>"
    by auto 
  then obtain bl' where "bl' \<in># \<B>" and "x \<in> bl'" using assms(1)
    using point_in_block_rep_min_iff by auto 
  then obtain y where "y < length \<B>s" and "\<B>s ! y = bl'"
    using valid_blocks_index_cons by auto 
  then have "y \<in> bl"
    by (simp add: \<open>x \<in> bl'\<close> blval) 
  thus ?thesis
    by blast
qed

lemma dual_blocks_size_is_rep: 
  assumes "j < length \<B>s*"
  shows "card (\<B>s* ! j) = \<B> rep (\<V>s ! j)"
proof -
  have 1: "card (\<B>s* ! j) = card {y . y < length \<B>s \<and> (\<V>s ! j) \<in> \<B>s ! y}"
    using assms dual_blocks_len dual_point_block points_list_length by force
  also have 2: "... = card {y \<in> {0..<length \<B>s} . (\<V>s ! j) \<in> \<B>s ! y}" by simp
  also have "... = size (mset_set {y \<in> {0..<length \<B>s} . (\<V>s ! j) \<in> \<B>s ! y})" by simp
  also have "... = size {# y \<in># mset_set {0..< length \<B>s} . (\<V>s ! j) \<in> \<B>s ! y #}" using filter_mset_mset_set
    by simp 
  finally have "card (\<B>s* ! j) = size {# bl \<in># \<B> . (\<V>s ! j) \<in> bl #}"
    by (metis 1 2 filter_size_blocks_eq_card_indexes lessThan_atLeast0 size_mset) 
  thus ?thesis by (simp add: point_replication_number_def)
qed

lemma dual_blocks_size_is_rep_obtain: 
  assumes "bl \<in># dual_blocks \<V> \<B>s"
  obtains x where "x \<in> \<V>" and "card bl = \<B> rep x"
proof -
  obtain j where jlt1: "j < length \<B>s*" and bleq: "\<B>s* ! j = bl"
    by (metis assms dual_blocks_ordered_eq in_mset_conv_nth) 
  then have jlt: "j < \<v>"
    by (simp add: dual_blocks_len points_list_length) 
  let ?x = "\<V>s ! j"
  have xin: "?x \<in> \<V>" using jlt
    by (simp add: valid_points_index) 
  have "card bl = \<B> rep ?x" using dual_blocks_size_is_rep jlt1 bleq by auto
  thus ?thesis using xin that by auto 
qed

lemma dual_blocks_rep_is_size:
  assumes "i \<in> {0..<length \<B>s}"
  shows "(mset \<B>s*) rep i = card (\<B>s ! i)"
proof -
  have "(mset \<B>s*) rep i = size {# bl \<in># (mset \<B>s*) . i \<in> bl #}" 
    by (simp add: point_replication_number_def)
  also have 1: "... = size {# bl \<in># {# {y . y < length \<B>s \<and> x \<in> \<B>s ! y} . x \<in># (mset_set \<V>)#} . i \<in> bl #}" 
    using dual_blocks_ordered_eq dual_blocks_def by metis 
  also have "... = size (filter_mset (\<lambda> bl . i \<in> bl) (image_mset (\<lambda> x . {y . y < length \<B>s \<and> x \<in> \<B>s ! y}) (mset_set \<V>)))" by simp
  finally have "(mset \<B>s*) rep i = size (image_mset (\<lambda> x . {y . y < length \<B>s \<and> x \<in> \<B>s ! y}) (filter_mset (\<lambda> bl . i \<in> {y . y < length \<B>s \<and> bl \<in> \<B>s ! y}) (mset_set \<V>)))"
    using filter_mset_image_mset by (metis 1 ordered_dual_sys.point_rep_number_alt_def) 
  then have "(mset \<B>s*) rep i = size (filter_mset (\<lambda> bl . i \<in> {y . y < length \<B>s \<and> bl \<in> \<B>s ! y}) (mset_set \<V>))"
    by fastforce
  then have "(mset \<B>s*) rep i = size (filter_mset (\<lambda> bl . bl \<in> \<B>s ! i) (mset_set \<V>))" using assms by simp
  then have "(mset \<B>s*) rep i =  card {x \<in> \<V> . x \<in> (\<B>s ! i)}" by simp
  thus ?thesis using assms block_size_alt by auto
qed

lemma dual_blocks_ne_index_ne: 
  assumes "j1 < length \<B>s*" "j2 < length \<B>s*"
  shows "\<B>s* ! j1 \<noteq> \<B>s* ! j2 \<Longrightarrow> j1 \<noteq> j2"
  by auto

lemma dual_blocks_elem_iff:
  assumes "j < \<v>"
  shows "x \<in> (\<B>s* ! j) \<longleftrightarrow> \<V>s ! j \<in> \<B>s ! x \<and> x < \<b>"
  apply (auto simp add: dual_blocks_ordered_def)
      using assms dual_blocks_ordered_def ordered_incidence_system.dual_point_block ordered_incidence_system_axioms apply fastforce
    using assms dual_blocks_ordered_def dual_point_block apply fastforce
  by (metis (full_types) assms blocks_list_length dual_blocks_ordered_def dual_incidence_iff)

lemma dual_blocks_inter_index: 
  assumes "j1 < length \<B>s*" "j2 < length \<B>s*"
  shows "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = points_index \<B> {\<V>s ! j1, \<V>s ! j2}"
proof -
  have fin: "finite {0..<length \<B>s}"
    by auto 
  have j1lt: "j1 < \<v>" using assms
    using dual_blocks_len points_list_length by auto 
  have j2lt: "j2 < \<v>" using assms dual_blocks_len points_list_length by auto
  have iff: "\<And> x. (x \<in>(\<B>s* ! j1) \<and> x \<in> (\<B>s* ! j2)) \<longleftrightarrow> (\<V>s ! j1 \<in> \<B>s ! x \<and> x < \<b> \<and> \<V>s ! j2 \<in> \<B>s ! x)" 
    by (auto simp add: dual_blocks_elem_iff j1lt j2lt)
  have pi: "points_index \<B> {\<V>s ! j1, \<V>s ! j2} = size {# bl \<in># \<B> . \<V>s !j1 \<in> bl \<and> \<V>s ! j2 \<in> bl#}" 
    by (auto simp add: points_index_def)
  have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = card ({x . x <length \<B>s \<and> x \<in> (\<B>s* ! j1) \<and> x \<in> (\<B>s* ! j2)})"
    apply (auto simp add: intersection_number_def)
    by (smt (verit) Collect_cong Int_Collect blocks_list_length dual_blocks_elem_iff inf.idem inf_set_def j2lt mem_Collect_eq)
  then have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = card ({x . x <length \<B>s \<and> \<V>s ! j1 \<in> \<B>s ! x \<and> \<V>s ! j2 \<in> \<B>s ! x})" using iff
    size_mset by (smt (verit, best) Collect_cong) 
  then have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = size (mset_set {x \<in> {0..<length \<B>s}. \<V>s ! j1 \<in> \<B>s ! x \<and> \<V>s ! j2 \<in> \<B>s ! x})" by simp
  then have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = size ({#x \<in># mset_set {0..<length \<B>s}. \<V>s ! j1 \<in> \<B>s ! x \<and> \<V>s ! j2 \<in> \<B>s ! x#})" using fin by simp
  then have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = size (filter_mset (\<lambda> x . \<V>s ! j1 \<in> \<B>s ! x \<and> \<V>s ! j2 \<in> \<B>s ! x) (mset_set {0..<length \<B>s}))" by simp
  then have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = size (image_mset (\<lambda> i. \<B>s ! i) (filter_mset (\<lambda> x . \<V>s ! j1 \<in> \<B>s ! x \<and> \<V>s ! j2 \<in> \<B>s ! x) (mset_set {0..<length \<B>s})))"
    by simp
  then have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = size (filter_mset (\<lambda> x . \<V>s ! j1 \<in> x \<and> \<V>s ! j2 \<in> x) (image_mset (\<lambda> i. \<B>s ! i) (mset_set {0..<length \<B>s})))"
    by (simp add: filter_mset_image_mset)
  then have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = size {# bl \<in># \<B> . \<V>s !j1 \<in> bl \<and> \<V>s ! j2 \<in> bl#}"
    by (metis blocks_list_length blocks_mset_image lessThan_atLeast0) 
  thus ?thesis using pi by simp
qed

lemma dual_blocks_list_index_img: "image_mset (\<lambda>x . \<B>s* ! x) (mset_set {0..<length \<B>s*}) = mset \<B>s*"
  using lessThan_atLeast0 ordered_dual_sys.blocks_list_length ordered_dual_sys.blocks_mset_image by presburger

lemma points_img_index_rep: "\<V> = image (\<lambda> j. \<V>s ! j) {0..<length \<V>s}"
  using lessThan_atLeast0 points_list_length points_set_image by presburger

lemma dual_blocks_points_index_inter: 
  assumes "i1 < \<b>" "i2 < \<b>"
  assumes "i1 \<noteq> i2"
  shows "(mset \<B>s*) index {i1, i2} = (\<B>s ! i1) |\<inter>| (\<B>s ! i2)"
proof - 
  have "\<And> j . j \<in># mset_set {0..<length \<B>s*} \<Longrightarrow> j < \<v>"
    by (metis atLeastLessThan_iff atLeastLessThan_upt dual_blocks_len mset_upt points_list_length set_mset_mset) 
  then have iff: "\<And> j i. j \<in># mset_set {0..<length \<B>s*} \<Longrightarrow> i < \<b> \<Longrightarrow> i \<in> (\<B>s* ! j) \<longleftrightarrow> (\<V>s ! j) \<in> (\<B>s ! i)" 
    using assms dual_incidence_iff2 by simp 
  then have iff2: "\<And> j . j \<in># mset_set {0..<length \<B>s*} \<Longrightarrow> i1 \<in> (\<B>s* ! j) \<and> i2 \<in> (\<B>s* ! j) \<longleftrightarrow> (\<V>s ! j) \<in> (\<B>s ! i1) \<and> (\<V>s ! j) \<in> (\<B>s ! i2)"
    using assms by auto
  have ss2: "(\<B>s ! i2) \<subseteq> \<V>" using wellformed assms by auto
  then have ss: "{x . x \<in> (\<B>s ! i1) \<and> x \<in> (\<B>s ! i2)} \<subseteq> \<V>"
    by auto 
  then have inter:  "(\<B>s ! i1) |\<inter>| (\<B>s ! i2) = card {x \<in> \<V>. x \<in> (\<B>s ! i1) \<and> x \<in> (\<B>s ! i2)}"
    using intersection_number_def by (metis Collect_conj_eq Collect_mem_eq Int_absorb1)
  have inj: "inj_on (\<lambda> j. \<V>s ! j) {j \<in> {0..<length \<V>s} . (\<V>s ! j) \<in> (\<B>s ! i1) \<and> (\<V>s ! j) \<in> (\<B>s ! i2)}"
    by (simp add: inj_on_nth distinct) 
  have init: "(mset \<B>s*) index {i1, i2} = size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#}"
    by (simp add: points_index_def)
  then have "size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#} = size {#j \<in># mset_set {0..<length \<B>s*} . i1 \<in> (\<B>s* ! j) \<and> i2 \<in> (\<B>s* ! j)#}"
  proof - 
    have "size {#j \<in># mset_set {0..<length \<B>s*} . i1 \<in> (\<B>s* ! j) \<and> i2 \<in> (\<B>s* ! j)#} 
      = size (filter_mset (\<lambda> j. i1 \<in> (\<B>s* ! j) \<and> i2 \<in> (\<B>s* ! j)) (mset_set {0..<length \<B>s*})) " by simp
    also have s1: "... = size (image_mset (\<lambda>x . \<B>s* ! x) (filter_mset (\<lambda> j. i1 \<in> (\<B>s* ! j) \<and> i2 \<in> (\<B>s* ! j)) (mset_set {0..<length \<B>s*})))" by fastforce
    also have s2: "... = size (filter_mset (\<lambda> j. i1 \<in> j \<and> i2 \<in> j) (image_mset (\<lambda>x . \<B>s* ! x) (mset_set {0..<length \<B>s*})))"
      by (simp add: filter_mset_image_mset) 
    finally have "size {#j \<in># mset_set {0..<length \<B>s*} . i1 \<in> (\<B>s* ! j) \<and> i2 \<in> (\<B>s* ! j)#} = size (filter_mset (\<lambda> j. i1 \<in> j \<and> i2 \<in> j) (mset \<B>s*))"
      using dual_blocks_list_index_img s2 s1 by presburger 
    thus ?thesis by simp
  qed
  then have "size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#} = size {#j \<in># mset_set {0..<length \<B>s*} . (\<V>s ! j) \<in> (\<B>s ! i1) \<and> (\<V>s ! j) \<in> (\<B>s ! i2)#}" using iff2
    by (smt (verit, ccfv_SIG) filter_mset_cong) 
  then have "size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#} = 
    card ({j \<in> {0..<length \<B>s*} . (\<V>s ! j) \<in> (\<B>s ! i1) \<and> (\<V>s ! j) \<in> (\<B>s ! i2)})" by simp
  then have "size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#} = 
    card ({j \<in> {0..<length \<V>s} . (\<V>s ! j) \<in> (\<B>s ! i1) \<and> (\<V>s ! j) \<in> (\<B>s ! i2)})" using dual_blocks_len by presburger 
  then have "size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#} = 
    card (image (\<lambda> j. \<V>s ! j) {j \<in> {0..<length \<V>s} . (\<V>s ! j) \<in> (\<B>s ! i1) \<and> (\<V>s ! j) \<in> (\<B>s ! i2)})"  
    using inj card_image[of "(\<lambda> j. \<V>s ! j)" "{j \<in> {0..<length \<V>s} . (\<V>s ! j) \<in> (\<B>s ! i1) \<and> (\<V>s ! j) \<in> (\<B>s ! i2)}"] by simp
  then have "size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#} = 
    card {j \<in> image (\<lambda> j. \<V>s ! j) {0..<length \<V>s}. j \<in> (\<B>s ! i1) \<and> j \<in> (\<B>s ! i2)}" 
    using Compr_image_eq[of "(\<lambda> j. \<V>s ! j)" "{0..<length \<V>s}" "(\<lambda> j . j \<in> (\<B>s ! i1) \<and> j \<in> (\<B>s ! i2))"] by simp
  then have "size {#bl \<in># (mset \<B>s*) . i1 \<in> bl \<and> i2 \<in> bl#} = 
    card {j \<in> \<V>. j \<in> (\<B>s ! i1) \<and> j \<in> (\<B>s ! i2)}" using points_img_index_rep by simp
  thus ?thesis using init inter by simp
qed
end

context ordered_design
begin

lemma dual_is_design: 
  assumes "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x > 0)" (* Required to ensure no blocks are empty *)
  shows "design {0..<length \<B>s} (dual_blocks \<V> \<B>s)"
  using dual_blocks_nempty assms by (unfold_locales) (simp) 
end

context ordered_proper_design
begin

lemma dual_sys_b_non_zero: "dual_sys.\<b> \<noteq> 0"
  using v_non_zero dual_blocks_b by auto

lemma dual_is_proper_design: 
  assumes "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x > 0)" (* Required to ensure no blocks are empty *)
  shows "proper_design {0..<length \<B>s} (dual_blocks \<V> \<B>s)"
  using dual_blocks_nempty dual_sys_b_non_zero assms by (unfold_locales) (simp_all)

end

context ordered_block_design 
begin

lemma dual_blocks_const_rep:
  assumes "i \<in> {0..<length \<B>s}"
  shows "(mset \<B>s*) rep i = \<k>"
  using dual_blocks_rep_is_size uniform
  by (metis assms atLeastLessThan_iff nth_mem_mset) 

lemma dual_blocks_constant_rep_design:
  assumes "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x > 0)"
  shows "constant_rep_design {0..<length \<B>s} (dual_blocks \<V> \<B>s) \<k>"
proof -
  interpret des: proper_design "{0..<length \<B>s}" "(dual_blocks \<V> \<B>s)"
    using dual_is_proper_design assms by simp
  show ?thesis using dual_blocks_const_rep dual_blocks_ordered_eq by (unfold_locales) (simp)
qed


end

context ordered_constant_rep
begin

lemma dual_blocks_const_size: 
  assumes "j < length \<B>s*"
  shows "card (\<B>s* ! j) = \<r>"
  using dual_blocks_rep_is_size assms dual_blocks_len dual_blocks_size_is_rep by fastforce 

lemma dual_is_block_design: "block_design {0..<length \<B>s} (dual_blocks \<V> \<B>s) \<r>"
proof -
  have "\<r> > 0" by (simp add: r_gzero)
  then have "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x > 0)" using rep_number by simp
  then interpret pdes: proper_design "{0..<length \<B>s}" "(dual_blocks \<V> \<B>s)" 
    using dual_is_proper_design by simp
  have "\<And> bl. bl \<in># dual_blocks \<V> \<B>s \<Longrightarrow> card bl = \<r>" 
    using dual_blocks_const_size 
    by (metis dual_blocks_ordered_eq in_set_conv_nth set_mset_mset)
  thus ?thesis by (unfold_locales) (simp)
qed

end

locale simple_const_intersect_design = const_intersect_design + simple_design

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

lemma count_complete_lt_balance: "count \<B> \<V> \<le> \<Lambda>"
proof (rule ccontr)
  assume a: "\<not> count \<B> \<V> \<le> \<Lambda>"
  then have assm: "count \<B> \<V> > \<Lambda>"
    by simp
  then have gt: "size {# bl \<in># \<B> . bl = \<V>#} > \<Lambda>"
    by (simp add: count_size_set_repr) 
  obtain ps where psss: "ps \<subseteq> \<V>" and pscard: "card ps = 2" using t_lt_order
    by (meson obtain_t_subset_points) 
  then have "{# bl \<in># \<B> . bl = \<V>#} \<subseteq># {# bl \<in># \<B> . ps \<subseteq> bl #}"
    by (metis a balanced le_refl points_index_count_min) 
  then have "size {# bl \<in># \<B> . bl = \<V>#} \<le> \<B> index ps " 
    using points_index_def[of \<B> ps] size_mset_mono by simp
  thus False using pscard psss balanced gt by auto
qed

end

context ordered_pairwise_balance 
begin

lemma dual_blocks_const_intersect: 
  assumes "j1 < length \<B>s*" "j2 < length \<B>s*"
  assumes "j1 \<noteq> j2"
  shows "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = \<Lambda>"
proof -
  have "\<V>s ! j1 \<noteq> \<V>s ! j2" using assms(3)
    using assms(1) assms(2) distinct dual_blocks_len nth_eq_iff_index_eq by auto 
  then have c: "card {\<V>s ! j1, \<V>s ! j2} = 2"
    using card_2_iff by blast 
  have ss: "{\<V>s ! j1, \<V>s ! j2} \<subseteq> \<V>" using assms points_list_length
    using dual_blocks_len by auto 
  have "(\<B>s* ! j1) |\<inter>| (\<B>s* ! j2) = points_index \<B> {\<V>s ! j1, \<V>s ! j2}"
    using dual_blocks_inter_index assms by simp
  thus ?thesis using ss c balanced
    by blast 
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

lemma dual_is_const_intersect_des: 
  assumes "\<Lambda> > 0"
  shows "const_intersect_design {0..<(length \<B>s)} (dual_blocks \<V> \<B>s) \<Lambda>"
proof -
  have "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x \<ge> \<Lambda>)" using const_index_lt_rep by simp
  then have "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x > 0)" using assms
    by (metis gr_zeroI le_zero_eq) 
  then interpret pd: proper_design "{0..<(length \<B>s)}" "(dual_blocks \<V> \<B>s)" 
    using dual_is_proper_design by (simp) 
  show ?thesis proof (unfold_locales)
    fix b1 b2
    assume b1in: "b1 \<in># dual_blocks \<V> \<B>s"
    assume b2in:  "b2 \<in># remove1_mset b1 (dual_blocks \<V> \<B>s)"
    obtain j1 where b1eq: "b1 = \<B>s* ! j1" and j1lt: "j1 < length \<B>s*" using b1in
      by (metis dual_blocks_ordered_eq in_set_conv_nth set_mset_mset) 
    obtain j2 where b2eq: "b2 = \<B>s* ! j2" and j2lt: "j2 < length \<B>s*" and "j1 \<noteq> j2" 
      using b2in index_remove1_mset_ne
      by (metis (mono_tags) b1eq dual_blocks_ordered_eq j1lt nth_mem set_mset_mset) 
    then show "b1 |\<inter>| b2 = \<Lambda>" 
      using dual_blocks_const_intersect b1eq b2eq j1lt j2lt by simp 
  qed
qed

lemma eq_index_rep_imp_complete: 
  assumes "\<Lambda> = \<B> rep x"
  assumes "x \<in> \<V>"
  assumes "bl \<in># \<B>"
  assumes "x \<in> bl"
  shows "card bl = \<v>"
proof -
  have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> card {x, y} = 2 \<and> {x, y} \<subseteq> \<V>" using assms by simp
  then have size_eq: "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> size {# b \<in># \<B> . {x, y} \<subseteq> b#} = size {# b \<in># \<B> . x \<in> b#}"
    using point_replication_number_def balanced points_index_def assms
    by metis 
  have "\<And> y b. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> b \<in># \<B> \<Longrightarrow> {x, y} \<subseteq> b \<longrightarrow> x \<in> b" by simp
  then have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> {# b \<in># \<B> . {x, y} \<subseteq> b#} \<subseteq># {# b \<in># \<B> . x \<in> b#}" 
    using multiset_filter_mono2 assms by auto
  then have eq_sets: "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> {# b \<in># \<B> . {x, y} \<subseteq> b#} = {# b \<in># \<B> . x \<in> b#}" using size_eq
    by (smt (z3) Diff_eq_empty_iff_mset cancel_comm_monoid_add_class.diff_cancel size_Diff_submset size_empty size_eq_0_iff_empty subset_mset.antisym) 
  have "bl \<in># {# b \<in># \<B> . x \<in> b#}" using assms by simp
  then have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<noteq> x \<Longrightarrow> {x, y} \<subseteq> bl" using eq_sets
    by (metis (no_types, lifting) Multiset.set_mset_filter mem_Collect_eq) 
  then have "\<And> y. y \<in> \<V> \<Longrightarrow> y \<in> bl" using assms by blast 
  then have "bl = \<V>" using wellformed assms(3) by blast 
  thus ?thesis by simp
qed

lemma incomplete_index_strict_lt_rep:
  assumes "\<And> bl. bl \<in># \<B> \<Longrightarrow> incomplete_block bl" 
  assumes "x \<in> \<V>"
  assumes "\<Lambda> > 0"
  shows "\<Lambda> < \<B> rep x"
proof (rule ccontr)
  assume "\<not> (\<Lambda> < \<B> rep x)"
  then have a: "\<Lambda> \<ge> \<B> rep x"
    by simp
  then have "\<Lambda> = \<B> rep x" using const_index_lt_rep
    using assms(2) le_antisym by blast 
  then obtain bl where xin: "x \<in> bl" and blin: "bl \<in># \<B>"
    by (metis assms(3) rep_number_g0_exists) 
  thus False using assms eq_index_rep_imp_complete incomplete_alt_size
    using \<open>\<Lambda> = \<B> rep x\<close> nat_less_le by blast  
qed

lemma dual_is_simp_const_inter_des: 
  assumes "\<Lambda> > 0"
  assumes "\<And> bl. bl \<in># \<B> \<Longrightarrow> incomplete_block bl"  
  shows "simple_const_intersect_design {0..<(length \<B>s)} (dual_blocks \<V> \<B>s) \<Lambda>"
proof -
  interpret d: const_intersect_design "{0..<(length \<B>s)}" "(dual_blocks \<V> \<B>s)"  "\<Lambda>"
    using assms dual_is_const_intersect_des by simp
(* Show that m < block size for all blocks *)
  have "\<And> x. x \<in> \<V> \<Longrightarrow> \<Lambda> < \<B> rep x" using assms incomplete_index_strict_lt_rep
    by blast 
  then have "\<And> bl. bl \<in># (dual_blocks \<V> \<B>s) \<Longrightarrow> \<Lambda> < card bl"
    by (metis dual_blocks_size_is_rep_obtain) 
  then interpret s: simple_design "{0..<(length \<B>s)}" "(dual_blocks \<V> \<B>s)" 
    using d.simple_const_inter_block_size by simp
  show ?thesis by (unfold_locales)
qed
end

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


locale ordered_const_intersect_design = ordered_proper_design \<V>s \<B>s + const_intersect_design "set \<V>s" "mset \<B>s" \<m>
  for \<V>s \<B>s \<m>
begin 

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

lemma dual_is_balanced: 
  assumes "ps \<subseteq> {0..<length \<B>s}"
  assumes "card ps = 2"
  shows "(dual_blocks \<V> \<B>s) index ps = \<m>"
proof -
  obtain i1 i2 where psin: "ps = {i1, i2}" and neq: "i1 \<noteq> i2" using assms
    by (meson card_2_iff) 
  then have lt: "i1 < \<b>" using assms 
    by (metis atLeastLessThan_iff blocks_list_length insert_subset) 
  have lt2: "i2 < \<b>" using assms psin
    by (metis atLeastLessThan_iff blocks_list_length insert_subset) 
  then have inter: "(dual_blocks \<V> \<B>s) index ps = (\<B>s ! i1) |\<inter>| (\<B>s ! i2)" using dual_blocks_points_index_inter neq lt
    using dual_blocks_ordered_eq psin by presburger
  have inb1: "(\<B>s ! i1) \<in># \<B>"
    using lt by auto 
  have inb2: "(\<B>s ! i2) \<in># (\<B> - {#(\<B>s ! i1)#})" using lt2 neq blocks_index_ne_belong
    by (metis blocks_list_length lt) 
  thus ?thesis using const_intersect inb1 inb2 inter by blast 
qed

lemma dual_is_pbd: 
  assumes "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x > 0)"
  assumes "\<b> \<ge> 2"
  shows "pairwise_balance {0..<(length \<B>s)} (dual_blocks \<V> \<B>s) \<m>"
proof -
  interpret pd: proper_design "{0..<(length \<B>s)}" "(dual_blocks \<V> \<B>s)" 
    using dual_is_proper_design
    by (simp add: assms) 
  show ?thesis proof (unfold_locales)
    show "(1 ::nat) \<le> 2" by simp
    then show "2 \<le> dual_sys.\<v>" using  assms(2)
      by fastforce 
    show "\<And>ps. ps \<subseteq> {0..<length \<B>s} \<Longrightarrow> card ps = 2 \<Longrightarrow> dual_blocks \<V> \<B>s index ps = \<m>"
      using dual_is_balanced by simp
  qed
qed

end

(* Symmetric bibd intro rules *)
context bibd
begin
lemma symmetric_bibdIII: "\<r> = \<k> \<Longrightarrow> symmetric_bibd \<V> \<B> \<k> \<Lambda>"
  using necessary_condition_one symmetric_condition_1 by(unfold_locales) (simp)
end

lemma (in simple_design) block_mset_distinct: "distinct_mset \<B>" using simple
  by (simp add: distinct_mset_def) 

locale ordered_simple_des = ordered_design \<V>s \<B>s + simple_design "set \<V>s" "mset \<B>s" for \<V>s \<B>s
begin

lemma block_list_distinct: "distinct \<B>s"
  using block_mset_distinct by auto

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

locale ordered_sym_bibd = ordered_bibd \<V>s \<B>s \<k> \<Lambda> + symmetric_bibd "set \<V>s" "mset \<B>s" \<k> \<Lambda> 
  for \<V>s and \<B>s and \<k> and \<Lambda>


sublocale ordered_sym_bibd \<subseteq> ordered_simple_des
  by (unfold_locales)

context ordered_sym_bibd
begin


lemma dual_is_balanced: 
  assumes "ps \<subseteq> {0..<length \<B>s}"
  assumes "card ps = 2"
  shows "(dual_blocks \<V> \<B>s) index ps = \<Lambda>"
proof -
  obtain i1 i2 where psin: "ps = {i1, i2}" and neq: "i1 \<noteq> i2" using assms
    by (meson card_2_iff) 
  then have lt: "i1 < \<b>" using assms 
    by (metis atLeastLessThan_iff blocks_list_length insert_subset) 
  have lt2: "i2 < \<b>" using assms psin
    by (metis atLeastLessThan_iff blocks_list_length insert_subset) 
  then have inter: "(dual_blocks \<V> \<B>s) index ps = (\<B>s ! i1) |\<inter>| (\<B>s ! i2)" using dual_blocks_points_index_inter neq lt
    using dual_blocks_ordered_eq psin by presburger
  have inb1: "(\<B>s ! i1) \<in># \<B>"
    using lt by auto 
  have inb2: "(\<B>s ! i2) \<in># (\<B> - {#(\<B>s ! i1)#})" using lt2 neq blocks_index_simp_unique
    by (metis blocks_list_length in_remove1_mset_neq lt valid_blocks_index) 
  thus ?thesis using sym_block_intersections_index inb1 inter by blast
qed

lemma dual_bibd: "bibd {0..<(length \<B>s)} (dual_blocks \<V> \<B>s) \<r> \<Lambda>"
proof -
  interpret block: block_design "{0..<(length \<B>s)}" "(dual_blocks \<V> \<B>s)" \<r> 
    using dual_is_block_design by simp
  show ?thesis proof (unfold_locales)
    show "\<r> < dual_sys.\<v>"
      using dual_blocks_v incomplete symmetric_condition_1 symmetric_condition_2 by presburger 
    show "(1 ::nat) \<le> 2" by simp
    have "\<v> \<ge> 2"
      by (simp add: t_lt_order) 
    then have "\<b> \<ge> 2" using local.symmetric by auto 
    then show "2 \<le> dual_sys.\<v>" by simp
    show "\<And>ps. ps \<subseteq> {0..<length \<B>s} \<Longrightarrow> card ps = 2 \<Longrightarrow> dual_blocks \<V> \<B>s index ps = \<Lambda>"
      using dual_is_balanced by simp
    show "2 \<le> \<r>" using r_ge_two by blast 
  qed
qed

lemma dual_bibd_symmetric: "symmetric_bibd {0..<(length \<B>s)} (dual_blocks \<V> \<B>s) \<r> \<Lambda>"
proof -
  interpret bibd: bibd "{0..<(length \<B>s)}" "(dual_blocks \<V> \<B>s)" \<r> \<Lambda>
    using dual_bibd by simp
  show ?thesis using dual_blocks_b local.symmetric by (unfold_locales) (simp)
qed

(* Should have proof that dual is a bibd implies orig bibd must be symmetric *)

end

context ordered_incidence_system 
begin

definition is_dual:: "'b list \<Rightarrow> 'b set list \<Rightarrow> bool" where
"is_dual Vs' Bs' \<equiv> ordered_incidence_system Vs' Bs' \<and> (inc_mat_of Vs' Bs' = N\<^sup>T)"

lemma is_dualI: 
  assumes "ordered_incidence_system Vs' Bs'"
  assumes "(inc_mat_of Vs' Bs' = N\<^sup>T)"
  shows "is_dual Vs' Bs'"
  by (auto simp add: is_dual_def assms)

lemma is_dualD1: 
  assumes "is_dual Vs' Bs'"
  shows  "(inc_mat_of Vs' Bs' = N\<^sup>T)"
  using is_dual_def assms
  by auto 

lemma is_dualD2: 
  assumes "is_dual Vs' Bs'"
  shows  "ordered_incidence_system Vs' Bs'"
  using is_dual_def assms
  by auto 

lemma generated_is_dual: "is_dual [0..<(length \<B>s)] \<B>s*"
proof -
  interpret osys: ordered_incidence_system "[0..<(length \<B>s)]" "\<B>s*" using dual_is_ordered_inc_sys by simp 
  show ?thesis using is_dual_def
    by (simp add: is_dual_def dual_incidence_mat_eq_trans osys.ordered_incidence_system_axioms) 
qed

lemma is_dual_isomorphism_generated: 
  assumes "is_dual Vs' Bs'"
  shows "\<exists> \<pi>. incidence_system_isomorphism (set Vs') (mset Bs') ({0..<(length \<B>s)}) (dual_blocks \<V> \<B>s) \<pi>"
proof -
  interpret os2: ordered_incidence_system "([0..<(length \<B>s)])" "(\<B>s*)"
    by (simp add: dual_is_ordered_inc_sys) 
  interpret os1: ordered_incidence_system Vs' Bs' using assms
    by (simp add: is_dualD2) 
  interpret tos: two_ordered_sys Vs' Bs' "([0..<(length \<B>s)])" "(\<B>s*)" 
     using assms  ordered_incidence_system_axioms two_ordered_sys.intro
     by (simp add: is_dualD2 two_ordered_sys.intro dual_is_ordered_inc_sys)
  have os2V: "os2.\<V> = {0..<(length \<B>s)}"
    by auto 
  have os2B: "os2.\<B> = dual_blocks \<V> \<B>s"
    by (simp add: dual_blocks_ordered_eq) 
  have "os1.N = inc_mat_of Vs' Bs'" by simp
  then have "os2.N = os1.N"
    using assms is_dualD1 dual_incidence_mat_eq_trans by fastforce 
  thus ?thesis using tos.equal_inc_mat_isomorphism_ex os2V os2B by auto
qed

end

end