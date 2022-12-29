theory Rule
  imports Morphism
begin

record ('v,'e,'l,'m) pre_rule =
  lhs    :: "('v,'e,'l,'m) pre_graph"
  interf :: "('v,'e,'l,'m) pre_graph"
  rhs    :: "('v,'e,'l,'m) pre_graph"

locale rule =
  k: inclusion_morphism "interf r" "lhs r" +
  r: inclusion_morphism "interf r" "rhs r" 
  for r :: "('v::countable,'e :: countable,'l,'m) pre_rule"
begin

lemma k_subset_l:
  \<open>V\<^bsub>interf r\<^esub> \<subseteq> V\<^bsub>lhs r\<^esub>\<close> \<open>E\<^bsub>interf r\<^esub> \<subseteq> E\<^bsub>lhs r\<^esub>\<close>
  by (simp_all add: subset_iff)

lemma k_subset_r:
  \<open>V\<^bsub>interf r\<^esub> \<subseteq> V\<^bsub>rhs r\<^esub>\<close> \<open>E\<^bsub>interf r\<^esub> \<subseteq> E\<^bsub>rhs r\<^esub>\<close>
  by auto  


lemma lhs_morph_impl_interf:
  assumes g: \<open>injective_morphism (lhs r) G g\<close>
  shows \<open>injective_morphism (interf r) G g\<close>
proof -
  interpret g: injective_morphism \<open>lhs r\<close> G g
    using g by assumption

  show ?thesis
  proof
    show \<open>\<^bsub>g\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that 
      by (simp add: g.morph_edge_range)
  next
    show \<open>\<^bsub>g\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
      using that 
      by (simp add: g.morph_node_range)
  next
    show \<open>\<^bsub>g\<^esub>\<^sub>V (s\<^bsub>interf r\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that g.source_preserve k.source_preserve
      by simp
  next
    show \<open>\<^bsub>g\<^esub>\<^sub>V (t\<^bsub>interf r\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that g.target_preserve k.target_preserve
      by simp
  next
    show \<open>l\<^bsub>interf r\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
      using that
      by (simp add: g.label_preserve k.label_preserve)
  next
    show \<open>m\<^bsub>interf r\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that
      by (simp add: g.mark_preserve k.mark_preserve)
  next
    show \<open>inj_on \<^bsub>g\<^esub>\<^sub>V V\<^bsub>interf r\<^esub>\<close>
      using inj_on_subset[OF g.inj_nodes k_subset_l(1)]
      by assumption
  next
    show \<open>inj_on \<^bsub>g\<^esub>\<^sub>E E\<^bsub>interf r\<^esub>\<close>
      using inj_on_subset[OF g.inj_edges k_subset_l(2)]
      by assumption
  qed
qed

lemma rhs_morph_impl_interf:
  assumes g: \<open>injective_morphism (rhs r) G g\<close>
  shows \<open>injective_morphism (interf r) G g\<close>
proof -
  interpret g: injective_morphism \<open>rhs r\<close> G g
    using g by assumption

  show ?thesis
  proof
    show \<open>\<^bsub>g\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that g.morph_edge_range
      by blast
  next
    show \<open>\<^bsub>g\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
      using that g.morph_node_range
      by blast
  next
    show \<open>\<^bsub>g\<^esub>\<^sub>V (s\<^bsub>interf r\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that g.source_preserve k.source_preserve
      using r.edges_g_in_h r.source_preserve by force
  next
    show \<open>\<^bsub>g\<^esub>\<^sub>V (t\<^bsub>interf r\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that g.target_preserve k.target_preserve
      using r.edges_g_in_h r.target_preserve by auto
  next
    show \<open>l\<^bsub>interf r\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
      using that g.label_preserve k.label_preserve r.label_preserve
      using r.nodes_g_in_h by auto
  next
    show \<open>m\<^bsub>interf r\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>g\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that g.mark_preserve k.mark_preserve
      using r.edges_g_in_h r.mark_preserve by auto
  next
    show \<open>inj_on \<^bsub>g\<^esub>\<^sub>V V\<^bsub>interf r\<^esub>\<close>
      using inj_on_subset[OF g.inj_nodes k_subset_r(1)]
      by assumption
  next
    show \<open>inj_on \<^bsub>g\<^esub>\<^sub>E E\<^bsub>interf r\<^esub>\<close>
      using inj_on_subset[OF g.inj_edges k_subset_r(2)]
      by assumption
  qed
qed

end

end