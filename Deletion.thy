theory Deletion
  imports Morphism Pushout Gluing
begin

locale deletion =
  g: injective_morphism L G g +
  l: injective_morphism K L b'
  for K G L g b' +
  assumes
    dang_src: \<open>e \<in> E\<^bsub>G\<^esub> - \<^bsub>g\<^esub>\<^sub>E ` (E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) \<Longrightarrow> s\<^bsub>G\<^esub> e \<notin> \<^bsub>g\<^esub>\<^sub>V ` (V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>)\<close> and
    dang_trg: \<open>e \<in> E\<^bsub>G\<^esub> - \<^bsub>g\<^esub>\<^sub>E ` (E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) \<Longrightarrow> t\<^bsub>G\<^esub> e \<notin> \<^bsub>g\<^esub>\<^sub>V ` (V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>)\<close>
begin


abbreviation V where \<open>V \<equiv> V\<^bsub>G\<^esub> - \<^bsub>g\<^esub>\<^sub>V ` (V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>)\<close>
abbreviation E where \<open>E \<equiv> E\<^bsub>G\<^esub> - \<^bsub>g\<^esub>\<^sub>E ` (E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>)\<close>

abbreviation D where \<open>D \<equiv> G\<lparr>nodes:=V,edges:=E\<rparr>\<close>

sublocale d: graph D
proof
  show \<open>finite V\<^bsub>D\<^esub>\<close>
    by (simp add:g.H.finite_nodes)
next
  show \<open>finite E\<^bsub>D\<^esub>\<close>
    by (simp add:g.H.finite_edges)
next
  show \<open>s\<^bsub>D\<^esub> e \<in> V\<^bsub>D\<^esub>\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that
    by (simp add: g.H.source_integrity dang_src[of e])
next
  show \<open>t\<^bsub>D\<^esub> e \<in> V\<^bsub>D\<^esub>\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that
    by (simp add: g.H.target_integrity dang_trg[of e])
qed


abbreviation d :: "('g, 'e, 'h, 'f) pre_morph" where
\<open>d \<equiv> g \<circ>\<^sub>\<rightarrow> b'\<close>

lemma k_inj_in_d_edge:
  assumes \<open>e \<in> E\<^bsub>K\<^esub>\<close>
  shows \<open>\<^bsub>d\<^esub>\<^sub>E e \<in> E\<^bsub>D\<^esub>\<close>
  using  g.morph_edge_range l.morph_edge_range  g.inj_edges 
  by (fastforce simp add: morph_comp_def assms dest: inj_onD)

lemma k_inj_in_d_node:
  assumes \<open>v \<in> V\<^bsub>K\<^esub>\<close>
  shows \<open>\<^bsub>d\<^esub>\<^sub>V v \<in> V\<^bsub>D\<^esub>\<close>
  using  g.morph_node_range l.morph_node_range  g.inj_nodes
  by (fastforce simp add: morph_comp_def assms dest: inj_onD)


interpretation inj_d: injective_morphism K D d
proof
  show \<open>\<^bsub>d\<^esub>\<^sub>E e \<in> E\<^bsub>D\<^esub>\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    using that k_inj_in_d_edge by blast
next
  show \<open>\<^bsub>d\<^esub>\<^sub>V v \<in> V\<^bsub>D\<^esub>\<close> if \<open>v \<in> V\<^bsub>K\<^esub>\<close> for v
    using that k_inj_in_d_node by blast
next
  show \<open>\<^bsub>d\<^esub>\<^sub>V (s\<^bsub>K\<^esub> e) = s\<^bsub>D\<^esub> (\<^bsub>d\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    using that wf_morph_comp[of K L b' G g]
    by (simp add: g.morphism_axioms l.morphism_axioms morphism.source_preserve)
next
  show \<open>\<^bsub>d\<^esub>\<^sub>V (t\<^bsub>K\<^esub> e) = t\<^bsub>D\<^esub> (\<^bsub>d\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    using that wf_morph_comp[of K L b' G g]
    by (simp add: g.morphism_axioms l.morphism_axioms morphism.target_preserve)
next
  show \<open>l\<^bsub>K\<^esub> v = l\<^bsub>D\<^esub> (\<^bsub>d\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>K\<^esub>\<close> for v
    using that wf_morph_comp[of K L b' G g]
    by (simp add: g.morphism_axioms l.morphism_axioms morphism.label_preserve)
next
  show \<open>m\<^bsub>K\<^esub> e = m\<^bsub>D\<^esub> (\<^bsub>d\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    using that wf_morph_comp[of K L b' G g]
    by (simp add: g.morphism_axioms l.morphism_axioms morphism.mark_preserve)
next
  show \<open>inj_on \<^bsub>d\<^esub>\<^sub>V V\<^bsub>K\<^esub>\<close>
    using inj_comp_inj g.injective_morphism_axioms injective_morphism.inj_nodes l.injective_morphism_axioms morph_comp_def
    by blast
next
  show \<open>inj_on \<^bsub>d\<^esub>\<^sub>E E\<^bsub>K\<^esub>\<close>
    using inj_comp_inj g.injective_morphism_axioms injective_morphism.inj_edges l.injective_morphism_axioms morph_comp_def
    by blast
qed

abbreviation c' :: "('e, 'e, 'f, 'f) pre_morph" where \<open>c' \<equiv> idM\<close>
interpretation inj_d: injective_morphism D G c'
proof                                         
  show \<open>\<^bsub>c'\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>\<^bsub>c'\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
    using that by simp
next
  show \<open>\<^bsub>c'\<^esub>\<^sub>V (s\<^bsub>D\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>c'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>\<^bsub>c'\<^esub>\<^sub>V (t\<^bsub>D\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>c'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>l\<^bsub>D\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>c'\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
    using that by simp
next
  show \<open>m\<^bsub>D\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>c'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>inj_on \<^bsub>c'\<^esub>\<^sub>V V\<^bsub>D\<^esub>\<close>
    by simp
next
  show \<open>inj_on \<^bsub>c'\<^esub>\<^sub>E E\<^bsub>D\<^esub>\<close>
    by simp
qed



lemma xxx[simp]: 
  assumes \<open>e \<in> X\<close>
  shows \<open>inv_into X id e = id e\<close>
  by (metis assms id_apply inj_on_id inv_into_f_f)

lemma xxx2[simp]:
  assumes \<open>e \<in> E\<^bsub>X\<^esub>\<close>
  shows \<open>inv_into E\<^bsub>X\<^esub> id e = id e\<close>
  by (metis assms id_apply inj_on_id inv_into_f_f)

lemma xx11:
  shows \<open>E\<^bsub>D\<^esub> \<subseteq> E\<^bsub>G\<^esub>\<close> and \<open>V\<^bsub>D\<^esub> \<subseteq> V\<^bsub>G\<^esub>\<close>
  by simp_all

lemma xx3:\<open>E \<subseteq> E\<^bsub>G\<^esub>\<close>
  by blast

lemma xx5:
  assumes \<open>\<^bsub>g\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> and \<open>v \<in> V\<^bsub>L\<^esub>\<close>
  shows \<open>\<^bsub>g\<^esub>\<^sub>V v \<notin> \<^bsub>g\<^esub>\<^sub>V ` (V\<^bsub>L\<^esub> - \<^bsub>l\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>) \<longleftrightarrow> v \<in>  \<^bsub>l\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>
  using assms(2) g.inj_nodes inj_onD by fastforce

lemma xxx8:
  assumes \<open>x \<in> V\<^bsub>L\<^esub>\<close>
  shows \<open>inv_into V\<^bsub>L\<^esub> \<^bsub>g\<^esub>\<^sub>V (\<^bsub>g\<^esub>\<^sub>V x) = x\<close>
  by (simp add: assms g.inj_nodes)

lemma xxx8':
  assumes \<open>x \<in> E\<^bsub>L\<^esub>\<close>
  shows \<open>inv_into E\<^bsub>L\<^esub> \<^bsub>g\<^esub>\<^sub>E (\<^bsub>g\<^esub>\<^sub>E x) = x\<close>
  by (simp add: assms g.inj_edges)

lemma case_sum_id_into_disj_union[simp]:
  shows \<open>case_sum id f  ` (Inl ` Y \<union> Inr ` R) = Y \<union> f ` (R)\<close>
  by force

sublocale po: pushout_diagram K L D G b' d g c'
proof -

  interpret gl: gluing K D L d b'
    ..

  define u where 
    \<open>u \<equiv> \<lparr> node_map = case_sum id \<^bsub>g\<^esub>\<^sub>V
         , edge_map = case_sum id \<^bsub>g\<^esub>\<^sub>E\<rparr>\<close>

  interpret u: bijective_morphism gl.H G u
  proof
    show \<open>\<^bsub>u\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>gl.H\<^esub>\<close> for e
      using that g.morph_edge_range
      by (auto simp add: u_def gl.H_def)
  next
    show \<open>\<^bsub>u\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>gl.H\<^esub>\<close> for v
      using that g.morph_node_range
      by (auto simp add: u_def gl.H_def)
  next
    show \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>gl.H\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>gl.H\<^esub>\<close> for e
    proof (cases e)
      case (Inl a)
      then show ?thesis 
        by (simp add: u_def gl.H_def)
    next
      case (Inr b)
      then show ?thesis 
        using that  l.inj_nodes g.source_preserve 
        by (auto simp add: u_def gl.H_def) (metis comp_apply morph_comp_def pre_morph.select_convs(1))
    qed
  next
    show \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>gl.H\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>gl.H\<^esub>\<close> for e
    proof (cases e)
      case (Inl a)
      then show ?thesis 
        by (simp add: u_def gl.H_def)
    next
      case (Inr b)
      then show ?thesis 
        using that  l.inj_nodes g.target_preserve 
        by (auto simp add: u_def gl.H_def) (metis comp_apply morph_comp_def pre_morph.select_convs(1))
    qed
  next
    show \<open>l\<^bsub>gl.H\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>u\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>gl.H\<^esub>\<close> for v
      using that g.label_preserve
      by (auto simp add: u_def gl.H_def)
  next
    show \<open>m\<^bsub>gl.H\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>gl.H\<^esub>\<close> for e
      using that g.mark_preserve
      by (auto simp add: u_def gl.H_def)

  next
    show \<open>bij_betw \<^bsub>u\<^esub>\<^sub>V V\<^bsub>gl.H\<^esub> V\<^bsub>G\<^esub>\<close>
    proof -
      have \<open>V\<^bsub>D\<^esub> \<inter> \<^bsub>g\<^esub>\<^sub>V ` (V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>) = {}\<close>
        using g.inj_nodes
        by fastforce

      moreover 
      have \<open>V\<^bsub>D\<^esub> \<union> \<^bsub>g\<^esub>\<^sub>V ` (V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>) = V\<^bsub>G\<^esub>\<close>
        using g.inj_nodes g.morph_node_range
        by fastforce

      ultimately show ?thesis
        using  g.inj_nodes
        by (force simp add: u_def inj_on_def bij_betw_def gl.H_def)
    qed
  next
    show \<open>bij_betw \<^bsub>u\<^esub>\<^sub>E E\<^bsub>gl.H\<^esub> E\<^bsub>G\<^esub>\<close>
    proof -
      have \<open>E\<^bsub>D\<^esub> \<inter> \<^bsub>g\<^esub>\<^sub>E ` (E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) = {}\<close>
        using g.inj_edges
        by fastforce

      moreover 
      have \<open>E\<^bsub>D\<^esub> \<union> \<^bsub>g\<^esub>\<^sub>E ` (E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) = E\<^bsub>G\<^esub>\<close>
        using g.inj_edges g.morph_edge_range
        by fastforce

      ultimately show ?thesis
        using  g.inj_edges
        by (force simp add: u_def inj_on_def bij_betw_def gl.H_def)
    qed
  qed

  have \<open>\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.h\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close>  \<open>\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.h\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
    and \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.c\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>  \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.c\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
  proof -
    show \<open>\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.h\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close>
      using l.inj_nodes gl.h_def
      by (auto simp add: morph_comp_def u_def l.inj_nodes)
   
  next 
    show \<open>\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.h\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
      using gl.h_def
      by (auto simp add: morph_comp_def u_def l.inj_edges)
  next
    show \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.c\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
      by (simp add: u_def gl.c_def morph_comp_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.c\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
      by (simp add: u_def gl.c_def morph_comp_def)
  qed



  show \<open>pushout_diagram K L D G b' d g c'\<close>
    using 
      u.bijective_morphism_axioms
      gl.po.uniqueness_po[OF g.H.graph_axioms  g.morphism_axioms inj_d.morphism_axioms]
      \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.c\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.h\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close> 
      \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.c\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> gl.h\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close>
    by blast
qed

end

end