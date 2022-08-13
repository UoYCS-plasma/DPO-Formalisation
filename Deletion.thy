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

interpretation d: graph D
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


abbreviation d where
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

abbreviation c' where \<open>c' \<equiv> idM\<close>
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

sublocale po: pushout_diagram K L D G b' d g c'
proof
  show \<open>\<^bsub>d\<^esub>\<^sub>V v = \<^bsub>c' \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>K\<^esub>\<close> for v
    by (simp add: morph_comp_def that)
next
  show \<open>\<^bsub>d\<^esub>\<^sub>E e = \<^bsub>c' \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    by (simp add: morph_comp_def that)
next
  show \<open>Ex1M (\<lambda>xa. morphism G D' xa 
    \<and> (\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) 
    \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)) G\<close>
    if \<open>graph D'\<close> \<open>morphism L D' x\<close> \<open>morphism D D' y\<close>
      \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>
      \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close>
    for D' x y
  proof -
    define u where 
          \<open>u \<equiv> \<lparr>node_map = \<lambda>v. if \<exists>v' \<in> V\<^bsub>D\<^esub>. \<^bsub>c'\<^esub>\<^sub>V v' = v then \<^bsub>y\<^esub>\<^sub>V (inv_into V\<^bsub>D\<^esub> \<^bsub>c'\<^esub>\<^sub>V v) else \<^bsub>x\<^esub>\<^sub>V (inv_into V\<^bsub>L\<^esub> \<^bsub>g\<^esub>\<^sub>V v), 
                edge_map = \<lambda>e. if \<exists>e' \<in> E\<^bsub>D\<^esub>. \<^bsub>c'\<^esub>\<^sub>E e' = e then \<^bsub>y\<^esub>\<^sub>E (inv_into E\<^bsub>D\<^esub> \<^bsub>c'\<^esub>\<^sub>E e) else \<^bsub>x\<^esub>\<^sub>E (inv_into E\<^bsub>L\<^esub> \<^bsub>g\<^esub>\<^sub>E e)\<rparr>\<close>

    show ?thesis
    proof (rule_tac x = u in exI, rule conjI)

      show \<open>morphism G D' u 
            \<and> (\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) 
            \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
      proof (intro conjI)
        show \<open>morphism G D' u\<close>
        proof
          show \<open>finite V\<^bsub>D'\<^esub>\<close>
            by (simp add: graph.finite_nodes that)
        next
          show \<open>finite E\<^bsub>D'\<^esub>\<close>
            by (simp add: graph.finite_edges that)
        next
          show \<open>s\<^bsub>D'\<^esub> e \<in> V\<^bsub>D'\<^esub>\<close> if \<open>e \<in> E\<^bsub>D'\<^esub>\<close> for e
            by (simp add: \<open>graph D'\<close> graph.source_integrity that)
        next
          show \<open>t\<^bsub>D'\<^esub> e \<in> V\<^bsub>D'\<^esub>\<close> if \<open>e \<in> E\<^bsub>D'\<^esub>\<close> for e
            by (simp add: \<open>graph D'\<close> graph.target_integrity that)
        next
          show \<open>\<^bsub>u\<^esub>\<^sub>E e \<in> E\<^bsub>D'\<^esub>\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
            by (fastforce simp add: u_def that g.inj_edges 
                morphism.morph_edge_range[OF \<open>morphism D D' y\<close>] 
                morphism.morph_edge_range[OF \<open>morphism L D' x\<close>])
        next
          show \<open>\<^bsub>u\<^esub>\<^sub>V v \<in> V\<^bsub>D'\<^esub>\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
           by (fastforce simp add: u_def that g.inj_nodes 
                morphism.morph_node_range[OF \<open>morphism D D' y\<close>] 
                morphism.morph_node_range[OF \<open>morphism L D' x\<close>])
       next
         show \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>G\<^esub> e) = s\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
         proof -
           consider 
               (a) \<open>\<exists>y \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>. \<^bsub>g\<^esub>\<^sub>E y = e\<close>
             | (b) \<open>e \<in> E\<^bsub>D\<^esub>\<close>
             using \<open>e \<in> E\<^bsub>G\<^esub>\<close>
             by auto
  
           thus ?thesis
           proof cases
             case a
                obtain y' where \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> and \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close>
                  using a by blast
  
                have \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>G\<^esub> e) = \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V (s\<^bsub>L\<^esub> y')\<close>
                  using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> and \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close> 
                  by (fastforce simp add: g.source_preserve morph_comp_def)
  
                also have \<open>\<dots> = \<^bsub>x\<^esub>\<^sub>V (s\<^bsub>L\<^esub> y')\<close>
                proof -
                  obtain v' where \<open>s\<^bsub>L\<^esub> y' = v'\<close> and \<open>v' \<in> V\<^bsub>L\<^esub>\<close>
                    using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close>
                    by (force simp add: g.G.source_integrity)
  
                  obtain v'' where \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> and \<open>v'' \<in> V\<^bsub>G\<^esub>\<close>
                    by (simp add: \<open>s\<^bsub>L\<^esub> y' = v'\<close> \<open>v' \<in> V\<^bsub>L\<^esub>\<close> g.morph_node_range)
  
                  have \<open>\<^bsub>u\<^esub>\<^sub>V v'' = \<^bsub>x\<^esub>\<^sub>V v'\<close>
                  proof (cases \<open>v' \<in> V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>)
                    case True
                    then show ?thesis 
                      using \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> and \<open>v'' \<in> V\<^bsub>G\<^esub>\<close>
                      by (fastforce simp add: u_def g.inj_nodes)
                  next
                    case False
                    then show ?thesis
                      using
                        \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>
                        \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> \<open> v' \<in> V\<^bsub>L\<^esub>\<close> g.inj_nodes

                      by (auto simp add: morph_comp_def inj_on_def u_def)
                  qed
                  thus ?thesis
                    using 
                      \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> \<open> v'' \<in> V\<^bsub>G\<^esub>\<close> \<open>s\<^bsub>L\<^esub> y' = v'\<close> \<open> v' \<in> V\<^bsub>L\<^esub>\<close> 
                      \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close> calculation g.source_preserve 
                    by force
                qed
  
                also have \<open>\<dots> = s\<^bsub>D'\<^esub> (\<^bsub>x\<^esub>\<^sub>E y')\<close>
                  using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close>
                  by (simp add: morphism.source_preserve[OF \<open>morphism L D' x\<close>])
  
                also have \<open>\<dots> =  s\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close>
                  using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close> 
                  by (fastforce simp add: u_def g.inj_edges)
  
                finally show ?thesis .
           next
             case b
             then show ?thesis
             proof -
               obtain y' where \<open>y' \<in> E\<^bsub>D\<^esub>\<close> and \<open>\<^bsub>c'\<^esub>\<^sub>E y' = e\<close>
                 using b by simp
  
               have \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>G\<^esub> e) = \<^bsub>u \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V (s\<^bsub>D\<^esub> y')\<close>
                 using \<open>y' \<in> E\<^bsub>D\<^esub>\<close> and \<open>\<^bsub>c'\<^esub>\<^sub>E y' = e\<close>
                 by (simp add: morph_comp_def)
  
               also have \<open>\<dots> = \<^bsub>y\<^esub>\<^sub>V (s\<^bsub>D\<^esub> y')\<close>
               proof -
                 have \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>D\<^esub> y') = \<^bsub>y\<^esub>\<^sub>V (s\<^bsub>D\<^esub> y')\<close>
                   using \<open>y' \<in> E\<^bsub>D\<^esub>\<close>
                   by (auto simp add: dang_src u_def g.H.source_integrity)
  
                 thus ?thesis
                   by (simp add:morph_comp_def)
               qed
  
               also have \<open>\<dots> = s\<^bsub>D'\<^esub> (\<^bsub>y\<^esub>\<^sub>E y')\<close>
                 using morphism.source_preserve[OF \<open>morphism D D' y\<close>, of y'] \<open>y' \<in> E\<^bsub>D\<^esub>\<close>
                 by simp
  
               also have \<open>\<dots> = s\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close>
                 using \<open>y' \<in> E\<^bsub>D\<^esub>\<close> \<open>\<^bsub>c'\<^esub>\<^sub>E y' = e\<close>
                 by (auto simp add: u_def)
  
                finally show ?thesis .
           qed
         qed
       qed 
     next
     show \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>G\<^esub> e) = t\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
         proof -
           consider 
               (a) \<open>\<exists>y \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>. \<^bsub>g\<^esub>\<^sub>E y = e\<close>
             | (b) \<open>e \<in> E\<^bsub>D\<^esub>\<close>
             using \<open>e \<in> E\<^bsub>G\<^esub>\<close>
             by auto
  
           thus ?thesis
           proof cases
             case a
                obtain y' where \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> and \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close>
                  using a by blast
  
                have \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>G\<^esub> e) = \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V (t\<^bsub>L\<^esub> y')\<close>
                  using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> and \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close> 
                  by (fastforce simp add: g.target_preserve morph_comp_def)
  
                also have \<open>\<dots> = \<^bsub>x\<^esub>\<^sub>V (t\<^bsub>L\<^esub> y')\<close>
                proof -
                  obtain v' where \<open>t\<^bsub>L\<^esub> y' = v'\<close> and \<open>v' \<in> V\<^bsub>L\<^esub>\<close>
                    using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close>
                    by (force simp add: g.G.target_integrity)
  
                  obtain v'' where \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> and \<open>v'' \<in> V\<^bsub>G\<^esub>\<close>
                    by (simp add: \<open>t\<^bsub>L\<^esub> y' = v'\<close> \<open>v' \<in> V\<^bsub>L\<^esub>\<close> g.morph_node_range)
  
                  have \<open>\<^bsub>u\<^esub>\<^sub>V v'' = \<^bsub>x\<^esub>\<^sub>V v'\<close>
                  proof (cases \<open>v' \<in> V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>)
                    case True
                    then show ?thesis 
                      using \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> and \<open>v'' \<in> V\<^bsub>G\<^esub>\<close>
                      by (fastforce simp add: u_def g.inj_nodes)
                  next
                    case False
                    then show ?thesis
                      using
                        \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>
                        \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> \<open> v' \<in> V\<^bsub>L\<^esub>\<close> g.inj_nodes

                      by (auto simp add: morph_comp_def inj_on_def u_def)
                  qed
                  thus ?thesis
                    using 
                      \<open>\<^bsub>g\<^esub>\<^sub>V v' = v''\<close> \<open> v'' \<in> V\<^bsub>G\<^esub>\<close> \<open>t\<^bsub>L\<^esub> y' = v'\<close> \<open> v' \<in> V\<^bsub>L\<^esub>\<close> 
                      \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close> calculation g.target_preserve 
                    by force
                qed
  
                also have \<open>\<dots> = t\<^bsub>D'\<^esub> (\<^bsub>x\<^esub>\<^sub>E y')\<close>
                  using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close>
                  by (simp add: morphism.target_preserve[OF \<open>morphism L D' x\<close>])
  
                also have \<open>\<dots> =  t\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close>
                  using \<open>y' \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> \<open>\<^bsub>g\<^esub>\<^sub>E y' = e\<close> 
                  by (fastforce simp add: u_def g.inj_edges)
  
                finally show ?thesis .
           next
             case b
             then show ?thesis
             proof -
               obtain y' where \<open>y' \<in> E\<^bsub>D\<^esub>\<close> and \<open>\<^bsub>c'\<^esub>\<^sub>E y' = e\<close>
                 using b by simp
  
               have \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>G\<^esub> e) = \<^bsub>u \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V (t\<^bsub>D\<^esub> y')\<close>
                 using \<open>y' \<in> E\<^bsub>D\<^esub>\<close> and \<open>\<^bsub>c'\<^esub>\<^sub>E y' = e\<close>
                 by (simp add: morph_comp_def)
  
               also have \<open>\<dots> = \<^bsub>y\<^esub>\<^sub>V (t\<^bsub>D\<^esub> y')\<close>
               proof -
                 have \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>D\<^esub> y') = \<^bsub>y\<^esub>\<^sub>V (t\<^bsub>D\<^esub> y')\<close>
                   using \<open>y' \<in> E\<^bsub>D\<^esub>\<close>
                   by (auto simp add: dang_trg u_def g.H.target_integrity)
  
                 thus ?thesis
                   by (simp add:morph_comp_def)
               qed
  
               also have \<open>\<dots> = t\<^bsub>D'\<^esub> (\<^bsub>y\<^esub>\<^sub>E y')\<close>
                 using morphism.target_preserve[OF \<open>morphism D D' y\<close>, of y'] \<open>y' \<in> E\<^bsub>D\<^esub>\<close>
                 by simp
  
               also have \<open>\<dots> = t\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close>
                 using \<open>y' \<in> E\<^bsub>D\<^esub>\<close> \<open>\<^bsub>c'\<^esub>\<^sub>E y' = e\<close>
                 by (auto simp add: u_def)
  
                finally show ?thesis .
           qed
         qed
       qed
     next
        show \<open>l\<^bsub>G\<^esub> v = l\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
         proof -
           consider 
               (a) \<open>\<exists>y \<in> V\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>. \<^bsub>g\<^esub>\<^sub>V y = v\<close>
             | (b) \<open>v \<in> V\<^bsub>D\<^esub>\<close>
             using \<open>v \<in> V\<^bsub>G\<^esub>\<close>
             by auto
           thus ?thesis
           proof cases
             case a
             then show ?thesis 
               using g.label_preserve morphism.label_preserve[OF \<open>morphism L D' x\<close>] xxx8 that
               by (auto simp add: u_def)
           next
             case b
             then show ?thesis
               using morphism.label_preserve[OF \<open>morphism D D' y\<close>]
               by (fastforce simp add: u_def)
           qed
         qed
      next
        show \<open>m\<^bsub>G\<^esub> e = m\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
         proof -
           consider 
               (a) \<open>\<exists>y \<in> E\<^bsub>L\<^esub> - \<^bsub>b'\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>. \<^bsub>g\<^esub>\<^sub>E y = e\<close>
             | (b) \<open>e \<in> E\<^bsub>D\<^esub>\<close>
             using \<open>e \<in> E\<^bsub>G\<^esub>\<close>
             by auto
           thus ?thesis
           proof cases
             case a
             then show ?thesis 
               using g.mark_preserve morphism.mark_preserve[OF \<open>morphism L D' x\<close>] xxx8' that
               by (auto simp add: u_def)
           next
             case b
             then show ?thesis
               using morphism.mark_preserve[OF \<open>morphism D D' y\<close>]
               by (fastforce simp add: u_def)
           qed
         qed
       qed
     next
      show \<open>\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
      proof - 
        have \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>L\<^esub>\<close> for v
        proof (cases \<open>\<exists>y \<in> V\<^bsub>K\<^esub>. \<^bsub>b'\<^esub>\<^sub>V y = v\<close>)
          case True
          then show ?thesis
            using \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close> 
            by (auto simp add: u_def morph_comp_def xxx8 that)
        next
          case False
          then show ?thesis
            by (auto simp add: morph_comp_def u_def that xxx8)
        qed

        thus ?thesis ..
      qed
    next
      show \<open>\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
      proof - 
        have \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>L\<^esub>\<close> for e
        proof (cases \<open>\<exists>y \<in> E\<^bsub>K\<^esub>. \<^bsub>b'\<^esub>\<^sub>E y = e\<close>)
          case True
          then show ?thesis
            using \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close> 
            by (auto simp add: u_def morph_comp_def xxx8' that)
        next
          case False
          then show ?thesis
            by (auto simp add: morph_comp_def u_def that xxx8')
        qed

        thus ?thesis ..
      qed
    next
      show \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
        by (simp add: morph_comp_def u_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
        by (simp add: morph_comp_def u_def)
    qed

  next
    show \<open>\<forall>ya. morphism G D' ya 
          \<and> (\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) 
          \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) 
          \<longrightarrow> (\<forall>e\<in>E\<^bsub>G\<^esub>. \<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>G\<^esub>. \<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v)\<close>
    proof safe
      show \<open>\<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close> 
        if \<open>morphism G D' ya\<close> 
          \<open>\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
          \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          \<open>e \<in> E\<^bsub>G\<^esub>\<close> for ya e

      proof (cases \<open>e \<in> E\<^bsub>D\<^esub>\<close>)
        case True
        then show ?thesis
          using \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          by (simp add: u_def)
      next
        case False
        then show ?thesis 
          using \<open>\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> xxx8' \<open>e \<in> E\<^bsub>G\<^esub>\<close>
          by (auto simp add: u_def morph_comp_def)
      qed
    next
      show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close> 
        if \<open>morphism G D' ya\<close> 
          \<open>\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
          \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          \<open>v \<in> V\<^bsub>G\<^esub>\<close> for ya v

      proof (cases \<open>v \<in> V\<^bsub>D\<^esub>\<close>)
        case True
        then show ?thesis
          using \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          by (simp add: u_def)
      next
        case False
        then show ?thesis 
          using \<open>\<forall>v\<in>V\<^bsub>L\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> xxx8 \<open>v \<in> V\<^bsub>G\<^esub>\<close>
          by (auto simp add: u_def morph_comp_def)
      qed
  qed
qed
qed
qed
end
end