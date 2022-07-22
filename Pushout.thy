theory Pushout
imports Morphism
begin

abbreviation Ex1M :: "(('v\<^sub>1,'v\<^sub>2,'e\<^sub>1,'e\<^sub>2) pre_morph \<Rightarrow> bool) \<Rightarrow> ('v\<^sub>1,'e\<^sub>1,'l,'m) pre_graph \<Rightarrow> bool"
  where "Ex1M P E \<equiv> \<exists>x. P x \<and> (\<forall>y. P y 
    \<longrightarrow> ((\<forall>e \<in> E\<^bsub>E\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>(\<forall>v \<in> V\<^bsub>E\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)))"

lemma ex_eq:
  shows "Ex1M P x \<Longrightarrow> P y \<Longrightarrow> P z \<Longrightarrow> (\<forall>v \<in> V\<^bsub>x\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>z\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>x\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>z\<^esub>\<^sub>E e)"
  by metis

lemma uniq_id_morph:
  assumes \<open>graph G\<close>
  shows\<open>Ex1M (identity_morphism G) G\<close>
  using
    xx3[OF assms]
    identity_morphism.id_edges
    identity_morphism.id_nodes
  by metis

locale pushout_diagram =
  b: morphism A B b +
  c: morphism A C c +
  f: morphism B D f +
  g: morphism C D g for A B C and D :: \<open>('g, 'h, 'k, 'l) pre_graph\<close> and b c f g +
assumes
  node_commutativity: \<open>v \<in> V\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> and
  edge_commutativity: \<open>e \<in> E\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> and
  universal_property: \<open>\<lbrakk>
    graph (D' :: ('g,'h,'k,'l) pre_graph); 
    morphism B D' x; 
    morphism C D' y;
     \<forall>v \<in> V\<^bsub>A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v;
     \<forall>e \<in> E\<^bsub>A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<rbrakk> 

      \<Longrightarrow> Ex1M (\<lambda>u. morphism D D' u \<and>
            (\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
            D\<close>
begin

lemma universal_property_exist:
  fixes D' :: \<open>('g,'h,'k,'l) pre_graph\<close>
  assumes \<open> graph D'\<close> \<open>morphism B D' x\<close> \<open>morphism C D' y\<close>
    \<open>\<forall>v \<in> V\<^bsub>A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close>
    \<open>\<forall>e \<in> E\<^bsub>A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
  shows \<open>\<exists>u. morphism D D' u \<and>
            (\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
  using universal_property[of D' x y] assms
  by fast



lemma
  fixes D' :: \<open>('g, 'h, 'k, 'l) pre_graph\<close>
  assumes 
    D': \<open>graph D'\<close> and 
    f': \<open>morphism B D' f'\<close> and 
    g': \<open>morphism C D' g'\<close>
  shows \<open>pushout_diagram  A B C D' b c f' g' 
    \<longleftrightarrow> (\<exists>u. bijective_morphism D D' u 
          \<and> (\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e)
          \<and> (\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e))\<close>
proof

  show \<open>\<exists>u. bijective_morphism D D' u 
          \<and> (\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e)
          \<and> (\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e)\<close> 
    if a: \<open>pushout_diagram  A B C D' b c f' g'\<close>
  proof -

  obtain u where \<open>morphism D D' u\<close>
    and \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
    and \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close>
    using universal_property[of D' f' g'] 
          pushout_diagram.edge_commutativity[OF a] 
          pushout_diagram.node_commutativity[OF a]
          D' f' g'
    by auto

  obtain u' where \<open>morphism D' D u'\<close> 
    and \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
    and \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
    using pushout_diagram.universal_property[of A B C D' b c f' g' D f g]
    using f.H.graph_axioms a
    using f.morphism_axioms
    using g.morphism_axioms
    using edge_commutativity node_commutativity by auto

\<comment> \<open>u' o u o f = f\<close>
  from \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close>
  have \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close>
    by (simp add: morph_comp_def)
  moreover 
  from \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close> and \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
  have \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
    by (simp add: morph_comp_def)


\<comment> \<open>u' o u o g = g\<close>
  moreover
  from \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close>
  have \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close>
    by (simp add: morph_comp_def)
  moreover 
  from \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close> and \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
  have \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
    by (simp add: morph_comp_def)

\<comment> \<open>id o g = g\<close>
  moreover have \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> and \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
    by simp_all

\<comment> \<open>id o f = f\<close>
  moreover have \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close> and \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
    by simp_all

\<comment> \<open>hence by univ. prop of pushout\<close>
  moreover 
  have \<open>\<forall>v \<in> V\<^bsub>D\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>D\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
  proof -

    have m: \<open>morphism D D (u' \<circ>\<^sub>\<rightarrow> u)\<close>
      by (simp add: wf_morph_comp[OF \<open>morphism D D' u\<close> \<open>morphism D' D u'\<close>])

    have idm: \<open>identity_morphism D idM\<close>
      by (simp add: xx3[OF f.H.graph_axioms])

    show \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close>
      using 
        universal_property[of D f g]
        ex_eq[of \<open>(\<lambda>x. morphism D D x \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e))\<close> D \<open>u' \<circ>\<^sub>\<rightarrow> u\<close> idM]
        edge_commutativity f.H.graph_axioms f.morphism_axioms g.morphism_axioms node_commutativity
          idm wf_morph_comp[OF \<open>morphism D D' u\<close> \<open>morphism D' D u'\<close>]
      by (simp add: bijective_morphism.axioms(1) calculation(1) calculation(2) calculation(3) calculation(4) identity_morphism_def)

    show \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
      using 
        universal_property[of D f g]
        ex_eq[of \<open>(\<lambda>x. morphism D D x \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e))\<close> D \<open>u' \<circ>\<^sub>\<rightarrow> u\<close> idM]
        edge_commutativity f.H.graph_axioms f.morphism_axioms g.morphism_axioms node_commutativity
          idm wf_morph_comp[OF \<open>morphism D D' u\<close> \<open>morphism D' D u'\<close>]
      by (simp add: bijective_morphism.axioms(1) calculation(1) calculation(2) calculation(3) calculation(4) identity_morphism_def)
  qed

\<comment> \<open>Analogously, (i) and (ii) imply\<close>
  moreover 
  have \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
    using assms 
      \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close>
      \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
      by (auto simp add: morph_comp_def)

  moreover 
  have \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close>
    using assms 
      \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close>
      \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
    by (auto simp add: morph_comp_def)



\<comment> \<open>id o f' = f'\<close>
  moreover have \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
    by simp_all

\<comment> \<open>id o g' = g'\<close>
  moreover have \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close>
    by simp_all

\<comment> \<open>hence\<close>
  moreover have \<open>\<forall>v \<in> V\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v =  \<^bsub>idM\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close> 
  proof -
    have m: \<open>morphism D' D' (u \<circ>\<^sub>\<rightarrow> u')\<close>
      by (simp add: wf_morph_comp[OF \<open>morphism D' D u'\<close> \<open>morphism D D' u\<close>])
 
     have idm: \<open>identity_morphism D' idM\<close>
       by (simp add: xx3[OF D'])


     show \<open>\<forall>v \<in> V\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v =  \<^bsub>idM\<^esub>\<^sub>V v\<close>
       using 
         pushout_diagram.universal_property[OF a D' \<open>morphism B D' f'\<close> \<open>morphism C D' g'\<close>]
         pushout_diagram.node_commutativity[OF a] pushout_diagram.edge_commutativity[OF a]
         ex_eq[of \<open>(\<lambda>x. morphism D' D' x \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e))\<close> D' \<open>u \<circ>\<^sub>\<rightarrow> u'\<close> idM]
         m idm
       by (simp add: bijective_morphism.axioms(1) calculation(11) calculation(12) calculation(13) calculation(14) identity_morphism_def)

     
     show \<open>\<forall>e \<in> E\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
       using 
         pushout_diagram.universal_property[OF a D' \<open>morphism B D' f'\<close> \<open>morphism C D' g'\<close>]
         pushout_diagram.node_commutativity[OF a] pushout_diagram.edge_commutativity[OF a]
         ex_eq[of \<open>(\<lambda>x. morphism D' D' x \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e))\<close> D' \<open>u \<circ>\<^sub>\<rightarrow> u'\<close> idM]
         m idm
       by (simp add: bijective_morphism.axioms(1) calculation(11) calculation(12) calculation(13) calculation(14) identity_morphism_def)
   qed
 
   ultimately show ?thesis
    using comp_id_bij[of D D' u u']
      \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> \<open>morphism D D' u\<close> \<open>morphism D' D u'\<close>
    by auto
qed
next
  show \<open>pushout_diagram A B C D' b c f' g'\<close> 
    if ex:\<open>\<exists>u. bijective_morphism D D' u \<and>
        (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and>
        (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and>
        (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e)\<close>
  proof intro_locales
    show \<open>graph D'\<close>
      by (simp add: D')
  next
    show \<open>morphism_axioms B D' f'\<close>
      by (simp add: f' morphism.axioms(3))
  next
    show \<open>morphism_axioms C D' g'\<close>
      by (simp add: g' morphism.axioms(3))
  next
    show \<open>pushout_diagram_axioms A B C D' b c f' g'\<close>
    proof
      show \<open>\<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      proof -
        obtain u where ex: \<open>bijective_morphism D D' u\<close> 
          and \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v= \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e= \<^bsub>f'\<^esub>\<^sub>E e\<close>
          and \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g'\<^esub>\<^sub>E e\<close>
          using ex
          by fast

        have \<open>\<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>u \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v= \<^bsub>f'\<^esub>\<^sub>V v\<close> that
          by (simp_all add: morph_comp_def b.morph_node_range b.morph_edge_range)

         also have \<open>\<dots> = \<^bsub>u \<circ>\<^sub>\<rightarrow> g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g'\<^esub>\<^sub>V v\<close> that
          using node_commutativity
          by (auto simp: morph_comp_def)
 
         also have \<open>\<dots> = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close>
           using \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g'\<^esub>\<^sub>V v\<close>
           by (simp add: c.morph_node_range morph_comp_def that)

         finally show ?thesis .
       qed
     next
       show \<open>\<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
      proof -
        obtain u where ex: \<open>bijective_morphism D D' u\<close> 
          and \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v= \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e= \<^bsub>f'\<^esub>\<^sub>E e\<close>
          and \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g'\<^esub>\<^sub>E e\<close>
          using ex
          by fast

        have \<open>\<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>u \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e= \<^bsub>f'\<^esub>\<^sub>E e\<close> that
          by (simp_all add: morph_comp_def b.morph_node_range b.morph_edge_range)

         also have \<open>\<dots> = \<^bsub>u \<circ>\<^sub>\<rightarrow> g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g'\<^esub>\<^sub>E e\<close> that
          using edge_commutativity
          by (auto simp: morph_comp_def)
 
         also have \<open>\<dots> = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
           using \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g'\<^esub>\<^sub>E e\<close>
           by (simp add: c.morph_edge_range morph_comp_def that)

         finally show ?thesis .
       qed
     next
       show \<open>Ex1M
            (\<lambda>xa. morphism D' D'' xa \<and>
                   (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) \<and>
                   (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) \<and>
                   (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e))
            D'\<close> 
         if \<open>graph D''\<close> and \<open> morphism B D'' f''\<close> and \<open>morphism C D'' g''\<close> 
           and \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close>
           and \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
         for D'' :: \<open>('g, 'h, 'k, 'l) pre_graph\<close> and f'' g''
       proof -

         obtain u'' where \<open>morphism D D'' u''\<close> and
           \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v= \<^bsub>f''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e= \<^bsub>f''\<^esub>\<^sub>E e\<close> and
           \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g''\<^esub>\<^sub>E e\<close>
           using universal_property[of D'']
             \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> 
             \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> 
             \<open>graph D''\<close> \<open>morphism B D'' f''\<close> \<open>morphism C D'' g''\<close>
           by blast

         obtain u where \<open>bijective_morphism D D' u\<close> and 
           \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v= \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e= \<^bsub>f'\<^esub>\<^sub>E e\<close> and
           \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g'\<^esub>\<^sub>E e\<close>
           using ex by auto

         obtain u' where \<open>bijective_morphism D' D u'\<close> and
           \<open>\<forall>v \<in> V\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
           \<open>\<forall>v \<in> V\<^bsub>D'\<^esub>. \<^bsub>u  \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>D'\<^esub>. \<^bsub>u  \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
           using  bijective_morphism.ex_inv[OF \<open>bijective_morphism D D' u\<close>]
           by auto

         let ?x = \<open>\<lparr>node_map = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V, edge_map=\<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E\<rparr>\<close>

\<comment> \<open>exist\<close>
         show \<open>Ex1M (\<lambda>x. morphism D' D'' x 
                \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) 
                \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e)) D'\<close>
         proof (rule exI, rule conjI)
           show abc: \<open>morphism D' D'' ?x 
                  \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) 
                  \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e)\<close>
           proof -

      \<comment> \<open>it follows (i)\<close>           
               have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>B\<^esub>\<close> for v
               proof -
                 have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v\<close>
                   using that \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v= \<^bsub>f'\<^esub>\<^sub>V v\<close>
                   by (simp add: morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v\<close>
                   using  \<open>\<forall>v \<in> V\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close> that
                   by (simp add: f.morph_node_range morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>f\<^esub>\<^sub>V v\<close>
                   by simp
                 finally show ?thesis .
               qed
      
               moreover
               have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>B\<^esub>\<close> for e
               proof -
                 have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e\<close>
                   using that \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e= \<^bsub>f'\<^esub>\<^sub>E e\<close>
                   by (simp add: morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e\<close>
                   using  \<open>\<forall>e \<in> E\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close> that
                   by (simp add: f.morph_edge_range morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>f\<^esub>\<^sub>E e\<close>
                   by simp
                 finally show ?thesis .
               qed


      \<comment> \<open>it follows (i)\<close>           
               moreover
               have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>C\<^esub>\<close> for v
               proof -
                 have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v\<close>
                   using  \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g'\<^esub>\<^sub>V v\<close> that
                   by (simp add: morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>idM \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v\<close>
                   using \<open>\<forall>v \<in> V\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close> that
                   by (simp add: g.morph_node_range morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>g\<^esub>\<^sub>V v\<close>
                   by simp
                 finally show ?thesis .
               qed
      
               moreover
               have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>C\<^esub>\<close> for e
               proof -
                 have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e\<close>
                   using  \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g'\<^esub>\<^sub>E e\<close> that
                   by (simp add: morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>idM \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e\<close>
                   using \<open>\<forall>e \<in> E\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close> that
                   by (simp add: g.morph_edge_range morph_comp_def)
                 also have \<open>\<dots> = \<^bsub>g\<^esub>\<^sub>E e\<close>
                   by simp
                 finally show ?thesis .
               qed

               moreover have \<open>morphism D' D'' ?x\<close>
                 using wf_morph_comp[OF bijective_morphism.axioms(1)[OF \<open>bijective_morphism D' D u'\<close>]
                                    ,OF \<open>morphism D D'' u''\<close>]
                 by (simp add: morph_comp_def)

         moreover 
         have  \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
           and \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
         proof -
           from calculation(1)  \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close>
           show \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close>
             by (simp add: morph_comp_def)
         next
           from calculation(2) \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
           show \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
             by (simp add: morph_comp_def)
         next
           from calculation(3) \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close>
           show \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close>
             by (simp add: morph_comp_def)
         next
           from calculation(4) \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
           show \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
             by (simp add: morph_comp_def)
         qed

         ultimately show ?thesis
           by simp

           qed
         next
\<comment> \<open>unique\<close>
           show \<open>\<forall>y. morphism D' D'' y \<and>
              (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) \<and>
              (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e) \<longrightarrow>
              (\<forall>e\<in>E\<^bsub>D'\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>D'\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>?x\<^esub>\<^sub>V v)\<close>
           proof -
             have g1: \<open>\<forall>v \<in> V\<^bsub>D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>?x\<^esub>\<^sub>V v\<close> and g2: \<open>\<forall>e \<in> E\<^bsub>D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e\<close>            
               if \<open>morphism D' D'' uh\<close>
                  \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
                  \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
               for uh
             proof -
                have \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v =\<^bsub>f''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e =\<^bsub>f''\<^esub>\<^sub>E e\<close>
                  using 
                    \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close>
                    \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
                   by (fastforce simp add: morph_comp_def)+

                 moreover
                 have \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v =\<^bsub>g''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e =\<^bsub>g''\<^esub>\<^sub>E e\<close>
                   using
                     \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close>
                     \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
                   by (fastforce simp add: morph_comp_def)+

                 ultimately 
                 have dd'': \<open>morphism D D'' (uh \<circ>\<^sub>\<rightarrow> u)  \<and>
                   (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) \<and>
                   (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) \<and>
                   (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) \<and>
                   (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e)\<close>
                   using wf_morph_comp[of D D' u D'' uh]
                   using \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>bijective_morphism D D' u\<close> \<open>morphism D' D'' uh\<close> bijective_morphism.axioms(1) 
                   by fast


               have x1: \<open>\<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>?x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>D'\<^esub>\<close> for v
               proof -
                 have \<open>\<forall>v \<in> V\<^bsub>D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>u''\<^esub>\<^sub>V v\<close>
                   using ex_eq[OF universal_property[OF \<open>graph D''\<close> \<open>morphism B D'' f''\<close> \<open>morphism C D'' g''\<close>
                       \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>]
                     dd'']
                   \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>morphism D D'' u''\<close>
                   by simp

                 show ?thesis
                 proof -
                   have \<open>\<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v\<close>
                     using that \<open>\<forall>v\<in>V\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close>
                     by (simp add: morph_comp_def)
                   also have \<open>\<dots> = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v\<close>
                     using  
                       morphism.morph_node_range[OF bijective_morphism.axioms(1)[OF \<open>bijective_morphism D' D u'\<close>]]
                       \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>u''\<^esub>\<^sub>V v\<close> that
                     by (simp add: morph_comp_def)

                   also have \<open>\<dots> = \<^bsub>?x\<^esub>\<^sub>V v\<close>
                     by simp
                   finally show ?thesis .
                 qed
               qed
              
               show \<open>\<forall>v\<in>V\<^bsub>D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>\<lparr>node_map = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V, edge_map = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E\<rparr>\<^esub>\<^sub>V v\<close>
                   using x1
                   by simp

               have x2: \<open>\<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>D'\<^esub>\<close> for e
               proof -
                 have \<open>\<forall>e \<in> E\<^bsub>D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>u''\<^esub>\<^sub>E e\<close>
                   using ex_eq[OF universal_property[OF \<open>graph D''\<close> \<open>morphism B D'' f''\<close> \<open>morphism C D'' g''\<close>
                       \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>]
                     dd'']
                   \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>morphism D D'' u''\<close>
                   by simp

                 show ?thesis
                 proof -
                   have \<open>\<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>uh \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e\<close>
                     using \<open>\<forall>e\<in>E\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close> that
                     by (simp add: morph_comp_def)
                   also have \<open>\<dots> = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e\<close>
                     using  
                       morphism.morph_edge_range[OF bijective_morphism.axioms(1)[OF \<open>bijective_morphism D' D u'\<close>]]
                       \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>u''\<^esub>\<^sub>E e\<close> that
                     by (simp add: morph_comp_def)
                   also have \<open>\<dots> = \<^bsub>?x\<^esub>\<^sub>E e\<close>
                     by simp
                   finally show ?thesis .
                 qed
               qed

               show \<open>\<forall>e\<in>E\<^bsub>D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e\<close>
                 using x2
               by simp
           qed
           show ?thesis
             using g1 g2
             by simp
           qed
         qed
       qed
     qed
   qed
 qed
end

end