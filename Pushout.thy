theory Pushout
imports Morphism Generics
begin

abbreviation Ex1M :: "(('v\<^sub>1,'v\<^sub>2,'e\<^sub>1,'e\<^sub>2) pre_morph \<Rightarrow> bool) \<Rightarrow> ('v\<^sub>1,'e\<^sub>1,'l,'m) pre_graph \<Rightarrow> bool"
  where "Ex1M P E \<equiv> \<exists>x. P x \<and> (\<forall>y. P y 
    \<longrightarrow> ((\<forall>e \<in> E\<^bsub>E\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>(\<forall>v \<in> V\<^bsub>E\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)))"

lemma ex1m_ex: \<open>Ex1M P G \<Longrightarrow> \<exists>m. P m\<close>
  by fast

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
  g: morphism C D g for A B C D b c f g +
assumes
  node_commutativity: \<open>v \<in> V\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> and
  edge_commutativity: \<open>e \<in> E\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> and
  universal_property: \<open>\<lbrakk>
    graph (D' :: ('c,'d) ngraph); 
    morphism (to_ngraph B) D' x; 
    morphism (to_ngraph C) D' y;
     \<forall>v \<in> V\<^bsub>to_ngraph A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> (to_nmorph b)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> (to_nmorph c)\<^esub>\<^sub>V v;
     \<forall>e \<in> E\<^bsub>to_ngraph A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> (to_nmorph b)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> (to_nmorph c)\<^esub>\<^sub>E e\<rbrakk> 

      \<Longrightarrow> Ex1M (\<lambda>u. morphism (to_ngraph D) D' u \<and>
            (\<forall>v \<in> V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph f)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph f)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
            (to_ngraph D)\<close>
begin
 
lemma universal_property_exist_gen:
  fixes D'
  assumes \<open>graph D'\<close> \<open>morphism B D' x\<close> \<open>morphism C D' y\<close>
    \<open>\<forall>v \<in> V\<^bsub>A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close>
    \<open>\<forall>e \<in> E\<^bsub>A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
  shows \<open>Ex1M (\<lambda>u. morphism D D' u \<and>
            (\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)) D\<close>
proof -
  interpret nD: graph \<open>to_ngraph D\<close>
    using graph_ngraph_corres_iff f.H.graph_axioms 
    by blast

  interpret nD': graph \<open>to_ngraph D'\<close>
    using graph_ngraph_corres_iff 
    using assms(1) by blast

  interpret nx: morphism \<open>to_ngraph B\<close> \<open>to_ngraph D'\<close> \<open>to_nmorph x\<close>
    using morph_eq_nmorph_iff[symmetric] assms(2)
    by auto

  interpret ny: morphism \<open>to_ngraph C\<close> \<open>to_ngraph D'\<close> \<open>to_nmorph y\<close>
    using morph_eq_nmorph_iff[symmetric] assms(3)
    by auto

  have n:\<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>to_nmorph x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>to_nmorph y \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v\<close>
    using assms(4) comp_lift_node
    by blast

  have e:\<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>to_nmorph x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>to_nmorph y \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e\<close>
    using assms(5) comp_lift_edge
    by blast

  obtain u where 
      ab: \<open> morphism (to_ngraph D) (to_ngraph D') u\<close> 
    and \<open>\<forall>v \<in> V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph f)\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v\<close>
            \<open>(\<forall>e \<in> E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph f)\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e)\<close> and
            \<open>(\<forall>v \<in> V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v)\<close> and
            \<open>(\<forall>e \<in> E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e)\<close>
    using universal_property[OF nD'.graph_axioms nx.morphism_axioms ny.morphism_axioms n e]
    by fast

  show ?thesis
  proof (rule_tac x = \<open>(from_nmorph u) :: ('i,'k,'j,'l) pre_morph\<close> in exI, intro conjI)
    show \<open>morphism D D' (from_nmorph u)\<close>
      using ab morph_tong_tong_u_is_morph_tonm
      by blast
  next
    show \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>from_nmorph u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
      using \<open>\<forall>v \<in> V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph f)\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>from_nmorph u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
      using \<open>(\<forall>e \<in> E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph f)\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e)\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>from_nmorph u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
      using \<open>(\<forall>v \<in> V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v)\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>from_nmorph u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
      using \<open>(\<forall>e \<in> E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e)\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>ya. morphism D D' ya 
              \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) 
              \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) 
            \<longrightarrow> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>(from_nmorph u)  :: ('i,'k,'j,'l) pre_morph\<^esub>\<^sub>E e) 
              \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>from_nmorph u\<^esub>\<^sub>V v) \<close>
proof -

  have aa: 
    \<open>morphism (to_ngraph D) (to_ngraph D') u 
      \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v) 
      \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e) 
      \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v) 
      \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e)\<close>
    using 
      \<open>\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e\<close>
      \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e\<close>
      \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v\<close>
      \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v\<close> ab
    by simp

  show ?thesis
  proof safe

  show \<open>\<^bsub>u' :: ('i,'k,'j,'l) pre_morph\<^esub>\<^sub>E e = \<^bsub>(from_nmorph u) :: ('i,'k,'j,'l) pre_morph\<^esub>\<^sub>E e\<close> 
    if \<open>morphism D D' u'\<close>
      \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
      \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
      \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
      \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
      \<open>e \<in> E\<^bsub>D\<^esub>\<close> for u' e
  proof -

    have a:
      \<open>morphism (to_ngraph D) (to_ngraph D') (to_nmorph u') 
        \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v) 
        \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e) 
        \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v) 
        \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e)\<close>
    proof (intro conjI)
      show \<open>morphism (to_ngraph D) (to_ngraph D') (to_nmorph u')\<close>
        using morph_eq_nmorph_iff that(1) by blast
    next
      show \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v\<close>
        using that(2) comp_lift_node1
        by blast
    next
      show \<open> \<forall>e::nat\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e\<close>
        using that(3) comp_lift_edge1
        by blast

      show \<open>\<forall>v::nat\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v\<close>
        using that(4) comp_lift_node1
        by blast
    next
      show \<open>\<forall>e::nat\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e\<close>
        using that(5) comp_lift_edge1
        by blast
    qed

    from ex_eq[OF universal_property[OF nD'.graph_axioms nx.morphism_axioms ny.morphism_axioms n e] a aa]
    have \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>to_nmorph u'\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close>
      by simp
          
    thus ?thesis
      using assms that(6) 
      by (auto simp add: to_ngraph_def to_nmorph_def from_nmorph_def) (metis from_nat_to_nat)
  qed
next
  show \<open>\<^bsub>u'\<^esub>\<^sub>V v = \<^bsub>from_nmorph u\<^esub>\<^sub>V v\<close>   
    if \<open>morphism D D' u'\<close>
      \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
      \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
      \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
      \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
      \<open>v \<in> V\<^bsub>D\<^esub>\<close> for u' v
  proof -

    have a:
      \<open>morphism (to_ngraph D) (to_ngraph D') (to_nmorph u') 
        \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v) 
        \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e) 
        \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v) 
        \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>(to_nmorph u') \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e)\<close>
    proof (intro conjI)
      show \<open>morphism (to_ngraph D) (to_ngraph D') (to_nmorph u')\<close>
        using morph_eq_nmorph_iff that(1) by blast
    next
      show \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph x\<^esub>\<^sub>V v\<close>
        using that(2) comp_lift_node1
        by blast
    next
      show \<open> \<forall>e::nat\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>to_nmorph x\<^esub>\<^sub>E e\<close>
        using that(3) comp_lift_edge1
        by blast

      show \<open>\<forall>v::nat\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph y\<^esub>\<^sub>V v\<close>
        using that(4) comp_lift_node1
        by blast
    next
      show \<open>\<forall>e::nat\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph y\<^esub>\<^sub>E e\<close>
        using that(5) comp_lift_edge1
        by blast
    qed


    from ex_eq[OF universal_property[OF nD'.graph_axioms nx.morphism_axioms ny.morphism_axioms n e] a aa]
    have \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>to_nmorph u'\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
      by simp
          
    thus ?thesis
      using assms that(6) 
      by (auto simp add: to_ngraph_def to_nmorph_def from_nmorph_def) (metis from_nat_to_nat)
  qed
qed
qed
qed
qed


lemma b_inj_imp_g_inj:
  assumes \<open>injective_morphism A B b\<close>
  shows \<open>injective_morphism C D g\<close>
proof -
  interpret b: injective_morphism A B b
     using assms by assumption

     define s and t where 
       \<open>s \<equiv> \<lambda>pe. case pe of
                    Inl e \<Rightarrow> Inl (s\<^bsub>C\<^esub> e)
                  | Inr e \<Rightarrow> (if e \<in> (E\<^bsub>B\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>A\<^esub>) \<and> (s\<^bsub>B\<^esub> e \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>A\<^esub>) 
                    then Inl (\<^bsub>c\<^esub>\<^sub>V ((inv_into V\<^bsub>A\<^esub> \<^bsub>b\<^esub>\<^sub>V) (s\<^bsub>B\<^esub> e))) else Inr (s\<^bsub>B\<^esub> e))\<close> and
       \<open>t \<equiv> \<lambda>pe. case pe of
                    Inl e \<Rightarrow> Inl (t\<^bsub>C\<^esub> e)
                  | Inr e \<Rightarrow> (if e \<in> (E\<^bsub>B\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>A\<^esub>) \<and> (t\<^bsub>B\<^esub> e \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>A\<^esub>) 
                    then Inl (\<^bsub>c\<^esub>\<^sub>V ((inv_into V\<^bsub>A\<^esub> \<^bsub>b\<^esub>\<^sub>V) (t\<^bsub>B\<^esub> e))) else Inr (t\<^bsub>B\<^esub> e))\<close> 

     define X :: "('g+'e, 'h+'f, 'c, 'd) pre_graph" where 
       \<open>X \<equiv> \<lparr>nodes = V\<^bsub>C\<^esub> <+> (V\<^bsub>B\<^esub> - \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>A\<^esub>)
            ,edges = E\<^bsub>C\<^esub> <+> (E\<^bsub>B\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>A\<^esub>)
            ,source= s
            ,target= t
            ,node_label=case_sum l\<^bsub>C\<^esub> l\<^bsub>B\<^esub>
            ,edge_label=case_sum m\<^bsub>C\<^esub> m\<^bsub>B\<^esub>\<rparr>\<close>

     interpret X: graph X
      proof
       show \<open>finite V\<^bsub>X\<^esub>\<close>
         by (simp add: X_def b.H.finite_nodes c.H.finite_nodes)
     next
       show \<open>finite E\<^bsub>X\<^esub>\<close>
         by (simp add: X_def b.H.finite_edges c.H.finite_edges)
     next
       show \<open>s\<^bsub>X\<^esub> e \<in> V\<^bsub>X\<^esub>\<close> if \<open>e \<in> E\<^bsub>X\<^esub>\<close> for e
       proof (cases e)
         case (Inl a)
         then show ?thesis
           using that
           by (auto simp add: X_def InlI c.H.source_integrity s_def)
       next
         case (Inr b)
         then show ?thesis 
           using that
           by (auto simp add: X_def s_def b.H.source_integrity b.inj_nodes c.morph_node_range)
       qed
     next
       show \<open>t\<^bsub>X\<^esub> e \<in> V\<^bsub>X\<^esub>\<close> if \<open>e \<in> E\<^bsub>X\<^esub>\<close> for e
       proof (cases \<open>isl e\<close>)
         case True
         then show ?thesis
           using that
           by (auto simp add: X_def InlI c.H.target_integrity t_def)
       next
         case False
         then show ?thesis 
           using that
           by (auto simp add: X_def t_def b.H.target_integrity b.inj_nodes c.morph_node_range)
       qed
     qed
 
     define ix :: "('g, 'g+'e, 'h, 'h+'f) pre_morph"
       where \<open>ix \<equiv> \<lparr>node_map = Inl, edge_map = Inl\<rparr>\<close>

     interpret ix: injective_morphism C X ix
       by standard 
         (auto simp add: 
           ix_def X_def s_def t_def
           c.H.finite_nodes b.H.finite_nodes 
           c.H.finite_edges b.H.finite_edges
           c.H.source_integrity c.H.target_integrity
           b.H.source_integrity b.H.target_integrity)
       
     define iy :: "('e, 'g+'e, 'f, 'h+'f) pre_morph"
       where \<open>iy \<equiv> \<lparr>node_map = \<lambda>v. if v \<in> V\<^bsub>B\<^esub> - \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>A\<^esub> then Inr v else Inl (\<^bsub>c\<^esub>\<^sub>V ((inv_into V\<^bsub>A\<^esub> \<^bsub>b\<^esub>\<^sub>V) v))
                   ,edge_map = \<lambda>e. if e \<in> E\<^bsub>B\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>A\<^esub> then Inr e else Inl (\<^bsub>c\<^esub>\<^sub>E ((inv_into E\<^bsub>A\<^esub> \<^bsub>b\<^esub>\<^sub>E) e))\<rparr>\<close>

     interpret iy: morphism B X iy
     proof
       show \<open>\<^bsub>iy\<^esub>\<^sub>E e \<in> E\<^bsub>X\<^esub>\<close> if \<open>e \<in> E\<^bsub>B\<^esub>\<close> for e
         using that        
         by (auto simp add: iy_def X_def b.inj_edges c.morph_edge_range)
     next
       show \<open>\<^bsub>iy\<^esub>\<^sub>V v \<in> V\<^bsub>X\<^esub>\<close> if \<open>v \<in> V\<^bsub>B\<^esub>\<close> for v
         using that        
         by (auto simp add: iy_def X_def b.inj_nodes c.morph_node_range)
     next
       show \<open>\<^bsub>iy\<^esub>\<^sub>V (s\<^bsub>B\<^esub> e) = s\<^bsub>X\<^esub> (\<^bsub>iy\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>B\<^esub>\<close> for e
       proof (cases \<open>s\<^bsub>B\<^esub> e \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>A\<^esub>\<close>)
         case True
         then show ?thesis
           using that
           unfolding iy_def X_def s_def
           apply auto
           using b.inj_nodes
           by (metis b.G.graph_axioms b.inj_edges b.source_preserve c.source_preserve graph.source_integrity inv_into_f_eq)
       next
         case False
         then show ?thesis 
         using that
           unfolding iy_def X_def s_def
            apply auto
           using b.H.source_integrity apply blast
           using b.G.graph_axioms b.source_preserve graph.source_integrity image_iff apply fastforce
           using b.H.source_integrity by blast
       qed
     next
       show \<open>\<^bsub>iy\<^esub>\<^sub>V (t\<^bsub>B\<^esub> e) = t\<^bsub>X\<^esub> (\<^bsub>iy\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>B\<^esub>\<close> for e
       proof (cases \<open>t\<^bsub>B\<^esub> e \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>A\<^esub>\<close>)
         case True
         then show ?thesis
           using that
           unfolding iy_def X_def t_def
           apply auto
           using b.inj_nodes
           by (metis b.G.graph_axioms b.inj_edges b.target_preserve c.target_preserve graph.target_integrity inv_into_f_eq)
       next
         case False
         then show ?thesis 
         using that
           unfolding iy_def X_def t_def
            apply auto
           using b.H.target_integrity apply blast
           using b.G.graph_axioms b.target_preserve graph.target_integrity image_iff apply fastforce
           using b.H.target_integrity by blast
       qed 
     next
       show \<open>l\<^bsub>B\<^esub> v = l\<^bsub>X\<^esub> (\<^bsub>iy\<^esub>\<^sub>V v)\<close> if \<open> v \<in> V\<^bsub>B\<^esub>\<close> for v
         using that b.inj_nodes b.label_preserve c.label_preserve
         by (auto simp add: X_def iy_def)
     next
       show \<open>m\<^bsub>B\<^esub> e = m\<^bsub>X\<^esub> (\<^bsub>iy\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>B\<^esub>\<close> for e
         using that b.inj_edges b.mark_preserve c.mark_preserve
         by (auto simp add: X_def iy_def)
     qed

     have tr1: \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>iy \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>ix \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close>     
       by (auto simp add: iy_def ix_def morph_comp_def b.inj_nodes)

     have tr2: \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>iy \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>ix \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
       by (auto simp add: iy_def ix_def morph_comp_def b.inj_edges)


     obtain u where \<open>morphism D X u\<close> 
       and   \<open>(\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>iy\<^esub>\<^sub>V v)\<close> \<open>(\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>iy\<^esub>\<^sub>E e)\<close>
       and *:\<open>(\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>ix\<^esub>\<^sub>V v)\<close> \<open>(\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>ix\<^esub>\<^sub>E e)\<close>
       using universal_property_exist_gen[OF X.graph_axioms iy.morphism_axioms ix.morphism_axioms tr1 tr2]
       by fast

     show ?thesis
     proof
       show \<open>inj_on \<^bsub>g\<^esub>\<^sub>V V\<^bsub>C\<^esub>\<close>
         using * ix.inj_nodes
         by (auto simp add: morph_comp_def  inj_on_def) metis
    next
      show \<open>inj_on \<^bsub>g\<^esub>\<^sub>E E\<^bsub>C\<^esub>\<close>
         using * ix.inj_edges
         by (auto simp add: morph_comp_def  inj_on_def) metis
     qed
qed        


theorem uniqueness_po:
  fixes D'
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
    if a: \<open>pushout_diagram A B C D' b c f' g'\<close>
  proof -

  obtain u where \<open>morphism D D' u\<close>
    and \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
    and \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close>
    using universal_property_exist_gen[of D' f' g']
          pushout_diagram.edge_commutativity[OF a] 
          pushout_diagram.node_commutativity[OF a]
          D' f' g'
    by auto

  obtain u' where \<open>morphism D' D u'\<close> 
    and \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
    and \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
    using pushout_diagram.universal_property_exist_gen[of A B C D' b c f' g' D f g]
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
        universal_property_exist_gen[of D f g]
        ex_eq[of \<open>(\<lambda>x. morphism D D x \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e))\<close> D \<open>u' \<circ>\<^sub>\<rightarrow> u\<close> idM]
        edge_commutativity f.H.graph_axioms f.morphism_axioms g.morphism_axioms node_commutativity
          idm wf_morph_comp[OF \<open>morphism D D' u\<close> \<open>morphism D' D u'\<close>]
      by (simp add: bijective_morphism.axioms(1) calculation(1) calculation(2) calculation(3) calculation(4) identity_morphism_def)

    show \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
      using 
        universal_property_exist_gen[of D f g]
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
         pushout_diagram.universal_property_exist_gen[OF a D' \<open>morphism B D' f'\<close> \<open>morphism C D' g'\<close>]
         pushout_diagram.node_commutativity[OF a] pushout_diagram.edge_commutativity[OF a]
         ex_eq[of \<open>(\<lambda>x. morphism D' D' x \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e))\<close> D' \<open>u \<circ>\<^sub>\<rightarrow> u'\<close> idM]
         m idm
       by (simp add: bijective_morphism.axioms(1) calculation(11) calculation(12) calculation(13) calculation(14) identity_morphism_def)

     
     show \<open>\<forall>e \<in> E\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
       using 
         pushout_diagram.universal_property_exist_gen[OF a D' \<open>morphism B D' f'\<close> \<open>morphism C D' g'\<close>]
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
            (\<lambda>xa. morphism (to_ngraph D') D'' xa 
                    \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) 
                    \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) 
                    \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) 
                    \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e))
            (to_ngraph D')\<close> 
         if \<open>graph D''\<close> and \<open>morphism (to_ngraph B) D'' f''\<close> and \<open>morphism (to_ngraph C) D'' g''\<close> 
           and \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v\<close>
           and \<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e\<close>
         for D'' :: "('c,'d) ngraph" and f'' g''
       proof -

         obtain u'' where \<open>morphism (to_ngraph D) D'' u''\<close> and
           \<open>\<forall>v \<in> V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v= \<^bsub>f''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e= \<^bsub>f''\<^esub>\<^sub>E e\<close> and
           \<open>\<forall>v \<in> V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v= \<^bsub>g''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e= \<^bsub>g''\<^esub>\<^sub>E e\<close>
           using 
             universal_property[OF 
               \<open>graph D''\<close> 
               \<open>morphism (to_ngraph B) D'' f''\<close>
               \<open>morphism (to_ngraph C) D'' g''\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e\<close>
              ]
           by fast
         obtain u where \<open>bijective_morphism D D' u\<close> and 
           \<open>\<forall>v \<in> V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v= \<^bsub>f'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e= \<^bsub>f'\<^esub>\<^sub>E e\<close> and
           \<open>\<forall>v \<in> V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v= \<^bsub>g'\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e= \<^bsub>g'\<^esub>\<^sub>E e\<close>
           using ex by auto

         obtain u' where \<open>bijective_morphism D' D u'\<close> and
           \<open>\<forall>v \<in> V\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>D \<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u \<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
           \<open>\<forall>v \<in> V\<^bsub>D'\<^esub>. \<^bsub>u  \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>D'\<^esub>. \<^bsub>u  \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
           using  bijective_morphism.ex_inv[OF \<open>bijective_morphism D D' u\<close>]
           by auto

         let ?x = \<open>\<lparr>node_map = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>V, edge_map=\<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>E\<rparr>\<close>

\<comment> \<open>exist\<close>
         show \<open>Ex1M (\<lambda>x. morphism (to_ngraph D') D'' x 
                \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) 
                \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) 
                \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) 
                \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e)) (to_ngraph D')\<close>
         proof (rule exI, rule conjI)

           show abc: \<open>morphism (to_ngraph D') D'' ?x 
                  \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) 
                  \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) 
                  \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) 
                  \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e)\<close>
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

               moreover have \<open>morphism (to_ngraph D') D'' ?x\<close>
                 using wf_morph_comp 
(* TODO, check proof *)
                   bijective_morphism.axioms(1)[OF \<open>bijective_morphism D' D u'\<close>]
                   \<open>morphism (to_ngraph D) D'' u''\<close>
                   morph_eq_nmorph_iff
                   bijective_morphism.axioms(1)[OF \<open>bijective_morphism D' D u'\<close>]
                 unfolding morph_comp_def
                 by (metis morph_comp_def morph_eq_nmorph_iff pre_morph.ext_inject pre_morph.surjective)


         moreover 
         have  
           \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close> 
           \<open>\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
           and 
           \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> 
           \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
         proof -


           show \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close>
           proof -
             (* here, we have to lift the statement calculcation(1) into to nat space *)
             have \<open>\<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>to_nmorph f\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph B\<^esub> \<close> for v
               using calculation (1) comp_lift_node1 that
               by blast

             thus ?thesis
               using \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close>
               by (simp add: morph_comp_def)
           qed
         next
           show \<open>\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
           proof -
             have \<open>\<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>to_nmorph f\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph B\<^esub>\<close> for e
               using calculation(2) comp_lift_edge1 that
               by blast
             thus ?thesis
               using \<open>\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
               by (simp add: morph_comp_def)
           qed
         next
           show \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close>
           proof -
             have \<open>\<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>to_nmorph g\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph C\<^esub>\<close> for v
               using calculation(3) comp_lift_node1 that
               by blast
             thus ?thesis
               using \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close>
               by (simp add: morph_comp_def)
           qed
         next
           show \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>?x \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
           proof -
             have \<open>\<^bsub>to_nmorph u' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>to_nmorph g\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph C\<^esub>\<close> for e
               using calculation(4) comp_lift_edge1 that
               by blast
             thus ?thesis
               using \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
               by (simp add: morph_comp_def)
           qed
         qed
     
         ultimately show ?thesis
           by simp
           qed
         next
\<comment> \<open>unique\<close>
           show \<open>\<forall>y. morphism (to_ngraph D') D'' y \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) \<and> 
              (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e) \<longrightarrow>
              (\<forall>e\<in>E\<^bsub>to_ngraph D'\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D'\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>?x\<^esub>\<^sub>V v)\<close>
           proof -
             have g1: \<open>\<forall>v \<in> V\<^bsub>to_ngraph D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>?x\<^esub>\<^sub>V v\<close> and g2: \<open>\<forall>e \<in> E\<^bsub>to_ngraph D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e\<close>            
               if \<open>morphism (to_ngraph D') D'' uh\<close>
                  \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
                  \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
                for uh
             proof - 

               have \<open>\<forall>v \<in> V\<^bsub>to_ngraph B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v =\<^bsub>f''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>to_ngraph B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e =\<^bsub>f''\<^esub>\<^sub>E e\<close>
                 using that(2,3)
                   \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close>
                   \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
                 by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)

                 moreover
                 have \<open>\<forall>v \<in> V\<^bsub>to_ngraph C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v =\<^bsub>g''\<^esub>\<^sub>V v\<close> and \<open>\<forall>e \<in> E\<^bsub>to_ngraph C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e =\<^bsub>g''\<^esub>\<^sub>E e\<close>
                   using that(4,5)
                     \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close>
                     \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close>
                   by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)

                 ultimately
                 have dd'': \<open>morphism (to_ngraph D)  D'' (uh \<circ>\<^sub>\<rightarrow> to_nmorph u)  \<and>
                   (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v) \<and>
                   (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e) \<and>
                   (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v) \<and>
                   (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e)\<close>
                   using wf_morph_comp[of \<open>to_ngraph D\<close> \<open>to_ngraph D'\<close> \<open>to_nmorph u\<close> D'' uh]
                     \<open>bijective_morphism D D' u\<close> bijective_morphism.axioms(1) morph_eq_nmorph_iff that(1)
                   by blast


               have x1: \<open>\<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>?x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D'\<^esub>\<close> for v
               proof -
                 have \<open>\<forall>v \<in> V\<^bsub>to_ngraph D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u\<^esub>\<^sub>V v = \<^bsub>u''\<^esub>\<^sub>V v\<close>
                   using ex_eq[OF
                     universal_property[OF \<open>graph D''\<close> \<open>morphism (to_ngraph B) D'' f''\<close> \<open>morphism (to_ngraph C) D'' g''\<close>
                       \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v\<close>    
                       \<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e\<close> 
                       ] dd'']
                      \<open>\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
                      \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
                      \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close>
                      \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>morphism (to_ngraph D) D'' u''\<close>
                  by blast
                  
                 show ?thesis
                 proof -
                   have  \<open>\<forall>v\<in>V\<^bsub>to_ngraph D'\<^esub>. \<^bsub>to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close>
                     using \<open>\<forall>v\<in>V\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>idM\<^esub>\<^sub>V v\<close>
                     by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
                   then 
                   have \<open>\<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>V v\<close>
                     using that
                     by (simp add: morph_comp_def)

                   also have \<open>\<dots> = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>V v\<close>
                   proof -
                     have g:\<open>morphism (to_ngraph D') (to_ngraph D) (to_nmorph u')\<close>
                       using 
                         morph_eq_nmorph_iff
                         bijective_morphism.axioms(1)[OF \<open>bijective_morphism D' D u'\<close>]
                       by blast
                     thus ?thesis
                     using 
                       morphism.morph_node_range[OF g that]
                        \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u\<^esub>\<^sub>V v = \<^bsub>u''\<^esub>\<^sub>V v\<close> 
                     by (simp add: morph_comp_def)
                 qed
                   also have \<open>\<dots> = \<^bsub>?x\<^esub>\<^sub>V v\<close>
                     by simp
                   finally show ?thesis .
                 qed
               qed
             
               show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>V v = \<^bsub>?x\<^esub>\<^sub>V v\<close>
                   using x1
                   by simp

               have x2: \<open>\<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph D'\<^esub>\<close> for e
               proof -
                 have \<open>\<forall>e \<in> E\<^bsub>to_ngraph D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u\<^esub>\<^sub>E e = \<^bsub>u''\<^esub>\<^sub>E e\<close>
                   using ex_eq[OF
                     universal_property[OF \<open>graph D''\<close> \<open>morphism (to_ngraph B) D'' f''\<close> \<open>morphism (to_ngraph C) D'' g''\<close>
                       \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v\<close>    
                       \<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>f'' \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>g'' \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e\<close> 
                       ] dd'']
                      \<open>\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>f''\<^esub>\<^sub>E e\<close>
                      \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>g''\<^esub>\<^sub>E e\<close>
                      \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>f''\<^esub>\<^sub>V v\<close>
                      \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>g''\<^esub>\<^sub>V v\<close> \<open>morphism (to_ngraph D) D'' u''\<close>
                  by blast


                 show ?thesis
                 proof -
                   have \<open>\<forall>e\<in>E\<^bsub>to_ngraph D'\<^esub>. \<^bsub>to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
                     using \<open>\<forall>e\<in>E\<^bsub>D'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>idM\<^esub>\<^sub>E e\<close>
                     by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)

                   then
                   have \<open>\<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>E e\<close>
                     using that
                     by (simp add: morph_comp_def)

                   also have \<open>\<dots> = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> to_nmorph u'\<^esub>\<^sub>E e\<close>
                   proof -
                     have g:\<open>morphism (to_ngraph D') (to_ngraph D) (to_nmorph u')\<close>
                       using 
                         morph_eq_nmorph_iff
                         bijective_morphism.axioms(1)[OF \<open>bijective_morphism D' D u'\<close>]
                       by blast
                     thus ?thesis
                     using 
                       morphism.morph_edge_range[OF g that]
                        \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>uh \<circ>\<^sub>\<rightarrow> to_nmorph u\<^esub>\<^sub>E e = \<^bsub>u''\<^esub>\<^sub>E e\<close> 
                     by (simp add: morph_comp_def)
                   qed

                   also have \<open>\<dots> = \<^bsub>?x\<^esub>\<^sub>E e\<close>
                     by simp
                   finally show ?thesis .
                 qed
               qed

               show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D'\<^esub>. \<^bsub>uh\<^esub>\<^sub>E e = \<^bsub>?x\<^esub>\<^sub>E e\<close>
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