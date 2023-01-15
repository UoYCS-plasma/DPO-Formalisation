theory Pushout
  imports Morphism Generics "HOL-Library.Disjoint_Sets"
begin

abbreviation Ex1M :: "(('v\<^sub>1,'v\<^sub>2,'e\<^sub>1,'e\<^sub>2) pre_morph \<Rightarrow> bool) \<Rightarrow> ('v\<^sub>1,'e\<^sub>1,'l,'m) pre_graph \<Rightarrow> bool"
  where "Ex1M P E \<equiv> \<exists>x. P x \<and> (\<forall>y. P y 
    \<longrightarrow> ((\<forall>e \<in> E\<^bsub>E\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>(\<forall>v \<in> V\<^bsub>E\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)))"

lemma ex1m_eq_surrogate:
  assumes \<open>P = T\<close>
  and \<open>Ex1M P A\<close>
shows \<open>Ex1M T A\<close>
  using assms
  by simp
  

lemma ex1m_ex: \<open>Ex1M P G \<Longrightarrow> \<exists>m. P m\<close>
  by fast

lemma ex_eq:
  shows "Ex1M P x \<Longrightarrow> P y \<Longrightarrow> P z \<Longrightarrow> (\<forall>v \<in> V\<^bsub>x\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>z\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>x\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>z\<^esub>\<^sub>E e)"
  by metis

lemma contr_eq1m:
  assumes \<open>Ex1M P G\<close> and \<open>P a\<close> \<open>P b\<close> and \<open>(\<exists>e \<in>E\<^bsub>G\<^esub>. \<^bsub>a\<^esub>\<^sub>E e \<noteq> \<^bsub>b\<^esub>\<^sub>E e) \<or> (\<exists>v \<in>V\<^bsub>G\<^esub>. \<^bsub>a\<^esub>\<^sub>V v \<noteq> \<^bsub>b\<^esub>\<^sub>V v)\<close>
  shows \<open>False\<close>
  using assms
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

lemma flip_diagram:
  \<open>pushout_diagram A C B D c b g f\<close>
proof
  show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v = \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
    using node_commutativity[OF that] by simp
next
  show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e = \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
    using edge_commutativity[OF that] by simp
next
  show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph D) D' xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph D)\<close>
    if  \<open>graph D'\<close> \<open>morphism (to_ngraph C) D' x\<close> \<open>morphism (to_ngraph B) D' y\<close>
        \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v\<close>
        \<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e\<close>
      for D' :: "('c,'d) ngraph" and x y
  proof -
    have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v\<close>
      using \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v\<close>
      by fastforce

    have b: \<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e\<close>
      using  \<open>\<forall>e\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e\<close>
      by fastforce

    have c: \<open>(\<lambda>xa. morphism (to_ngraph D) D' xa \<and>
       (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
       (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)) = (\<lambda>xa. morphism (to_ngraph D) D' xa \<and>
           (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
           (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))\<close>
      by fastforce

    show ?thesis
      using ex1m_eq_surrogate[OF c universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph B) D' y\<close> \<open>morphism (to_ngraph C) D' x\<close> a b]]
      by assumption
  qed
qed

      

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

lemma joint_surjectivity_edges:
  fixes x
  assumes \<open>x \<in> E\<^bsub>D\<^esub>\<close>
  shows \<open>(\<exists>e \<in> E\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>E e = x) \<or> (\<exists>e \<in> E\<^bsub>B\<^esub>. \<^bsub>f\<^esub>\<^sub>E e = x)\<close> 
proof (rule ccontr)
  assume 
    asm: \<open>\<not> ((\<exists>e\<in>E\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>B\<^esub>. \<^bsub>f\<^esub>\<^sub>E e = x))\<close>
  show False
  proof -

    obtain e 
      where e: \<open>e \<in> E\<^bsub>D\<^esub>\<close> 
        and \<open>e \<notin> \<^bsub>g\<^esub>\<^sub>E ` E\<^bsub>C\<^esub>\<close> 
        and \<open>e \<notin> \<^bsub>f\<^esub>\<^sub>E ` E\<^bsub>B\<^esub>\<close>
      using asm assms
      by fast

    define D' 
      where \<open>D' \<equiv> \<lparr>nodes  = V\<^bsub>D\<^esub>
                  ,edges  = E\<^bsub>D\<^esub> <+> {e}
                  ,source = case_sum s\<^bsub>D\<^esub> s\<^bsub>D\<^esub>
                  ,target = case_sum t\<^bsub>D\<^esub> t\<^bsub>D\<^esub>
                  ,node_label = l\<^bsub>D\<^esub>
                  ,edge_label = case_sum m\<^bsub>D\<^esub> m\<^bsub>D\<^esub>\<rparr>\<close>

    interpret D': graph D'
      by standard
        (auto simp add: D'_def e f.H.finite_nodes f.H.finite_edges f.H.source_integrity f.H.target_integrity)

    define fd :: "('i, 'i, 'j, 'j+'j) pre_morph" and gd :: "('i, 'i, 'j, 'j+'j) pre_morph"
      where \<open>fd \<equiv> \<lparr>node_map = id, edge_map = Inl\<rparr>\<close>
        and \<open>gd \<equiv> \<lparr>node_map = id, edge_map = \<lambda>x. if x = e then Inr e else Inl x\<rparr>\<close>

    interpret fd: morphism D D' fd
      by standard (auto simp add: D'_def fd_def)

    interpret gd: morphism D D' gd
      by standard (auto simp add: D'_def gd_def)

    define f' :: "('e, 'i, 'f, 'j + 'j) pre_morph" and g' :: "('g, 'i, 'h, 'j + 'j) pre_morph"
      where \<open>f' = \<lparr>node_map = \<^bsub>f\<^esub>\<^sub>V, edge_map = Inl \<circ> \<^bsub>f\<^esub>\<^sub>E\<rparr>\<close> and
        \<open>g' = \<lparr>node_map = \<^bsub>g\<^esub>\<^sub>V, edge_map = Inl \<circ> \<^bsub>g\<^esub>\<^sub>E\<rparr>\<close>

    interpret f': morphism B D' f'
      by standard 
        (auto simp add: D'_def f'_def f.morph_edge_range f.morph_node_range 
          f.source_preserve f.target_preserve f.label_preserve f.mark_preserve)

    interpret g': morphism C D' g'
      by standard 
        (auto simp add: D'_def g'_def g.morph_edge_range g.morph_node_range 
          g.source_preserve g.target_preserve g.label_preserve g.mark_preserve)

    have tr: \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
      using node_commutativity edge_commutativity
      by (auto simp add: morph_comp_def f'_def g'_def)

    have u1: \<open>morphism D D' fd \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>fd \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>fd \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>fd \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>fd \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e)\<close>
    proof (intro conjI)
      show \<open>morphism D D' fd\<close>
        using fd.morphism_axioms by assumption
    qed (auto simp add: morph_comp_def f'_def fd_def g'_def )
   
    have u2: \<open>morphism D D' gd \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e)\<close>
    proof (intro conjI)
      show \<open>morphism D D' gd\<close>
        using gd.morphism_axioms by assumption
    next
      show \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close>
        by (simp add: morph_comp_def f'_def gd_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
        using \<open>e \<notin> \<^bsub>f\<^esub>\<^sub>E ` E\<^bsub>B\<^esub>\<close>
        by (auto simp add: morph_comp_def f'_def gd_def)
    next
      show \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close> 
        by (simp add: morph_comp_def gd_def g'_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>gd \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close>
        using \<open>e \<notin> \<^bsub>g\<^esub>\<^sub>E ` E\<^bsub>C\<^esub>\<close>   
        by (auto simp add: morph_comp_def g'_def gd_def)
    qed
     
    have diff: \<open>(\<exists>e\<in>E\<^bsub>D\<^esub>. \<^bsub>fd\<^esub>\<^sub>E e \<noteq> \<^bsub>gd\<^esub>\<^sub>E e) \<or> (\<exists>v\<in>V\<^bsub>D\<^esub>. \<^bsub>fd\<^esub>\<^sub>V v \<noteq> \<^bsub>gd\<^esub>\<^sub>V v)\<close>
      by (auto simp add: fd_def gd_def e)


    show ?thesis
      using contr_eq1m[OF universal_property_exist_gen[OF D'.graph_axioms f'.morphism_axioms g'.morphism_axioms tr] u1 u2 diff]
      by assumption
  qed
qed




lemma joint_surjectivity_nodes:
  fixes x
  assumes \<open>x \<in> V\<^bsub>D\<^esub>\<close>
  shows \<open>(\<exists>v \<in> V\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>V v = x) \<or> (\<exists>v \<in> V\<^bsub>B\<^esub>. \<^bsub>f\<^esub>\<^sub>V v = x)\<close> 
proof (rule ccontr)

  assume asm: \<open>\<not> ((\<exists>v\<in>V\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>B\<^esub>. \<^bsub>f\<^esub>\<^sub>V v = x))\<close>
  show False
  proof -

    obtain v
      where v: \<open>v \<in> V\<^bsub>D\<^esub>\<close> 
        and \<open>v \<notin> \<^bsub>g\<^esub>\<^sub>V ` V\<^bsub>C\<^esub>\<close> 
        and \<open>v \<notin> \<^bsub>f\<^esub>\<^sub>V ` V\<^bsub>B\<^esub>\<close>
      using asm assms
      by fast

    define D' 
      where \<open>D' \<equiv> \<lparr>nodes  = V\<^bsub>D\<^esub> <+> {v}
                  ,edges  = E\<^bsub>D\<^esub>
                  ,source = Inl \<circ> s\<^bsub>D\<^esub>
                  ,target = Inl \<circ> t\<^bsub>D\<^esub>
                  ,node_label = case_sum l\<^bsub>D\<^esub> l\<^bsub>D\<^esub>
                  ,edge_label = m\<^bsub>D\<^esub>\<rparr>\<close>

    interpret D': graph D'
      by standard
        (auto simp add: D'_def v f.H.finite_nodes f.H.finite_edges f.H.source_integrity f.H.target_integrity)

    define u1 :: "('i, 'i+'i, 'j, 'j) pre_morph" and u2 :: "('i, 'i+'i, 'j, 'j) pre_morph"
      where \<open>u1 \<equiv> \<lparr>node_map = Inl, edge_map = id\<rparr>\<close>
        and \<open>u2 \<equiv> \<lparr>node_map = \<lambda>x. if x = v then Inr x else Inl x, edge_map = id\<rparr>\<close>

    interpret fd: morphism D D' u1
      by standard (auto simp add: D'_def u1_def)

    define f' :: "('e, 'i+'i, 'f, 'j) pre_morph" and g' :: "('g, 'i+'i, 'h, 'j) pre_morph"
      where \<open>f' = \<lparr>node_map = Inl \<circ> \<^bsub>f\<^esub>\<^sub>V, edge_map = \<^bsub>f\<^esub>\<^sub>E\<rparr>\<close> and
        \<open>g' = \<lparr>node_map = Inl \<circ> \<^bsub>g\<^esub>\<^sub>V, edge_map = \<^bsub>g\<^esub>\<^sub>E\<rparr>\<close>

    interpret f': morphism B D' f'
      by standard 
        (auto simp add: D'_def f'_def f.morph_edge_range f.morph_node_range 
          f.source_preserve f.target_preserve f.label_preserve f.mark_preserve)

    interpret g': morphism C D' g'
      by standard 
        (auto simp add: D'_def g'_def g.morph_edge_range g.morph_node_range 
          g.source_preserve g.target_preserve g.label_preserve g.mark_preserve)

    have tr: \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close>
      using node_commutativity edge_commutativity
      by (auto simp add: morph_comp_def f'_def g'_def)

    have u1: \<open>morphism D D' u1 \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u1 \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u1 \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u1 \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u1 \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e)\<close>
    proof (intro conjI)
      show \<open>morphism D D' u1\<close>
        using fd.morphism_axioms  by assumption
    qed (auto simp add: morph_comp_def f'_def u1_def g'_def)

    show ?thesis
    proof (cases \<open>\<exists>x \<in> E\<^bsub>D\<^esub>. (s\<^bsub>D\<^esub> x = v \<or> t\<^bsub>D\<^esub> x = v)\<close>)
      case True
      then show ?thesis 
      proof -
        obtain e where \<open>e \<in> E\<^bsub>D\<^esub>\<close> \<open>s\<^bsub>D\<^esub> e = v \<or> t\<^bsub>D\<^esub> e = v\<close>
          using True
          by blast

        show ?thesis (* proof generated by sledgehammer *)
          using \<open>e \<in> E\<^bsub>D\<^esub>\<close> \<open>s\<^bsub>D\<^esub> e = v \<or> t\<^bsub>D\<^esub> e = v\<close> \<open>v \<notin> \<^bsub>f\<^esub>\<^sub>V ` V\<^bsub>B\<^esub>\<close> \<open>v \<notin> \<^bsub>g\<^esub>\<^sub>V ` V\<^bsub>C\<^esub>\<close> f.source_preserve f.target_preserve b.H.source_integrity c.H.source_integrity b.H.target_integrity b.H.source_integrity imageI f.source_preserve g.source_preserve f.target_preserve g.target_preserve joint_surjectivity_edges 
        proof -
          obtain hh :: 'h and ff :: 'f where
            "hh \<in> E\<^bsub>C\<^esub> \<and> e = \<^bsub>g\<^esub>\<^sub>E hh \<or> ff \<in> E\<^bsub>B\<^esub> \<and> e = \<^bsub>f\<^esub>\<^sub>E ff"
            using \<open>e \<in> E\<^bsub>D\<^esub>\<close> joint_surjectivity_edges by moura
          then have f1: "ff \<in> E\<^bsub>B\<^esub> \<and> e = \<^bsub>f\<^esub>\<^sub>E ff"
          proof -
            have f1: "hh \<in> E\<^bsub>C\<^esub> \<longrightarrow> t\<^bsub>C\<^esub> hh \<in> V\<^bsub>C\<^esub>"
              using c.H.target_integrity by blast
            have f2: "hh \<in> E\<^bsub>C\<^esub> \<longrightarrow> s\<^bsub>C\<^esub> hh \<in> V\<^bsub>C\<^esub>"
              using c.H.source_integrity by blast
            have f3: "hh \<in> E\<^bsub>C\<^esub> \<longrightarrow> \<^bsub>g\<^esub>\<^sub>V (s\<^bsub>C\<^esub> hh) = s\<^bsub>D\<^esub> (\<^bsub>g\<^esub>\<^sub>E hh)"
              using g.source_preserve by blast
            have "\<forall>ga. ga \<notin> V\<^bsub>C\<^esub> \<or> v \<noteq> \<^bsub>g\<^esub>\<^sub>V ga"
              using \<open>v \<notin> \<^bsub>g\<^esub>\<^sub>V ` V\<^bsub>C\<^esub>\<close> by blast
            then have "e \<noteq> \<^bsub>g\<^esub>\<^sub>E hh \<or> hh \<notin> E\<^bsub>C\<^esub>"
              using f3 f2 f1 \<open>s\<^bsub>D\<^esub> e = v \<or> t\<^bsub>D\<^esub> e = v\<close> g.target_preserve by fastforce
            then have "hh \<notin> E\<^bsub>C\<^esub> \<or> e \<noteq> \<^bsub>g\<^esub>\<^sub>E hh"
              by meson
            then show ?thesis
              using \<open>hh \<in> E\<^bsub>C\<^esub> \<and> e = \<^bsub>g\<^esub>\<^sub>E hh \<or> ff \<in> E\<^bsub>B\<^esub> \<and> e = \<^bsub>f\<^esub>\<^sub>E ff\<close> by force
          qed
          then have f2: "ff \<in> E\<^bsub>B\<^esub>"
            by meson
          have f3: "e = \<^bsub>f\<^esub>\<^sub>E ff"
            using f1 by blast
          have f4: "t\<^bsub>B\<^esub> ff \<in> V\<^bsub>B\<^esub>"
            using f2 b.H.target_integrity by blast
          have f5: "s\<^bsub>B\<^esub> ff \<in> V\<^bsub>B\<^esub>"
            using f2 b.H.source_integrity by blast
          have f6: "\<forall>e. e \<notin> V\<^bsub>B\<^esub> \<or> v \<noteq> \<^bsub>f\<^esub>\<^sub>V e"
            using \<open>v \<notin> \<^bsub>f\<^esub>\<^sub>V ` V\<^bsub>B\<^esub>\<close> by blast
          then have f7: "v \<noteq> \<^bsub>f\<^esub>\<^sub>V (t\<^bsub>B\<^esub> ff)"
            using f4 by blast
          have f8: "v \<noteq> \<^bsub>f\<^esub>\<^sub>V (s\<^bsub>B\<^esub> ff)"
            using f6 f5 by blast
          have f9: "v \<noteq> t\<^bsub>D\<^esub> e"
            using f7 f3 f2 by (simp add: f.target_preserve)
          have "s\<^bsub>D\<^esub> e \<noteq> v"
            using f8 f3 f2 f.source_preserve by fastforce
          then show ?thesis
            using f9 \<open>s\<^bsub>D\<^esub> e = v \<or> t\<^bsub>D\<^esub> e = v\<close> by presburger
        qed
      qed
    next
      case False
      then show ?thesis 
      proof -
        interpret gd: morphism D D' u2
        proof (unfold_locales, auto simp add: D'_def u2_def)
          show False if \<open>e \<in> E\<^bsub>D\<^esub>\<close> and \<open>v = s\<^bsub>D\<^esub> e\<close> for e
            using False that
            by blast
        next
          show False if \<open>e \<in> E\<^bsub>D\<^esub>\<close> and \<open>v = t\<^bsub>D\<^esub> e\<close> for e
            using False that
            by blast
        qed

        have u2: \<open>morphism D D' u2 \<and> (\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e)\<close>
        proof (intro conjI)
          show \<open>morphism D D' u2\<close>
            using gd.morphism_axioms by assumption
        next
          show \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close>
            using \<open>v \<notin> \<^bsub>f\<^esub>\<^sub>V ` V\<^bsub>B\<^esub>\<close>
            by (auto simp add: morph_comp_def f'_def u2_def)
        next
          show \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
            by (simp add: morph_comp_def f'_def u2_def)
        next
          show \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g'\<^esub>\<^sub>V v\<close>
            using \<open>v \<notin> \<^bsub>g\<^esub>\<^sub>V ` V\<^bsub>C\<^esub>\<close>     
            by (auto simp add: morph_comp_def g'_def u2_def)
        next
          show \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u2 \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g'\<^esub>\<^sub>E e\<close>
            by (simp add: morph_comp_def g'_def u2_def)
        qed
          
        have diff: \<open>(\<exists>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u1\<^esub>\<^sub>E e \<noteq> \<^bsub>u2\<^esub>\<^sub>E e) \<or> (\<exists>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u1\<^esub>\<^sub>V v \<noteq> \<^bsub>u2\<^esub>\<^sub>V v)\<close>
          by (auto simp add: u1_def u2_def v)


        show ?thesis
          using contr_eq1m[OF universal_property_exist_gen[OF D'.graph_axioms f'.morphism_axioms g'.morphism_axioms tr] u1 u2 diff]
          by assumption

      qed
    qed
  qed
qed


lemma b_surj_imp_g_surj:
  assumes \<open>surjective_morphism A B b\<close>
  shows \<open>surjective_morphism C D g\<close>
proof -
  interpret b: surjective_morphism A B b
    using assms by assumption

   show ?thesis
   proof
     show \<open>\<exists>v'\<in>V\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>V v' = v\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
       using that node_commutativity b.surj_nodes c.morph_node_range joint_surjectivity_nodes
       by (force simp add: morph_comp_def)
   next
     show \<open>\<exists>e'\<in>E\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>E e' = e\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
       using that edge_commutativity b.surj_edges c.morph_edge_range joint_surjectivity_edges
       by (force simp add: morph_comp_def)
   qed
 qed
     

lemma b_bij_imp_g_bij:
  assumes \<open>bijective_morphism A B b\<close>
  shows \<open>bijective_morphism C D g\<close>
proof -
  interpret b: bijective_morphism A B b 
    using assms by assumption
  thm conjE
  show ?thesis
  proof (rule inj_surj_morph_is_bijI)
    show \<open>injective_morphism C D g\<close>
      using b_inj_imp_g_inj 
      by (simp add: b.injective_morphism_axioms)
  next
    show \<open>surjective_morphism C D g\<close>
      using b_surj_imp_g_surj assms
      by (auto elim: bijective_morphismE)
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


theorem uniqueness_po_generalised:
  fixes D' C' u
  assumes 
    D': \<open>graph D'\<close> and 
    f': \<open>morphism B D' f'\<close> and 
    g': \<open>morphism C' D' g'\<close> and
    u: \<open>bijective_morphism C C' u\<close> and
    po2: \<open>pushout_diagram  A B C' D' b c' f' g'\<close>
  shows \<open>\<exists>x. bijective_morphism D D' x\<close>
proof -
  interpret D': graph D'
    using D' by assumption
  interpret f': morphism B D' f'
    using f' by assumption
  interpret g': morphism C' D' g'
    using g' by assumption

  interpret u: bijective_morphism C C' u
    using u by assumption

  obtain uinv where uinv:\<open>bijective_morphism C' C uinv\<close>
    and \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = v\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = e\<close> \<open>\<forall>v\<in>V\<^bsub>C'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v = v\<close> \<open>\<forall>e\<in>E\<^bsub>C'\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e = e\<close>
  using u.ex_inv 
  by blast

  interpret uinv: bijective_morphism C' C uinv
    using uinv by assumption

  interpret po2: pushout_diagram A B C' D' b c' f' g'
    using po2 by assumption

  interpret g'u: morphism C D' "g' \<circ>\<^sub>\<rightarrow> u"
    using wf_morph_comp[OF u.morphism_axioms g']
    by assumption

  have \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
    using that node_commutativity po2.node_commutativity
    apply (auto simp add: morph_comp_def)
    sledgehammer

  have a: \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close>
    using node_commutativity po2.node_commutativity
    apply (auto simp add: morph_comp_def)
    sorry
    obtain u'' where \<open>morphism D D' u''\<close>
        using universal_property_exist_gen[OF D' f' g'u.morphism_axioms ]

  
  interpret morphism C' D "uinv \<circ>\<^sub>\<rightarrow> g'"
  obtain u' where \<open>morphism D' D u'\<close>
   
    using po2.universal_property_exist_gen[OF f.H.graph_axioms f.morphism_axioms ]
    
  obtain u'' where \<open>morphism D D' u''\<close>
    sorry



end

(* Fundamentals of Alg. Graph Transformation
   Pushout composition
   Fact 2.20 PDF page 41 
 *)

lemma pushout_composition:
  assumes
    1: \<open>pushout_diagram A B C D f g g' f'\<close> and
    2: \<open>pushout_diagram B E D F e g' e'' e'\<close>
  shows \<open>pushout_diagram A E C F (e \<circ>\<^sub>\<rightarrow> f) g  e'' (e' \<circ>\<^sub>\<rightarrow> f')\<close>
proof -
  interpret 1: pushout_diagram A B C D f g g' f'
    using 1 by assumption

  interpret 2: pushout_diagram B E D F e g' e'' e'
    using 2 by assumption

  interpret ef: morphism A E \<open>e \<circ>\<^sub>\<rightarrow> f\<close>
    using wf_morph_comp[OF "1.b.morphism_axioms" "2.b.morphism_axioms"]
    by assumption

  interpret e'f': morphism C F \<open>e' \<circ>\<^sub>\<rightarrow> f'\<close>
    using wf_morph_comp[OF "1.g.morphism_axioms" "2.g.morphism_axioms"]
    by assumption

  show ?thesis
  proof 
    show \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      using that "1.node_commutativity" "2.node_commutativity" "1.b.morph_node_range"
      by(simp add: morph_comp_def)
  next
    show \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>E ea = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>A\<^esub>\<close> for ea
      using that "1.edge_commutativity" "2.edge_commutativity" "1.b.morph_edge_range"
      by(simp add: morph_comp_def)
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph F) X xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) 
            \<and> (\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e) 
            \<and> (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v)
            \<and> (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e))
        (to_ngraph F)\<close>
      if \<open>graph X\<close> \<open>morphism (to_ngraph E) X h\<close> \<open>morphism (to_ngraph C) X k\<close>
        \<open> \<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>V v = \<^bsub>k \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close>
        \<open>\<forall>ea\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>E ea = \<^bsub>k \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close>
      for X :: "('c,'d) ngraph" and h k
    proof -
      interpret D': graph X
        using \<open>graph X\<close> by assumption

      interpret nE: graph \<open>to_ngraph E\<close>
        by (simp add: "2.b.H.graph_axioms" graph_ngraph_corres_iff)
      interpret nC: graph \<open>to_ngraph C\<close>
        by (simp add: "1.c.H.graph_axioms" graph_ngraph_corres_iff)
      interpret x: morphism \<open>to_ngraph E\<close> X h
        by (simp add: that(2))
      interpret y: morphism \<open>to_ngraph C\<close> X k
        by (simp add: that(3))

      interpret nf': morphism \<open>to_ngraph C\<close> \<open>to_ngraph D\<close> \<open>to_nmorph f'\<close>
        using "1.g.morphism_axioms" morph_eq_nmorph_iff by blast

      interpret nbx: morphism \<open>to_ngraph B\<close> X \<open>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<close>
        using "2.b.morphism_axioms" morph_eq_nmorph_iff wf_morph_comp x.morphism_axioms by blast

      have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>k \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close>
        using \<open> \<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>V v = \<^bsub>k \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close>
        by (simp add:  to_nmorph_dist morph_assoc_nodes)
      have b: \<open>\<forall>ea\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E ea = \<^bsub>k \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close>
        using \<open>\<forall>ea\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>E ea = \<^bsub>k \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close>
        by (simp add:  to_nmorph_dist morph_assoc_edges)

(* From pushout (1) we obtain a unique morphism y: D \<rightarrow> X *)
      obtain y where \<open>morphism (to_ngraph D) X y\<close>
        and "**v": \<open>\<And>v. v \<in> V\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
        and "**e":\<open>\<And>e. e \<in> E\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close>
        and "**v2": \<open>\<And>v. v \<in> V\<^bsub>to_ngraph B\<^esub> \<Longrightarrow> \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v\<close>
        and "**e2": \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph B\<^esub> \<Longrightarrow> \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea\<close>
        using "1.universal_property"[OF \<open>graph X\<close> nbx.morphism_axioms y.morphism_axioms a b]
        by fast

      have uniq_y: \<open>(\<forall>v \<in> V\<^bsub>to_ngraph D\<^esub>. \<^bsub>uy\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>to_ngraph D\<^esub>. \<^bsub>uy\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close> 
        if \<open>morphism (to_ngraph D) X uy\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>uy \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
            \<open>\<And>e. e \<in> E\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>uy \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph B\<^esub> \<Longrightarrow> \<^bsub>uy \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v\<close>
            \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph B\<^esub> \<Longrightarrow> \<^bsub>uy \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea\<close>
          for uy
        using that ex_eq[OF "1.universal_property"[OF \<open>graph X\<close> nbx.morphism_axioms y.morphism_axioms a b], of uy y]
        by (simp add: "**e" "**e2" "**v" "**v2" \<open>morphism (to_ngraph D) X y\<close>)
 
(* Pushout (2)  *)
      have a':\<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v\<close>
        by (simp add: "**v2")
      have b': \<open>\<forall>ea\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea\<close>
        by (simp add: "**e2")

      obtain x where \<open>morphism (to_ngraph F) X x\<close>
        and "***v": \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
        and "***e":\<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
        and  "*v":\<open>\<And>v. v \<in> V\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
        and "*e": \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close>
        using "2.universal_property"[OF \<open>graph X\<close> x.morphism_axioms \<open>morphism (to_ngraph D) X y\<close> a' b']
        by fast

      have uniq_x: \<open>(\<forall>v \<in> V\<^bsub>to_ngraph F\<^esub>. \<^bsub>ux\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>to_ngraph F\<^esub>. \<^bsub>ux\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
        if \<open>morphism (to_ngraph F) X ux\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
            \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
            \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close>
          for ux
        using that ex_eq[OF "2.universal_property"[OF \<open>graph X\<close> x.morphism_axioms \<open>morphism (to_ngraph D) X y\<close> a' b'], of ux x]
        by (simp add: "***e" "***v" "*e" "*v" \<open>morphism (to_ngraph F) X x\<close>)

(* which implies  e ◦ f = y ◦ f = k. M *)
      have p1: \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph C\<^esub>\<close> for v
      proof -
        have \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close>
        using that "*v" nf'.morph_node_range
        by (simp add: morph_comp_def)
      also have \<open>\<dots> = \<^bsub>k\<^esub>\<^sub>V v\<close>
        using "**v" that
        by (simp add: morph_comp_def)
      finally show ?thesis .
    qed
      have p1u: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph C\<^esub>\<close> \<open>morphism (to_ngraph F) X ux\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
            \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
            \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close> for v ux
      proof -
          have \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close>
          using that "*v" nf'.morph_node_range
          by (simp add: morph_comp_def)
        also have \<open>\<dots> = \<^bsub>k\<^esub>\<^sub>V v\<close>
          using "**v" that
          by (simp add: morph_comp_def)
        finally show ?thesis .
      qed

    have p2: \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>to_ngraph C\<^esub>\<close> for ea
    proof -
        have \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea\<close>
        using that "*e" nf'.morph_edge_range
        by (simp add: morph_comp_def)
      also have \<open>\<dots> = \<^bsub>k\<^esub>\<^sub>E ea\<close>
        using "**e" that
        by (simp add: morph_comp_def)
      finally show ?thesis .
    qed
    have p2u: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>to_ngraph C\<^esub>\<close> \<open>morphism (to_ngraph F) X ux\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
            \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
            \<open>\<And>v. v \<in> V\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
            \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph D\<^esub> \<Longrightarrow> \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close> for ea ux
    proof -
        have \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea\<close>
        using that "*e" nf'.morph_edge_range
        by (simp add: morph_comp_def)
      also have \<open>\<dots> = \<^bsub>k\<^esub>\<^sub>E ea\<close>
        using "**e" that
        by (simp add: morph_comp_def)
      finally show ?thesis .
    qed

    have uniq: \<open>(\<forall>e\<in>E\<^bsub>to_ngraph F\<^esub>. \<^bsub>ux\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph F\<^esub>. \<^bsub>ux\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
      if \<open>morphism (to_ngraph F) X ux\<close>
        \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
         \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
         \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
         \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close>
       for ux
    proof -
      have a: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph E\<^esub>\<close> for v
        using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
        by simp
      have b: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>to_ngraph E\<^esub>\<close> for ea
        using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
        by simp

(* following is used to proof c *)
        have ac: \<open>morphism (to_ngraph D) X (ux \<circ>\<^sub>\<rightarrow> to_nmorph e')\<close>
          using "2.g.morphism_axioms" \<open>morphism (to_ngraph F) X ux\<close> morph_eq_nmorph_iff wf_morph_comp
          by blast

        have bc: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph C\<^esub>\<close> for v
          using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
          by (simp add:  to_nmorph_dist morph_assoc_nodes)

        have cc: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph C\<^esub>\<close> for e
          using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close>
          by (simp add: to_nmorph_dist morph_assoc_edges)


        have dc: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph B\<^esub>\<close> for v
        proof -
          have \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'' \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v\<close>
            using "2.node_commutativity" that
            by (force simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          also have \<open>\<dots> = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v\<close>
          proof -
            have \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> if \<open>v\<in>V\<^bsub>to_ngraph E\<^esub>\<close> for v
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> that
              by simp

            thus ?thesis
              using that "2.b.morph_node_range"
              by (fastforce simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          qed
          finally show ?thesis .
        qed
        
        have ec: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>to_ngraph B\<^esub>\<close> for ea
        proof -
          have \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea = \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'' \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea\<close>
            using "2.edge_commutativity" that
            by (force simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          also have \<open>\<dots> = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea\<close>
          proof -
            have \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close> if \<open>e\<in>E\<^bsub>to_ngraph E\<^esub>\<close> for e
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close> that
              by simp

            thus ?thesis
              using that "2.b.morph_edge_range"
              by (fastforce simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          qed
          finally show ?thesis .
        qed

        have c: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D\<^esub>\<close> for v
          using that uniq_y[OF ac bc cc dc ec]
          by fast
     
      
      have d: \<open>\<^bsub>ux \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>to_ngraph D\<^esub>\<close> for ea
       using that uniq_y[OF ac bc cc dc ec]
          by fast
      
    show ?thesis
       using uniq_x[OF \<open>morphism (to_ngraph F) X ux\<close> a b c d]
       by fast
   qed

    show ?thesis
    proof (rule_tac x=x in exI, intro conjI)
      show \<open>morphism (to_ngraph F) X x\<close>
        by (simp add: \<open>morphism (to_ngraph F) X x\<close>)
    next
      show \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
        using "***v" by simp
    next
      show \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
        using "***e" by simp
    next
      show \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
        using \<open>\<And>v. v \<in> V\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
        by (simp add:  to_nmorph_dist morph_assoc_nodes)
    next
      show \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close>
        using \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close>
        by (simp add:  to_nmorph_dist morph_assoc_edges)
    next
      show \<open>\<forall>y. morphism (to_ngraph F) X y \<and>
        (\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and>
        (\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e) \<and>
        (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v) \<and>
        (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e) \<longrightarrow>
        (\<forall>e\<in>E\<^bsub>to_ngraph F\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph F\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
        by (simp add: uniq)
    qed
  qed
qed
qed

lemma pushout_decomposition:
  assumes
(* We cant deduce that `e` and `e'` are valid morphisms *)
    e:  \<open>morphism B E e\<close> and
    e': \<open> morphism D F e'\<close> and
    1: \<open>pushout_diagram A B C D f g g' f'\<close> and
    "1+2":  \<open>pushout_diagram A E C F (e \<circ>\<^sub>\<rightarrow> f) g  e'' (e' \<circ>\<^sub>\<rightarrow> f')\<close> and
    "2cv": \<open>\<And>v. v \<in> V\<^bsub>B\<^esub> \<Longrightarrow> \<^bsub>e'' \<circ>\<^sub>\<rightarrow> e\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v\<close> and
    "2ce": \<open>\<And>ea. ea \<in> E\<^bsub>B\<^esub> \<Longrightarrow> \<^bsub>e'' \<circ>\<^sub>\<rightarrow> e\<^esub>\<^sub>E ea = \<^bsub>e' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E ea\<close>
  shows \<open>pushout_diagram B E D F e g' e'' e'\<close>
proof -
  interpret po1: pushout_diagram A B C D f g g' f'
    using 1 by assumption

  interpret po12: pushout_diagram A E C F \<open>e \<circ>\<^sub>\<rightarrow> f\<close> g e'' \<open>e' \<circ>\<^sub>\<rightarrow> f'\<close>
    using "1+2" by assumption

  interpret e: morphism B E e
    using e by assumption

  interpret e': morphism D F e'
    using e' by assumption

  show ?thesis
  proof
    show \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> e\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>B\<^esub>\<close> for v
      using "2cv"[OF that] by assumption
  next
    show \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> e\<^esub>\<^sub>E ea = \<^bsub>e' \<circ>\<^sub>\<rightarrow> g'\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>B\<^esub>\<close> for ea
      using "2ce"[OF that] by assumption
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph F) X xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e) \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph F)\<close>
      if \<open>graph X\<close>
       \<open>morphism (to_ngraph E) X h\<close>
       \<open>morphism (to_ngraph D) X y\<close>
       \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v\<close>
       \<open>\<forall>ea\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea\<close>
     for X :: "('c,'d) ngraph" and h y
    proof -
      interpret X: graph X
        using \<open>graph X\<close> by assumption

      interpret nE: graph \<open>to_ngraph E\<close>
        using graph_ngraph_corres_iff  po12.b.H.graph_axioms
        by blast 

      interpret nD: graph \<open>to_ngraph D\<close>
        using graph_ngraph_corres_iff po1.f.H.graph_axioms by blast

      interpret h: morphism \<open>to_ngraph E\<close> X h
        using \<open>morphism (to_ngraph E) X h\<close> by assumption

      interpret y: morphism \<open>to_ngraph D\<close> X y
        using \<open>morphism (to_ngraph D) X y\<close> by assumption

      interpret yf': morphism \<open>to_ngraph C\<close> X \<open>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<close>
        using y.morphism_axioms morph_eq_nmorph_iff po1.g.morphism_axioms wf_morph_comp by blast

      
      have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close>
      proof 
        have \<open>\<^bsub>to_nmorph g' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph A\<^esub>\<close> for v
          using that po1.node_commutativity comp_lift_node 
          by blast

        thus \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph A\<^esub>\<close>for v
          using \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v\<close> 
            that
            po1.b.morph_node_range
          by (fastforce simp add: to_nmorph_dist morph_comp_def to_nmorph_def to_ngraph_def)
      qed

     have b: \<open>\<forall>ea\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close>
     proof
       have \<open>\<^bsub>to_nmorph g' \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E ea = \<^bsub>to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>to_ngraph A\<^esub>\<close> for ea
            using that po1.edge_commutativity comp_lift_edge
            by blast
  
          thus \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>to_ngraph A\<^esub>\<close>for ea
            using \<open>\<forall>ea\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea\<close>
              that
              po1.b.morph_edge_range
            by (fastforce simp add: to_nmorph_dist morph_comp_def to_nmorph_def to_ngraph_def)
     qed

      obtain x where x:\<open>morphism (to_ngraph F) X x\<close>
        and \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
        and \<open>\<And>v. v \<in> V\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea\<close>
         using po12.universal_property[OF \<open>graph X\<close> h.morphism_axioms yf'.morphism_axioms a b]
         by (simp add: to_nmorph_dist morph_assoc_edges morph_assoc_nodes) fast


(* Since (1) is a pushout, the uniqueness of y with respect to (1) implies x ◦ e = y *)
       interpret eh: morphism \<open>to_ngraph B\<close> X \<open>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<close>
         using e h.morphism_axioms morph_eq_nmorph_iff wf_morph_comp by blast

       have a': \<open>\<forall>v\<in>V\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close>
       proof 
         have \<open>\<^bsub>to_nmorph e'' \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close>
           if \<open>v \<in> V\<^bsub>to_ngraph A\<^esub>\<close> for v
           using po12.node_commutativity that 
           by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
  
         thus \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v\<close>
           if \<open> v \<in> V\<^bsub>to_ngraph A\<^esub>\<close> for v
           using 
             \<open>\<And>v. v \<in> V\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close> that
             \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
             e.morph_node_range po1.b.morph_node_range po1.c.morph_node_range
           by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def) fastforce
       qed


       have b': \<open>\<forall>ea\<in>E\<^bsub>to_ngraph A\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close>
       proof 
         have \<open>\<^bsub>to_nmorph e'' \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E ea = \<^bsub>to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close>
           if \<open>ea \<in> E\<^bsub>to_ngraph A\<^esub>\<close> for ea
           using po12.edge_commutativity that 
           by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
  
         thus \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e \<circ>\<^sub>\<rightarrow> to_nmorph f\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f' \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E ea\<close>
           if \<open> ea \<in> E\<^bsub>to_ngraph A\<^esub>\<close> for ea
           using 
             \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea\<close> that
             \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
             e.morph_edge_range po1.b.morph_edge_range po1.c.morph_edge_range
           by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def) fastforce
       qed



(*  *)
         have a'': \<open>morphism (to_ngraph D) X y \<and>
                    (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v) \<and>
                    (\<forall>ea\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea) \<and> 
                    (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v) \<and> 
                    (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e)\<close>
           by (simp add: \<open>\<forall>ea\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v\<close> y.morphism_axioms)
    
         have b'': \<open>morphism (to_ngraph D) X (x \<circ>\<^sub>\<rightarrow> to_nmorph e') \<and>
                      (\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v) \<and>
                      (\<forall>ea\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea) \<and>
                      (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v) \<and> 
                      (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
           show xe': \<open>morphism (to_ngraph D) X (x \<circ>\<^sub>\<rightarrow> to_nmorph e')\<close>
             using e' morph_eq_nmorph_iff wf_morph_comp x
             by blast
         next
           show \<open>\<forall>v\<in>V\<^bsub>to_ngraph B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>V v = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>V v\<close>
             using \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> "2cv"  e.morph_node_range
             by (fastforce simp add: morph_comp_def to_ngraph_def to_nmorph_def)
         next
           show \<open>\<forall>ea\<in>E\<^bsub>to_ngraph B\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph g'\<^esub>\<^sub>E ea = \<^bsub>h \<circ>\<^sub>\<rightarrow> to_nmorph e\<^esub>\<^sub>E ea\<close>
             using \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close> "2ce"  e.morph_edge_range
             by (fastforce simp add: morph_comp_def to_ngraph_def to_nmorph_def)
         next
           show \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close>
             using \<open>\<And>v. v \<in> V\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close>
             by simp
         next
           show \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e\<close>
             using \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea\<close> 
             by simp
         qed


         have uniq: \<open>(\<forall>e\<in>E\<^bsub>to_ngraph F\<^esub>. \<^bsub>x'\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph F\<^esub>. \<^bsub>x'\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
           if \<open>morphism (to_ngraph F) X x'\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
            for x'
         proof -
           have a''': \<open>morphism (to_ngraph F) X x \<and>
                      (\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and>
                      (\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e) \<and> 
                      (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v) \<and> 
                      (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e)\<close>
           proof (intro conjI)
             show \<open>morphism (to_ngraph F) X x\<close>
               by (simp add: x)
           next
             show \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
               using \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> 
               by simp
           next
             show \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
               using \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
               by simp
           next
             show \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close>
               by (simp add: to_nmorph_dist \<open>\<And>v. v \<in> V\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close> morph_assoc_nodes)
           next
             show \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e\<close>
               by (simp add: to_nmorph_dist \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph C\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e' \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E ea\<close> morph_assoc_edges)
           qed



           interpret nf': morphism \<open>to_ngraph C\<close> \<open>to_ngraph D\<close> \<open>to_nmorph f'\<close>
             using po1.g.morphism_axioms morph_eq_nmorph_iff
             by blast

           have b''': \<open>morphism (to_ngraph F) X x' \<and>
                    (\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and>
                    (\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e) \<and> 
                    (\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v) \<and> 
                    (\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e)\<close>
           proof (intro conjI)
             show \<open>morphism (to_ngraph F) X x'\<close>
               by (simp add: that(1))
           next
             show \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
               using that(2) by simp
           next
             show \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
               using that(3) by simp
           next
             show \<open>\<forall>v\<in>V\<^bsub>to_ngraph C\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>V v\<close>
               using  \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> nf'.morph_node_range 
               by (simp add: to_nmorph_dist) (simp add: morph_comp_def)
           
               
           next
             show \<open>\<forall>e\<in>E\<^bsub>to_ngraph C\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph (e' \<circ>\<^sub>\<rightarrow> f')\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph f'\<^esub>\<^sub>E e\<close>
               using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>x' \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> nf'.morph_edge_range 
               by (simp add: to_nmorph_dist) (simp add: morph_comp_def)
           qed

           show ?thesis
           using ex_eq[OF po12.universal_property[OF \<open>graph X\<close> h.morphism_axioms yf'.morphism_axioms a b] a''' b''']
           by simp
       qed


       show ?thesis
       proof (rule_tac x = x in exI, intro conjI)
         show \<open>morphism (to_ngraph F) X x\<close>
           using x by assumption
       next
         show \<open>\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
           using \<open>\<And>v. v \<in> V\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
           by simp
       next
         show \<open>\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
           using \<open>\<And>ea. ea \<in> E\<^bsub>to_ngraph E\<^esub> \<Longrightarrow> \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
           by simp
       next
         show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
           using that ex_eq[OF po1.universal_property[OF \<open>graph X\<close> eh.morphism_axioms yf'.morphism_axioms a' b'], OF a'' b'']
           by simp
       next
         show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
           using that ex_eq[OF po1.universal_property[OF \<open>graph X\<close> eh.morphism_axioms yf'.morphism_axioms a' b'], OF a'' b'']
           by simp
       next
         show \<open>\<forall>ya. morphism (to_ngraph F) X ya \<and>
         (\<forall>v\<in>V\<^bsub>to_ngraph E\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and>
         (\<forall>e\<in>E\<^bsub>to_ngraph E\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph e''\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e) \<and>
         (\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
         (\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph e'\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<longrightarrow>
         (\<forall>e\<in>E\<^bsub>to_ngraph F\<^esub>. \<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph F\<^esub>. \<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
           using uniq
           by simp       
       qed
     qed
   qed
 qed


end