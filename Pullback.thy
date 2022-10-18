theory Pullback
  imports Pushout
begin
  (* declare [[show_types]]
 *)
locale pullback_diagram =                    
  b: morphism A B b +
  c: morphism A C c +
  f: morphism B D f +
  g: morphism C D g for A B C D b c f g +
assumes
  node_commutativity: \<open>\<And>v. v \<in> V\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> and
  edge_commutativity: \<open>\<And>e. e \<in> E\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> and
  universal_property: \<open>\<lbrakk>
    graph (A' :: ('c,'d) ngraph); 
    morphism A' (to_ngraph C) c'; 
    morphism A' (to_ngraph B) b';
     \<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v;
     \<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<rbrakk> 
    \<Longrightarrow> Ex1M (\<lambda>u. morphism A' (to_ngraph A) u \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A'\<close>

begin

lemma universal_property_exist_gen:
  fixes A'
  assumes A':\<open>graph A'\<close> 
    and \<open>morphism A' C c'\<close> 
    and \<open>morphism A' B b'\<close>
    and \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
    and \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
  shows \<open>Ex1M (\<lambda>u. morphism A' A u \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A'\<close>
proof -

  interpret nA': graph \<open>to_ngraph A'\<close>
    using A' graph_ngraph_corres_iff[symmetric, of A']
    by simp

  interpret nc': morphism \<open>to_ngraph A'\<close> \<open>to_ngraph C\<close> \<open>to_nmorph c'\<close>
    using morph_eq_nmorph_iff[symmetric] assms(2)
    by blast

  interpret nb': morphism \<open>to_ngraph A'\<close> \<open>to_ngraph B\<close> \<open>to_nmorph b'\<close>
    using morph_eq_nmorph_iff[symmetric] assms(3)
    by blast


  have a: \<open>\<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph b'\<^esub>\<^sub>V v = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> to_nmorph c'\<^esub>\<^sub>V v\<close>
    if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
    using that comp_lift_node assms(4)
    by blast

  have b: \<open>\<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph b'\<^esub>\<^sub>E e = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> to_nmorph c'\<^esub>\<^sub>E e\<close>
    if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
    using that comp_lift_edge assms(5)
    by blast

  obtain u 
    where ab: \<open>morphism (to_ngraph A') (to_ngraph A) u\<close>
      and \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v\<close>
      and \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e\<close>
      and \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v\<close>
      and \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e\<close>
    using universal_property[OF nA'.graph_axioms nc'.morphism_axioms nb'.morphism_axioms a b]
    by blast

  show ?thesis
  proof (rule_tac x = \<open>(from_nmorph u) :: ('k,'a,'l,'b) pre_morph\<close> in exI, intro conjI)
    show \<open>morphism A' A (from_nmorph u)\<close>
      using ab morph_tong_tong_u_is_morph_tonm
      by blast
  next
    show \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> from_nmorph u\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close>
      using \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> from_nmorph u\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
      using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> from_nmorph u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
      using \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> from_nmorph u\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
      using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e\<close>
      by (auto simp: from_nmorph_def to_nmorph_def morph_comp_def to_ngraph_def from_ngraph_def)
  next
    show \<open>\<forall>y. morphism A' A y \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e) \<longrightarrow>
        (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>from_nmorph u\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>from_nmorph u\<^esub>\<^sub>V v)\<close>
    proof -
      have 1: \<open>Ex1M
           (\<lambda>x. morphism (to_ngraph A') (to_ngraph A) x \<and>
                 (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v) \<and>
                 (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e))
           (to_ngraph A')\<close>
        using universal_property[OF nA'.graph_axioms nc'.morphism_axioms nb'.morphism_axioms a b]
        by blast
      show ?thesis
      proof safe
        show \<open>\<^bsub>u'\<^esub>\<^sub>E e = \<^bsub>from_nmorph u\<^esub>\<^sub>E e\<close>
          if \<open>morphism A' A u'\<close> 
            and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
            and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
            and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close> 
            and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
            and \<open>e \<in> E\<^bsub>A'\<^esub>\<close>
          for e u'
        proof -
          have a: \<open>morphism (to_ngraph A') (to_ngraph A) (to_nmorph u') \<and>
             (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v) \<and>
             (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e)\<close>
            by (meson comp_lift_edge1 comp_lift_node1 morph_eq_nmorph_iff that(1) that(2) that(3) that(4) that(5))

          have b: \<open>morphism (to_ngraph A') (to_ngraph A) u \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e)\<close>
            using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v\<close> ab by blast

          have \<open>(\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph u'\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph u'\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e)\<close>
            using ex_eq[OF 1 a b] by assumption
          then have \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>u'\<^esub>\<^sub>E e = \<^bsub>from_nmorph u\<^esub>\<^sub>E e\<close>
            apply (simp add: to_nmorph_def from_nmorph_def to_ngraph_def)
            by (metis from_nat_to_nat)
          thus ?thesis
            using that
            by blast
        qed
      next
        show \<open>\<^bsub>u'\<^esub>\<^sub>V v = \<^bsub>from_nmorph u\<^esub>\<^sub>V v\<close>
          if \<open>morphism A' A u'\<close> 
            and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
            and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
            and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close> 
            and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
            and \<open>v \<in> V\<^bsub>A'\<^esub>\<close>
          for v u'
        proof -
          have a: \<open>morphism (to_ngraph A') (to_ngraph A) (to_nmorph u') \<and>
             (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v) \<and>
             (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> (to_nmorph u')\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e)\<close>
            by (meson comp_lift_edge1 comp_lift_node1 morph_eq_nmorph_iff that(1) that(2) that(3) that(4) that(5))

          have b: \<open>morphism (to_ngraph A') (to_ngraph A) u \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e)\<close>
            using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph b'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>to_nmorph c'\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph b'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>to_nmorph c'\<^esub>\<^sub>V v\<close> ab by blast

          have \<open>(\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph u'\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>to_nmorph u'\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e)\<close>
            using ex_eq[OF 1 a b] by assumption
          then have \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>u'\<^esub>\<^sub>V v = \<^bsub>from_nmorph u\<^esub>\<^sub>V v\<close>
            apply (simp add: to_nmorph_def from_nmorph_def to_ngraph_def)
            by (metis from_nat_to_nat)

          thus ?thesis
            using that
            by blast
        qed
      qed
    qed
  qed
qed

end

context pushout_diagram
begin


lemma 
  assumes \<open>injective_morphism A B b\<close>
  shows \<open>pullback_diagram A B C D b c f g\<close>
proof -
  interpret b: injective_morphism A B b
    using assms .

  show ?thesis
  proof
    show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      by (simp add: that node_commutativity)
  next
    show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
      by (simp add: that edge_commutativity)
  next
    show \<open>Ex1M
            (\<lambda>x. morphism A' (to_ngraph A) x \<and>
                  (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
                  (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A'\<close>
      if \<open>graph A'\<close> 
        and \<open>morphism A' (to_ngraph C) c'\<close> 
        and \<open>morphism A' (to_ngraph B) b'\<close>
        and \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
        and \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
      for A' :: "('c,'d) ngraph" and b' c'
    proof -
      term A
      define u :: "(nat, nat, nat, nat ) pre_morph" 
        where \<open>u \<equiv> \<lparr>node_map = \<lambda>v. if \<^bsub>b'\<^esub>\<^sub>V v \<in> V\<^bsub>to_ngraph B\<^esub> then to_nat (inv_into V\<^bsub>A\<^esub> \<^bsub>b\<^esub>\<^sub>V (from_nat v)) else v
                          ,edge_map = \<lambda>e. if \<^bsub>b'\<^esub>\<^sub>E e \<in> E\<^bsub>to_ngraph B\<^esub> then to_nat(inv_into E\<^bsub>A\<^esub> \<^bsub>b\<^esub>\<^sub>E (from_nat e)) else e\<rparr>\<close>

      show ?thesis
      proof (rule_tac x = u in exI, intro conjI)
        show \<open>morphism A' (to_ngraph A) u\<close>
          using that
          apply (auto simp add: u_def to_ngraph_def)
          sledgehammer
      using that
      sorry
end


end