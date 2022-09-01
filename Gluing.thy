theory Gluing
  imports Morphism Pushout
begin

locale gluing =
  d: injective_morphism K D d +
  r: injective_morphism K R b
  for K D R d b
begin

abbreviation V where \<open>V \<equiv> Inl ` V\<^bsub>D\<^esub> \<union> Inr ` (V\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>)\<close>
abbreviation E where \<open>E \<equiv> Inl ` E\<^bsub>D\<^esub> \<union> Inr ` (E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>)\<close>

fun s where
 "s (Inl e) = Inl (s\<^bsub>D\<^esub> e)"
|"s (Inr e) = (if e \<in> (E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) \<and> (s\<^bsub>R\<^esub> e \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>) 
  then Inl (\<^bsub>d\<^esub>\<^sub>V ((inv_into V\<^bsub>K\<^esub> \<^bsub>b\<^esub>\<^sub>V) (s\<^bsub>R\<^esub> e))) else Inr (s\<^bsub>R\<^esub> e))"

fun t where
 "t (Inl e) = Inl (t\<^bsub>D\<^esub> e)"
|"t (Inr e) = (if e \<in> (E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) \<and> (t\<^bsub>R\<^esub> e \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>) 
  then Inl (\<^bsub>d\<^esub>\<^sub>V ((inv_into V\<^bsub>K\<^esub> \<^bsub>b\<^esub>\<^sub>V) (t\<^bsub>R\<^esub> e))) else Inr (t\<^bsub>R\<^esub> e))"

fun l where
  "l (Inl v) = l\<^bsub>D\<^esub> v"
| "l (Inr v) = l\<^bsub>R\<^esub> v"

fun m where
  "m (Inl v) = m\<^bsub>D\<^esub> v"
| "m (Inr v) = m\<^bsub>R\<^esub> v"


abbreviation H where \<open>H \<equiv> \<lparr>nodes=V,edges=E,source=s,target=t,node_label=l,edge_label=m\<rparr>\<close>

sublocale h: graph H
proof
  show \<open>finite V\<^bsub>H\<^esub>\<close>
    by (simp add: d.H.finite_nodes r.H.finite_nodes)
next
  show \<open>finite E\<^bsub>H\<^esub>\<close>
    by (simp add: d.H.finite_edges r.H.finite_edges)
next
  show \<open>s\<^bsub>H\<^esub> e \<in> V\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
  proof (cases e)
    case (Inl a)
    then show ?thesis 
      using d.H.source_integrity that 
      by auto
  next
    case (Inr b)
    then show ?thesis
      using inv_into_into d.morph_node_range graph.source_integrity r.H.graph_axioms that r.inj_nodes
      by fastforce
  qed
next
  show \<open>t\<^bsub>H\<^esub> e \<in> V\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
  proof (cases e)
    case (Inl a)
    then show ?thesis 
      using d.H.target_integrity that 
      by auto
  next
    case (Inr b)
    then show ?thesis
      using inv_into_into d.morph_node_range graph.target_integrity r.H.graph_axioms that r.inj_nodes
      by fastforce
  qed
qed

abbreviation h where 
\<open>h \<equiv> \<lparr>node_map = \<lambda>v. if v \<in> V\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>K\<^esub> then Inr v else Inl (\<^bsub>d\<^esub>\<^sub>V ((inv_into V\<^bsub>K\<^esub> \<^bsub>b\<^esub>\<^sub>V) v)),
      edge_map = \<lambda>e. if e \<in> E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>K\<^esub> then Inr e else Inl (\<^bsub>d\<^esub>\<^sub>E ((inv_into E\<^bsub>K\<^esub> \<^bsub>b\<^esub>\<^sub>E) e))\<rparr>\<close>

interpretation inc_h: injective_morphism R H h
proof
  show \<open>\<^bsub>h\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
    using d.morph_edge_range r.inj_edges that by auto
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^esub>\<close> if \<open>v \<in> V\<^bsub>R\<^esub>\<close> for v
    using d.morph_node_range r.inj_nodes that by auto
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V (s\<^bsub>R\<^esub> e) = s\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
  proof (cases \<open>(s\<^bsub>R\<^esub> e) \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>)
    case True
    then show ?thesis
      using
        morphism.source_preserve[OF  d.morphism_axioms] graph.source_integrity[OF  d.G.graph_axioms ]r.source_preserve that
        inv_into_f_f[OF r.inj_edges] inv_into_f_f[OF r.inj_nodes]
      by auto metis
  next
    case False
    then show ?thesis
      using d.G.source_integrity image_iff r.H.source_integrity r.source_preserve that by fastforce
  qed
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V (t\<^bsub>R\<^esub> e) = t\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
  proof (cases \<open>e \<in> E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close>)
    case True
    then show ?thesis 
      by (simp add: graph.target_integrity r.H.graph_axioms)
  next
    case False
    then show ?thesis 
      using
        morphism.target_preserve[OF d.morphism_axioms] graph.target_integrity[OF d.G.graph_axioms]
        r.target_preserve that
        inv_into_f_f[OF r.inj_edges] inv_into_f_f[OF r.inj_nodes]
      by (auto iff: image_iff) metis+
    qed
next
  show \<open>l\<^bsub>R\<^esub> v = l\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>R\<^esub>\<close> for v
    using d.label_preserve r.inj_nodes r.label_preserve that by force
next
  show \<open>m\<^bsub>R\<^esub> e = m\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
    using d.mark_preserve r.inj_edges r.mark_preserve that by force
next
  show \<open>inj_on \<^bsub>h\<^esub>\<^sub>V V\<^bsub>R\<^esub>\<close>
    using d.inj_nodes r.inj_nodes 
    by (fastforce simp: inj_on_def)
next
  show \<open>inj_on \<^bsub>h\<^esub>\<^sub>E E\<^bsub>R\<^esub>\<close>
    using d.inj_edges r.inj_edges 
    by (fastforce simp: inj_on_def)
qed

abbreviation c :: "('e, 'e + 'g, 'f, 'f + 'h) pre_morph" where 
\<open>c \<equiv> \<lparr>node_map = Inl, edge_map = Inl\<rparr>\<close>


interpretation inj_c: injective_morphism D H c
proof
  show \<open>\<^bsub>c\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>\<^bsub>c\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^esub>\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
    using that by simp
next
  show \<open>\<^bsub>c\<^esub>\<^sub>V (s\<^bsub>D\<^esub> e) =s\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>\<^bsub>c\<^esub>\<^sub>V (t\<^bsub>D\<^esub> e) =t\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>l\<^bsub>D\<^esub> v = l\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
    using that by simp
next
  show \<open>m\<^bsub>D\<^esub> e = m\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by simp
next
  show \<open>inj_on \<^bsub>c\<^esub>\<^sub>V V\<^bsub>D\<^esub>\<close>
    by simp
next
  show \<open>inj_on \<^bsub>c\<^esub>\<^sub>E E\<^bsub>D\<^esub>\<close>
    by simp
qed

sublocale po: pushout_diagram K R D H b d h c
proof
  show \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>K\<^esub>\<close> for v
    using r.inj_nodes that 
    by (simp add: morph_comp_def)
next
  show \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    using r.inj_edges that 
    by (simp add: morph_comp_def)
next
  show \<open> Ex1M
            (\<lambda>xa. morphism (to_ngraph H) D' xa \<and>
                   (\<forall>v\<in>V\<^bsub>to_ngraph R\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
                   (\<forall>e\<in>E\<^bsub>to_ngraph R\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
                   (\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
                   (\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
            (to_ngraph H)\<close>
    if \<open>graph D'\<close> \<open>morphism (to_ngraph R) D' x\<close> \<open>morphism (to_ngraph D) D' y\<close>
      \<open>\<forall>v\<in>V\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>V v\<close> 
      \<open>\<forall>e\<in>E\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>E e\<close> for D' :: "('c,'d) ngraph" and x y
  proof -
    define u where \<open>u \<equiv> 
      \<lparr> node_map = \<lambda>v. case_sum (\<^bsub>y\<^esub>\<^sub>V \<circ> to_nat ) (\<^bsub>x\<^esub>\<^sub>V \<circ> to_nat )(from_nat v :: 'e + 'g)
      , edge_map = \<lambda>e. case_sum (\<^bsub>y\<^esub>\<^sub>E \<circ> to_nat ) (\<^bsub>x\<^esub>\<^sub>E \<circ> to_nat )(from_nat e :: 'f + 'h)\<rparr>\<close>

    interpret u: morphism \<open>to_ngraph H\<close> D' u
    proof intro_locales
      show \<open>graph (to_ngraph H)\<close>
        using graph_ngraph_corres_iff h.graph_axioms by blast
    next
      show \<open>graph D'\<close>
        using that(1) by assumption
    next
      show \<open>morphism_axioms (to_ngraph H) D' u\<close>
      proof
        show \<open>\<^bsub>u\<^esub>\<^sub>E e \<in> E\<^bsub>D'\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> for e
        proof (cases \<open>from_nat e :: 'f + 'h\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.morph_edge_range[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (auto simp add: u_def to_ngraph_def)
        next
          case (Inr b)
          then show ?thesis
            using that morphism.morph_edge_range[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (auto simp add: u_def to_ngraph_def)
        qed
      next
        show \<open>\<^bsub>u\<^esub>\<^sub>V v \<in> V\<^bsub>D'\<^esub>\<close> if \<open>v \<in> V\<^bsub>to_ngraph H\<^esub>\<close> for v
        proof (cases \<open>from_nat v :: 'e + 'g\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.morph_node_range[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (auto simp add: u_def to_ngraph_def)
        next
          case (Inr b)
          then show ?thesis
            using that morphism.morph_node_range[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (auto simp add: u_def to_ngraph_def)
        qed
      next
        show \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>to_ngraph H\<^esub> e) = s\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> for e
        proof (cases \<open>from_nat e :: 'f + 'h\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.source_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def)
        next
          case (Inr ba)      
          then show ?thesis
            using 
              that morphism.source_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>V v\<close> 
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>E e\<close> 
              r.inj_nodes
            by(force simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def)
        qed
      next
        show \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>to_ngraph H\<^esub> e) = t\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> for e
        proof (cases \<open>from_nat e :: 'f + 'h\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.target_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def)
        next
          case (Inr ba)      
          then show ?thesis
            using 
              that morphism.target_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>V v\<close> 
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>E e\<close> 
              r.inj_nodes
            by(force simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def)
        qed
      next
        show \<open>l\<^bsub>to_ngraph H\<^esub> v = l\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>to_ngraph H\<^esub>\<close> for v
        proof (cases \<open>from_nat v :: 'e + 'g\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.label_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def)
        next
          case (Inr b)
          then show ?thesis 
            using that morphism.label_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (force simp add: u_def to_ngraph_def)
        qed
      next
        show \<open>m\<^bsub>to_ngraph H\<^esub> e = m\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> for e
        proof (cases \<open>from_nat e :: 'f + 'h\<close>)
          case (Inl a)
          then show ?thesis
            using that morphism.mark_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def)
        next
          case (Inr b)
          then show ?thesis
            using that morphism.mark_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (force simp add: u_def to_ngraph_def)
        qed
      qed
    qed

    show ?thesis
    proof (rule_tac x = u in exI, intro conjI)
      show \<open>morphism (to_ngraph H) D' u\<close>
        using u.morphism_axioms by assumption
    next
      show \<open>\<forall>v\<in>V\<^bsub>to_ngraph R\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
        using that
        by (force simp add: morph_comp_def u_def r.inj_nodes to_nmorph_def to_ngraph_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>to_ngraph R\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
        using that
        by (force simp add: morph_comp_def u_def r.inj_edges to_nmorph_def to_ngraph_def)
    next
      show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c \<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          by (auto simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
        by (auto simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def)
    next
      show \<open>\<forall>ya. morphism (to_ngraph H) D' ya \<and>
       (\<forall>v\<in>V\<^bsub>to_ngraph R\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
       (\<forall>e\<in>E\<^bsub>to_ngraph R\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
       (\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e::nat\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<longrightarrow>
       (\<forall>e\<in>E\<^bsub>to_ngraph H\<^esub>. \<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e) \<and>
       (\<forall>v\<in>V\<^bsub>to_ngraph H\<^esub>. \<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v)\<close>
        by (auto simp add: u_def   to_ngraph_def to_nmorph_def morph_comp_def)
    qed
  qed
qed

end


end
