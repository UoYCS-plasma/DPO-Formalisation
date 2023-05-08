theory Gluing
  imports Morphism Pushout PullbackConstruction
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


definition H where \<open>H \<equiv> \<lparr>nodes=V,edges=E,source=s,target=t,node_label=l,edge_label=m\<rparr>\<close>

sublocale h: graph H
proof
  show \<open>finite V\<^bsub>H\<^esub>\<close>
    by (simp add: H_def d.H.finite_nodes r.H.finite_nodes)
next
  show \<open>finite E\<^bsub>H\<^esub>\<close>
    by (simp add: H_def d.H.finite_edges r.H.finite_edges)
next
  show \<open>s\<^bsub>H\<^esub> e \<in> V\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
  proof (cases e)
    case (Inl a)
    then show ?thesis 
      using d.H.source_integrity that 
      by (auto simp add: H_def)
  next
    case (Inr b)
    then show ?thesis
      using inv_into_into d.morph_node_range graph.source_integrity r.H.graph_axioms that r.inj_nodes
      by (fastforce simp add: H_def)
  qed
next
  show \<open>t\<^bsub>H\<^esub> e \<in> V\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
  proof (cases e)
    case (Inl a)
    then show ?thesis 
      using d.H.target_integrity that 
      by (auto simp add: H_def)
  next
    case (Inr b)
    then show ?thesis
      using inv_into_into d.morph_node_range graph.target_integrity r.H.graph_axioms that r.inj_nodes
      by (fastforce simp add: H_def)
  qed
qed

definition h where 
\<open>h \<equiv> \<lparr>node_map = \<lambda>v. if v \<in> V\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>K\<^esub> then Inr v else Inl (\<^bsub>d\<^esub>\<^sub>V ((inv_into V\<^bsub>K\<^esub> \<^bsub>b\<^esub>\<^sub>V) v)),
      edge_map = \<lambda>e. if e \<in> E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>K\<^esub> then Inr e else Inl (\<^bsub>d\<^esub>\<^sub>E ((inv_into E\<^bsub>K\<^esub> \<^bsub>b\<^esub>\<^sub>E) e))\<rparr>\<close>

sublocale inc_h: injective_morphism R H h
proof
  show \<open>\<^bsub>h\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
    using d.morph_edge_range r.inj_edges that 
    by (auto simp add: h_def H_def)
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^esub>\<close> if \<open>v \<in> V\<^bsub>R\<^esub>\<close> for v
    using d.morph_node_range r.inj_nodes that by (auto simp add: h_def H_def)
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V (s\<^bsub>R\<^esub> e) = s\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
  proof (cases \<open>(s\<^bsub>R\<^esub> e) \<in> \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>)
    case True
    then show ?thesis
      using
        morphism.source_preserve[OF  d.morphism_axioms] graph.source_integrity[OF  d.G.graph_axioms ]r.source_preserve that
        inv_into_f_f[OF r.inj_edges] inv_into_f_f[OF r.inj_nodes]
      by (auto simp add: h_def H_def) metis
  next
    case False
    then show ?thesis
      using d.G.source_integrity image_iff r.H.source_integrity r.source_preserve that 
      by (fastforce simp add: h_def H_def)
  qed
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V (t\<^bsub>R\<^esub> e) = t\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
  proof (cases \<open>e \<in> E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close>)
    case True
    then show ?thesis 
      by (simp add: h_def H_def graph.target_integrity r.H.graph_axioms)
  next
    case False
    then show ?thesis 
      using
        morphism.target_preserve[OF d.morphism_axioms] graph.target_integrity[OF d.G.graph_axioms]
        r.target_preserve that
        inv_into_f_f[OF r.inj_edges] inv_into_f_f[OF r.inj_nodes]
      by (auto simp: h_def H_def iff: image_iff) metis+
    qed
next
  show \<open>l\<^bsub>R\<^esub> v = l\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>R\<^esub>\<close> for v
    using d.label_preserve r.inj_nodes r.label_preserve that by (force simp: h_def H_def)
next
  show \<open>m\<^bsub>R\<^esub> e = m\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
    using d.mark_preserve r.inj_edges r.mark_preserve that by (force simp: h_def H_def)
next
  show \<open>inj_on \<^bsub>h\<^esub>\<^sub>V V\<^bsub>R\<^esub>\<close>
    using d.inj_nodes r.inj_nodes 
    by (fastforce simp: inj_on_def h_def H_def)
next
  show \<open>inj_on \<^bsub>h\<^esub>\<^sub>E E\<^bsub>R\<^esub>\<close>
    using d.inj_edges r.inj_edges 
    by (fastforce simp: inj_on_def h_def H_def)
qed

definition c :: "('e, 'e + 'g, 'f, 'f + 'h) pre_morph" where 
\<open>c \<equiv> \<lparr>node_map = Inl, edge_map = Inl\<rparr>\<close>


sublocale inj_c: injective_morphism D H c
proof
  show \<open>\<^bsub>c\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by (simp add: c_def H_def)
next
  show \<open>\<^bsub>c\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^esub>\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
    using that by (simp add: c_def H_def)
next
  show \<open>\<^bsub>c\<^esub>\<^sub>V (s\<^bsub>D\<^esub> e) =s\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by (simp add: c_def H_def)
next
  show \<open>\<^bsub>c\<^esub>\<^sub>V (t\<^bsub>D\<^esub> e) =t\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by (simp add: c_def H_def)
next
  show \<open>l\<^bsub>D\<^esub> v = l\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
    using that by (simp add: c_def H_def)
next
  show \<open>m\<^bsub>D\<^esub> e = m\<^bsub>H\<^esub> (\<^bsub>c\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
    using that by (simp add: c_def H_def)
next
  show \<open>inj_on \<^bsub>c\<^esub>\<^sub>V V\<^bsub>D\<^esub>\<close>
    by (simp add: c_def H_def)
next
  show \<open>inj_on \<^bsub>c\<^esub>\<^sub>E E\<^bsub>D\<^esub>\<close>
    by (simp add: c_def H_def)
qed

sublocale po: pushout_diagram K R D H b d h c
proof
  show \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>K\<^esub>\<close> for v
    using r.inj_nodes that 
    by (simp add: morph_comp_def h_def c_def)
next
  show \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    using r.inj_edges that 
    by (simp add: morph_comp_def h_def c_def)
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
            by (auto simp add: u_def to_ngraph_def H_def)
        next
          case (Inr b)
          then show ?thesis
            using that morphism.morph_edge_range[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (auto simp add: u_def to_ngraph_def H_def)
        qed
      next
        show \<open>\<^bsub>u\<^esub>\<^sub>V v \<in> V\<^bsub>D'\<^esub>\<close> if \<open>v \<in> V\<^bsub>to_ngraph H\<^esub>\<close> for v
        proof (cases \<open>from_nat v :: 'e + 'g\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.morph_node_range[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (auto simp add: u_def to_ngraph_def H_def)
        next
          case (Inr b)
          then show ?thesis
            using that morphism.morph_node_range[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (auto simp add: u_def to_ngraph_def H_def)
        qed
      next
        show \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>to_ngraph H\<^esub> e) = s\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> for e
        proof (cases \<open>from_nat e :: 'f + 'h\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.source_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def H_def)
        next
          case (Inr ba)      
          then show ?thesis
            using 
              that morphism.source_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>V v\<close> 
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>E e\<close> 
              r.inj_nodes
            by(force simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def H_def)
        qed
      next
        show \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>to_ngraph H\<^esub> e) = t\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> for e
        proof (cases \<open>from_nat e :: 'f + 'h\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.target_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def H_def)
        next
          case (Inr ba)      
          then show ?thesis
            using 
              that morphism.target_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>V v\<close> 
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph d\<^esub>\<^sub>E e\<close> 
              r.inj_nodes
            by(force simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def H_def)
        qed
      next
        show \<open>l\<^bsub>to_ngraph H\<^esub> v = l\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>to_ngraph H\<^esub>\<close> for v
        proof (cases \<open>from_nat v :: 'e + 'g\<close>)
          case (Inl a)
          then show ?thesis 
            using that morphism.label_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def H_def)
        next
          case (Inr b)
          then show ?thesis 
            using that morphism.label_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (force simp add: u_def to_ngraph_def H_def)
        qed
      next
        show \<open>m\<^bsub>to_ngraph H\<^esub> e = m\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> for e
        proof (cases \<open>from_nat e :: 'f + 'h\<close>)
          case (Inl a)
          then show ?thesis
            using that morphism.mark_preserve[OF \<open>morphism (to_ngraph D) D' y\<close>]
            by (force simp add: u_def to_ngraph_def H_def)
        next
          case (Inr b)
          then show ?thesis
            using that morphism.mark_preserve[OF \<open>morphism (to_ngraph R) D' x\<close>]
            by (force simp add: u_def to_ngraph_def H_def)
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
        by (force simp add: morph_comp_def u_def r.inj_nodes to_nmorph_def to_ngraph_def h_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>to_ngraph R\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
        using that
        by (force simp add: morph_comp_def u_def r.inj_edges to_nmorph_def to_ngraph_def h_def)
    next
      show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c \<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          by (auto simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def c_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
        by (auto simp add: u_def to_ngraph_def to_nmorph_def morph_comp_def c_def)
    next
      show \<open>\<forall>ya. morphism (to_ngraph H) D' ya \<and>
       (\<forall>v\<in>V\<^bsub>to_ngraph R\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
       (\<forall>e\<in>E\<^bsub>to_ngraph R\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
       (\<forall>v\<in>V\<^bsub>to_ngraph D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e::nat\<in>E\<^bsub>to_ngraph D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<longrightarrow>
       (\<forall>e\<in>E\<^bsub>to_ngraph H\<^esub>. \<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e) \<and>
       (\<forall>v\<in>V\<^bsub>to_ngraph H\<^esub>. \<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v)\<close>
        by (auto simp add: u_def   to_ngraph_def to_nmorph_def morph_comp_def h_def c_def H_def)
    qed
  qed
qed


 (* reduced chain  condition.
  Definition 1: https://doi.org/10.1002/mana.19790910111
*)


lemma reduced_chain_condition_nodes:
  fixes x y
  assumes
    \<open>x \<in> V\<^bsub>R\<^esub>\<close>
and \<open>y \<in> V\<^bsub>D\<^esub>\<close>
and \<open>\<^bsub>h\<^esub>\<^sub>V x = \<^bsub>c\<^esub>\<^sub>V y\<close>
shows \<open>\<exists>a \<in> V\<^bsub>K\<^esub>. (\<^bsub>b\<^esub>\<^sub>V a = x \<and> \<^bsub>d\<^esub>\<^sub>V a = y)\<close>
  using assms  Inr_Inl_False image_iff Inl_inject image_iff po.node_commutativity
  unfolding h_def c_def morph_comp_def
  apply (auto simp add: c_def h_def morph_comp_def )
  using assms  Inr_Inl_False image_iff Inl_inject image_iff po.node_commutativity
  using inv_into_f_f r.injective_morphism_axioms
  by (smt (verit, del_insts) Inl_inject Inr_Inl_False image_iff)

lemma reduced_chain_condition_edges:
  fixes x y
  assumes
    \<open>x \<in> E\<^bsub>R\<^esub>\<close>
and \<open>y \<in> E\<^bsub>D\<^esub>\<close>
and \<open>\<^bsub>h\<^esub>\<^sub>E x = \<^bsub>c\<^esub>\<^sub>E y\<close>
shows \<open>\<exists>a \<in> E\<^bsub>K\<^esub>. (\<^bsub>b\<^esub>\<^sub>E a = x \<and> \<^bsub>d\<^esub>\<^sub>E a = y)\<close>
  using assms  Inr_Inl_False image_iff Inl_inject image_iff po.edge_commutativity
  unfolding h_def c_def morph_comp_def
  apply auto
  by (smt (verit, del_insts) Inl_inject Inr_Inl_False image_iff)


lemma pushout_pullback_inj:
 shows \<open>pullback_diagram K R D H b d h c\<close>
proof -
  interpret pb: pullback_construction R H D h c ..

  obtain u where \<open>morphism K pb.A u\<close>
    \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close>
    \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>d\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>d\<^esub>\<^sub>E e\<close>
    using pb.pb.universal_property_exist_gen[OF d.G.graph_axioms d.morphism_axioms r.morphism_axioms
        po.node_commutativity po.edge_commutativity]
    by fast

  interpret morphism K pb.A u
    using \<open>morphism K pb.A u\<close> by assumption

  interpret u: bijective_morphism K pb.A u
  proof (intro inj_surj_morph_is_bijI)
    show \<open>injective_morphism K pb.A u\<close>
    proof
      show \<open>inj_on \<^bsub>u\<^esub>\<^sub>V V\<^bsub>K\<^esub>\<close>
        using \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> r.inj_nodes 
        by (simp add: morph_comp_def inj_on_def) metis
    next
      show \<open>inj_on \<^bsub>u\<^esub>\<^sub>E E\<^bsub>K\<^esub>\<close>
        using \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close> r.inj_edges
        by (simp add: morph_comp_def inj_on_def) metis
    qed
  next
    show \<open>surjective_morphism K pb.A u\<close>
    proof
      show \<open>\<exists>v'\<in>V\<^bsub>K\<^esub>. \<^bsub>u\<^esub>\<^sub>V v' = v\<close> if \<open>v \<in> V\<^bsub>pb.A\<^esub>\<close> for v
      proof -
        have *: \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>V v\<close>
          using that pb.pb.node_commutativity by blast

        obtain z where \<open>z \<in> V\<^bsub>K\<^esub>\<close> 
          and \<open>\<^bsub>b\<^esub>\<^sub>V z = \<^bsub>pb.b\<^esub>\<^sub>V v\<close> 
          and \<open>\<^bsub>d\<^esub>\<^sub>V z = \<^bsub>pb.c\<^esub>\<^sub>V v\<close> 
          using r.inj_nodes * po.node_commutativity \<open>v \<in> V\<^bsub>pb.A\<^esub>\<close> 
            reduced_chain_condition_nodes
            d.inj_nodes d.morph_node_range inc_h.inj_nodes r.morph_node_range
          by (auto simp add: morph_comp_def pb.A_def pb.b_def pb.c_def) (metis inj_onD)

        have \<open>\<^bsub>u\<^esub>\<^sub>V z = v\<close>
          using  pb.pb.node_commutativity
            \<open>\<^bsub>b\<^esub>\<^sub>V z = \<^bsub>pb.b\<^esub>\<^sub>V v\<close>  \<open>\<^bsub>d\<^esub>\<^sub>V z = \<^bsub>pb.c\<^esub>\<^sub>V v\<close>
            \<open>v \<in> V\<^bsub>pb.A\<^esub>\<close> \<open>z \<in> V\<^bsub>K\<^esub>\<close>
            \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> 
            \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>d\<^esub>\<^sub>V v\<close>
          by (auto simp add: morph_comp_def pb.b_def pb.c_def iff: prod_eq_iff)
       
        thus ?thesis
          using \<open>z \<in> V\<^bsub>K\<^esub>\<close>
          by blast
      qed
    next
      show \<open>\<exists>e'\<in>E\<^bsub>K\<^esub>. \<^bsub>u\<^esub>\<^sub>E e' = e \<close> if \<open>e \<in> E\<^bsub>pb.A\<^esub>\<close> for e
      proof -
        have *: \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>E e\<close>
          using that pb.pb.edge_commutativity by blast

        obtain z where \<open>z \<in> E\<^bsub>K\<^esub>\<close> 
          and \<open>\<^bsub>b\<^esub>\<^sub>E z = \<^bsub>pb.b\<^esub>\<^sub>E e\<close> 
          and \<open>\<^bsub>d\<^esub>\<^sub>E z = \<^bsub>pb.c\<^esub>\<^sub>E e\<close> 
          using r.inj_edges * po.edge_commutativity \<open>e \<in> E\<^bsub>pb.A\<^esub>\<close> 
            reduced_chain_condition_edges
            d.inj_edges d.morph_edge_range inc_h.inj_edges r.morph_edge_range
          by (auto simp add: morph_comp_def pb.A_def pb.b_def pb.c_def) (metis inj_onD)

        have \<open>\<^bsub>u\<^esub>\<^sub>E z = e\<close>
          using  pb.pb.edge_commutativity
            \<open>\<^bsub>b\<^esub>\<^sub>E z = \<^bsub>pb.b\<^esub>\<^sub>E e\<close>  \<open>\<^bsub>d\<^esub>\<^sub>E z = \<^bsub>pb.c\<^esub>\<^sub>E e\<close>
            \<open>e \<in> E\<^bsub>pb.A\<^esub>\<close> \<open>z \<in> E\<^bsub>K\<^esub>\<close>
            \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close> 
            \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>d\<^esub>\<^sub>E e\<close>
          by (auto simp add: morph_comp_def pb.b_def pb.c_def iff: prod_eq_iff)
       
        thus ?thesis
          using \<open>z \<in> E\<^bsub>K\<^esub>\<close>
          by blast
    qed
  qed
qed

  show ?thesis
    using pb.pb.uniqueness_pb[OF d.G.graph_axioms r.morphism_axioms d.morphism_axioms]
     \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>d\<^esub>\<^sub>E e\<close> 
     \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>d\<^esub>\<^sub>V v\<close>
     u.bijective_morphism_axioms
    by blast
qed


lemma rosen_213_nodes:
  fixes x y
  assumes \<open>x \<in> V\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>V ` V\<^bsub>k\<^esub>\<close>
    and   \<open>y \<in> V\<^bsub>R\<^esub>\<close>
    and   \<open>\<^bsub>h\<^esub>\<^sub>V x = \<^bsub>h\<^esub>\<^sub>V y\<close>
  shows   \<open>x = y\<close>
  using assms  inc_h.inj_nodes
  by (fastforce simp add: h_def dest: inj_onD)

lemma rosen_213_edges:
  fixes x y
  assumes \<open>x \<in> E\<^bsub>R\<^esub> - \<^bsub>b\<^esub>\<^sub>E ` E\<^bsub>k\<^esub>\<close>
    and   \<open>y \<in> E\<^bsub>R\<^esub>\<close>
    and   \<open>\<^bsub>h\<^esub>\<^sub>E x = \<^bsub>h\<^esub>\<^sub>E y\<close>
  shows   \<open>x = y\<close>
  using assms  inc_h.inj_edges
  by (fastforce simp add: h_def dest: inj_onD)


end


context pushout_diagram 
begin

lemma reduced_chain_condition_nodes:
  fixes x y
  assumes 
    \<open>injective_morphism A B b\<close>
    \<open>injective_morphism A C c\<close>
    \<open>x \<in> V\<^bsub>B\<^esub>\<close>
    \<open>y \<in> V\<^bsub>C\<^esub>\<close>
    \<open>\<^bsub>f\<^esub>\<^sub>V x = \<^bsub>g\<^esub>\<^sub>V y\<close>
  shows \<open>\<exists>a \<in> V\<^bsub>A\<^esub>. (\<^bsub>b\<^esub>\<^sub>V a = x \<and> \<^bsub>c\<^esub>\<^sub>V a = y)\<close>
proof -
  interpret b: injective_morphism A B b
    using \<open>injective_morphism A B b\<close> by assumption
  interpret c: injective_morphism A C c
    using \<open>injective_morphism A C c\<close> by assumption

  interpret g: gluing A C B c b  ..

  obtain u where \<open>bijective_morphism D g.H u\<close>
    and \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>g.h\<^esub>\<^sub>V v\<close>
     \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>g.h\<^esub>\<^sub>E e\<close>
     \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g.c\<^esub>\<^sub>V v\<close>
     \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g.c\<^esub>\<^sub>E e\<close>
    using g.po.pushout_diagram_axioms uniqueness_po[OF g.h.graph_axioms g.inc_h.morphism_axioms g.inj_c.morphism_axioms]
    by fast

  have \<open>\<^bsub>g.h\<^esub>\<^sub>V x = \<^bsub>g.c\<^esub>\<^sub>V y\<close>
    using
      \<open>\<^bsub>f\<^esub>\<^sub>V x = \<^bsub>g\<^esub>\<^sub>V y\<close>
      \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>g.h\<^esub>\<^sub>V v\<close>
      \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g.c\<^esub>\<^sub>V v\<close>
      assms
    by (auto simp add: morph_comp_def)
    

  show ?thesis
    using g.reduced_chain_condition_nodes[OF \<open> x \<in> V\<^bsub>B\<^esub>\<close>  \<open>y \<in> V\<^bsub>C\<^esub>\<close> \<open>\<^bsub>g.h\<^esub>\<^sub>V x = \<^bsub>g.c\<^esub>\<^sub>V y\<close>]
    by assumption
qed

lemma reduced_chain_condition_edges:
  fixes x y
  assumes 
    \<open>injective_morphism A B b\<close>
    \<open>injective_morphism A C c\<close>
    \<open>x \<in> E\<^bsub>B\<^esub>\<close>
    \<open>y \<in> E\<^bsub>C\<^esub>\<close>
    \<open>\<^bsub>f\<^esub>\<^sub>E x = \<^bsub>g\<^esub>\<^sub>E y\<close>
  shows \<open>\<exists>a \<in> E\<^bsub>A\<^esub>. (\<^bsub>b\<^esub>\<^sub>E a = x \<and> \<^bsub>c\<^esub>\<^sub>E a = y)\<close>
proof -
  interpret b: injective_morphism A B b
    using \<open>injective_morphism A B b\<close> by assumption
  interpret c: injective_morphism A C c
    using \<open>injective_morphism A C c\<close> by assumption

  interpret g: gluing A C B c b  ..

  obtain u where \<open>bijective_morphism D g.H u\<close>
    and \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>g.h\<^esub>\<^sub>V v\<close>
     \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>g.h\<^esub>\<^sub>E e\<close>
     \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>g.c\<^esub>\<^sub>V v\<close>
     \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g.c\<^esub>\<^sub>E e\<close>
    using g.po.pushout_diagram_axioms uniqueness_po[OF g.h.graph_axioms g.inc_h.morphism_axioms g.inj_c.morphism_axioms]
    by fast

  have \<open>\<^bsub>g.h\<^esub>\<^sub>E x = \<^bsub>g.c\<^esub>\<^sub>E y\<close>
    using
      \<open>\<^bsub>f\<^esub>\<^sub>E x = \<^bsub>g\<^esub>\<^sub>E y\<close>
      \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>g.h\<^esub>\<^sub>E e\<close>
      \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>g.c\<^esub>\<^sub>E e\<close>
      assms
    by (auto simp add: morph_comp_def)
    

  show ?thesis
    using g.reduced_chain_condition_edges[OF \<open>x \<in> E\<^bsub>B\<^esub>\<close>  \<open>y \<in> E\<^bsub>C\<^esub>\<close> \<open>\<^bsub>g.h\<^esub>\<^sub>E x = \<^bsub>g.c\<^esub>\<^sub>E y\<close>]
    by assumption
qed


lemma pushout_pullback_inj_b:
  assumes 
    b: \<open>injective_morphism A B b\<close> and
    c: \<open>injective_morphism A C c\<close>
  shows \<open>pullback_diagram A B C D b c f g\<close>
proof -
  interpret b: injective_morphism A B b
    using b by assumption

  interpret c: injective_morphism A C c 
    using c by assumption

  interpret g: injective_morphism C D g
    using b_inj_imp_g_inj[OF b] by assumption

  interpret pb: pullback_construction B D C f g ..
  obtain u where \<open>morphism A pb.A u\<close>
    \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close>
    \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c\<^esub>\<^sub>E e\<close>
  using pb.pb.universal_property_exist_gen[OF b.G.graph_axioms c.morphism_axioms b.morphism_axioms node_commutativity edge_commutativity]
  by fast

  interpret morphism A pb.A u
    using \<open>morphism A pb.A u\<close> by assumption

  interpret u: bijective_morphism A pb.A u
  proof (intro inj_surj_morph_is_bijI)
    show \<open>injective_morphism A pb.A u\<close>
    proof
      show \<open>inj_on \<^bsub>u\<^esub>\<^sub>V V\<^bsub>A\<^esub>\<close>
        using \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> b.inj_nodes 
        by (simp add: morph_comp_def inj_on_def) metis
    next
      show \<open>inj_on \<^bsub>u\<^esub>\<^sub>E E\<^bsub>A\<^esub>\<close>
        using \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close> b.inj_edges
        by (simp add: morph_comp_def inj_on_def) metis
    qed
  next
    show \<open>surjective_morphism A pb.A u\<close>
    proof
      show \<open>\<exists>v'\<in>V\<^bsub>A\<^esub>. \<^bsub>u\<^esub>\<^sub>V v' = v\<close> if \<open>v \<in> V\<^bsub>pb.A\<^esub>\<close> for v
      proof -
        have *: \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>V v\<close>
          by (simp add:that pb.pb.node_commutativity)

        obtain z where \<open>z \<in> V\<^bsub>A\<^esub>\<close>
          and \<open>\<^bsub>b\<^esub>\<^sub>V z = \<^bsub>pb.b\<^esub>\<^sub>V v\<close> 
          and \<open>\<^bsub>c\<^esub>\<^sub>V z = \<^bsub>pb.c\<^esub>\<^sub>V v\<close> 
          using b.inj_nodes * node_commutativity \<open>v \<in> V\<^bsub>pb.A\<^esub>\<close> 
            reduced_chain_condition_nodes[OF b c] g.inj_nodes c.morph_node_range
          by (auto simp add: morph_comp_def pb.A_def pb.b_def pb.c_def) (metis inj_onD)
    

        have \<open>\<^bsub>u\<^esub>\<^sub>V z = v\<close>
          using  pb.pb.node_commutativity
            \<open>\<^bsub>b\<^esub>\<^sub>V z = \<^bsub>pb.b\<^esub>\<^sub>V v\<close>  \<open>\<^bsub>c\<^esub>\<^sub>V z = \<^bsub>pb.c\<^esub>\<^sub>V v\<close>
            \<open>v \<in> V\<^bsub>pb.A\<^esub>\<close> \<open>z \<in> V\<^bsub>A\<^esub>\<close>
            \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> 
            \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c\<^esub>\<^sub>V v\<close>
          by (auto simp add: morph_comp_def pb.b_def pb.c_def iff: prod_eq_iff)
       
        thus ?thesis
          using \<open>z \<in> V\<^bsub>A\<^esub>\<close>
          by blast
      qed
    next
      show \<open>\<exists>e'\<in>E\<^bsub>A\<^esub>. \<^bsub>u\<^esub>\<^sub>E e' = e \<close> if \<open>e \<in> E\<^bsub>pb.A\<^esub>\<close> for e
      proof -
        have *: \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>E e\<close>
          by (simp add:that pb.pb.edge_commutativity)
        
        obtain z where \<open>z \<in> E\<^bsub>A\<^esub>\<close> 
          and \<open>\<^bsub>b\<^esub>\<^sub>E z = \<^bsub>pb.b\<^esub>\<^sub>E e\<close> 
          and \<open>\<^bsub>c\<^esub>\<^sub>E z = \<^bsub>pb.c\<^esub>\<^sub>E e\<close> 
          using b.inj_edges * edge_commutativity \<open>e \<in> E\<^bsub>pb.A\<^esub>\<close> 
            reduced_chain_condition_edges[OF b c] g.inj_edges c.morph_edge_range
          by (auto simp add: morph_comp_def pb.A_def pb.b_def pb.c_def) (metis inj_onD)
    

        have \<open>\<^bsub>u\<^esub>\<^sub>E z = e\<close>
          using  pb.pb.edge_commutativity
            \<open>\<^bsub>b\<^esub>\<^sub>E z = \<^bsub>pb.b\<^esub>\<^sub>E e\<close>  \<open>\<^bsub>c\<^esub>\<^sub>E z = \<^bsub>pb.c\<^esub>\<^sub>E e\<close>
            \<open>e \<in> E\<^bsub>pb.A\<^esub>\<close> \<open>z \<in> E\<^bsub>A\<^esub>\<close>
            \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close> 
            \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c\<^esub>\<^sub>E e\<close>
          by (auto simp add: morph_comp_def pb.b_def pb.c_def iff: prod_eq_iff)
       
        thus ?thesis
          using \<open>z \<in> E\<^bsub>A\<^esub>\<close>
          by blast
      qed
    qed
  qed


  show ?thesis
    using pb.pb.uniqueness_pb[OF b.G.graph_axioms b.morphism_axioms c.morphism_axioms]
     \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>A\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>pb.b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>A\<^esub>. \<^bsub>pb.c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c\<^esub>\<^sub>V v\<close> b.G.graph_axioms b.morphism_axioms c.morphism_axioms u.bijective_morphism_axioms
    by blast
qed
end


(* Pushout characterization, https://doi.org/10.1002/mana.19790910111
  1.2 Theorem pushout characterization
 *)
lemma po_characterization:
  assumes 
    b: \<open>injective_morphism A B b\<close> and
    c: \<open>injective_morphism A C c\<close> and
    f: \<open>injective_morphism B D f\<close> and
    g: \<open>injective_morphism C D g\<close> and
    node_commutativity: \<open>\<And>v. v \<in> V\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> and
    edge_commutativity: \<open>\<And>e. e \<in> E\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> and
    reduced_chain_condition_nodes: \<open>\<And>x y. x \<in> V\<^bsub>B\<^esub> \<Longrightarrow> y \<in> V\<^bsub>C\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>V x = \<^bsub>g\<^esub>\<^sub>V y \<Longrightarrow> (\<exists>a \<in> V\<^bsub>A\<^esub>. (\<^bsub>b\<^esub>\<^sub>V a = x \<and> \<^bsub>c\<^esub>\<^sub>V a = y))\<close> and
    reduced_chain_condition_edges: \<open>\<And>x y. x \<in> E\<^bsub>B\<^esub> \<Longrightarrow> y \<in> E\<^bsub>C\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>E x = \<^bsub>g\<^esub>\<^sub>E y \<Longrightarrow> (\<exists>a \<in> E\<^bsub>A\<^esub>. (\<^bsub>b\<^esub>\<^sub>E a = x \<and> \<^bsub>c\<^esub>\<^sub>E a = y))\<close> and
    joint_surjectivity_nodes: \<open>\<And>x. x \<in> V\<^bsub>D\<^esub> \<Longrightarrow> (\<exists>v \<in> V\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>V v = x) \<or> (\<exists>v \<in> V\<^bsub>B\<^esub>. \<^bsub>f\<^esub>\<^sub>V v = x)\<close> and
    joint_surjectivity_edges: \<open>\<And>x. x \<in> E\<^bsub>D\<^esub> \<Longrightarrow> (\<exists>e \<in> E\<^bsub>C\<^esub>. \<^bsub>g\<^esub>\<^sub>E e = x) \<or> (\<exists>e \<in> E\<^bsub>B\<^esub>. \<^bsub>f\<^esub>\<^sub>E e = x)\<close>
  shows \<open>pushout_diagram A B C D b c f g\<close>
proof -
  interpret b: injective_morphism A B b using b by assumption
  interpret c: injective_morphism A C c using c by assumption
  interpret f: injective_morphism B D f using f by assumption
  interpret g: injective_morphism C D g using g by assumption

  

  interpret constr: gluing A C B c b ..

  obtain u where \<open>morphism constr.H D u\<close>
       \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.h\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.h\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
       \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.c\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.c\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
    using constr.po.universal_property_exist_gen edge_commutativity f.H.graph_axioms f.morphism_axioms g.morphism_axioms node_commutativity by blast

  interpret morphism constr.H D u
    using \<open>morphism constr.H D u\<close> by assumption
  interpret bijective_morphism constr.H D u
  proof
    show \<open>bij_betw \<^bsub>u\<^esub>\<^sub>V V\<^bsub>constr.H\<^esub> V\<^bsub>D\<^esub>\<close>
      using \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.h\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.c\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close>
      apply (auto simp add: bij_betw_def constr.H_def morph_comp_def constr.h_def constr.c_def inj_on_def) 
            apply (metis g.inj_nodes inv_into_f_f)
      using reduced_chain_condition_nodes apply fastforce
      using reduced_chain_condition_nodes apply fastforce
      apply (smt (verit) f.inj_nodes inv_into_f_f)
      using g.morph_node_range apply blast
      using f.morph_node_range apply fastforce
      using  DiffI Un_iff b.inj_nodes c.morph_node_range image_iff inv_into_f_f joint_surjectivity_nodes
      by (smt (verit, ccfv_threshold))     
  next
    show \<open>bij_betw \<^bsub>u\<^esub>\<^sub>E E\<^bsub>constr.H\<^esub> E\<^bsub>D\<^esub>\<close>
      using \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.h\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.c\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close>
      apply (auto simp add: bij_betw_def constr.H_def morph_comp_def constr.h_def constr.c_def inj_on_def) 
            apply (metis g.inj_edges inv_into_f_f)
      using reduced_chain_condition_edges apply fastforce
      using reduced_chain_condition_edges apply fastforce
      apply (smt (verit) f.inj_edges inv_into_f_f)
      using g.morph_edge_range apply blast
      using f.morph_edge_range apply fastforce
      using  DiffI Un_iff b.inj_edges c.morph_edge_range image_iff inv_into_f_f joint_surjectivity_edges
      by (smt (verit, ccfv_threshold))    
  qed


  show ?thesis
    using constr.po.uniqueness_po[OF f.H.graph_axioms f.morphism_axioms g.morphism_axioms]
    using \<open>\<forall>e\<in>E\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.h\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.c\<^esub>\<^sub>E e = \<^bsub>g\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>B\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.h\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>C\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> constr.c\<^esub>\<^sub>V v = \<^bsub>g\<^esub>\<^sub>V v\<close> 
      bijective_morphism_axioms by blast
qed
  

context pushout_diagram 
begin

theorem uniqueness_pc:
  fixes C' c' g'
  assumes 
    b: \<open>injective_morphism A B b\<close> and
    c: \<open>injective_morphism A C c\<close> and

    C': \<open>graph C'\<close> and
    c': \<open>injective_morphism A C' c'\<close> and
    g': \<open>morphism C' D g'\<close>
  shows \<open>pushout_diagram A B C' D b c' f g' \<longrightarrow> (\<exists>u. bijective_morphism C C' u)\<close>
proof 
  show \<open>\<exists>u. bijective_morphism C C' u\<close>
    if \<open>pushout_diagram A B C' D b c' f g'\<close>
  proof -
    interpret b: injective_morphism A B b
      using b by assumption

    interpret c: injective_morphism A C c
      using c by assumption

    (* front left *)
    interpret po2: pushout_diagram A B C' D b c' f g'
      using that by assumption

    (* front right *)      
    interpret fr: pullback_construction C D C' g g' ..

    (* bottom face *)
    interpret po1: pushout_diagram A B C D b c f g
      by (simp add: pushout_diagram_axioms)

    (* back left *)
    interpret bt: pullback_diagram A A A B idM idM b b
      using fun_algrtr_4_7_2[OF b] by assumption



    (* back right *)
    interpret pb_frontleft: pullback_diagram A B C' D b c' f g'
      using po2.pushout_pullback_inj_b[OF b c'] by assumption

    (* frontleft has to be flipped *)
    interpret backside: pullback_diagram A C' A D \<open>c' \<circ>\<^sub>\<rightarrow> idM\<close> idM g' \<open>f \<circ>\<^sub>\<rightarrow> b\<close>
      using pullback_composition[OF bt.pullback_diagram_axioms pb_frontleft.flip_diagram]
      by assumption

    define h where \<open>h \<equiv> \<lparr>node_map = \<lambda>v. (\<^bsub>c\<^esub>\<^sub>V v, \<^bsub>c'\<^esub>\<^sub>V v), edge_map = \<lambda>e. (\<^bsub>c\<^esub>\<^sub>E e, \<^bsub>c'\<^esub>\<^sub>E e)\<rparr>\<close>
    interpret h: morphism A fr.A h
    proof
      show \<open>\<^bsub>h\<^esub>\<^sub>E e \<in> E\<^bsub>fr.A\<^esub>\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
        using that fr.pb.edge_commutativity c.morph_edge_range edge_commutativity po2.edge_commutativity po2.c.morph_edge_range
        by (simp add: fr.A_def h_def fr.b_def morph_comp_def fr.c_def)
    next
      show \<open>\<^bsub>h\<^esub>\<^sub>V v \<in> V\<^bsub>fr.A\<^esub>\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
        using that fr.pb.node_commutativity c.morph_node_range node_commutativity po2.node_commutativity po2.c.morph_node_range
        by (simp add: fr.A_def h_def fr.b_def morph_comp_def fr.c_def)
    next
      show \<open>\<^bsub>h\<^esub>\<^sub>V (s\<^bsub>A\<^esub> e) = s\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
        using that
        by (simp add: c.source_preserve po2.c.source_preserve fr.A_def h_def)
    next
      show \<open>\<^bsub>h\<^esub>\<^sub>V (t\<^bsub>A\<^esub> e) = t\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
        using that
        by (simp add: c.target_preserve po2.c.target_preserve fr.A_def h_def)
    next
      show \<open>l\<^bsub>A\<^esub> v = l\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
        using that
        by (simp add: fr.A_def h_def c.label_preserve)
    next
      show \<open>m\<^bsub>A\<^esub> e = m\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
        using that
        by (simp add: fr.A_def h_def c.mark_preserve)
    qed

    (*  k: U \<rightarrow> C' = fr.c*)
(* top square commutativity *)
    have a: \<open>\<^bsub>c' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      using that
      by (simp add: h_def fr.c_def morph_comp_def)

    have b: \<open>\<^bsub>c' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
      using that
      by (simp add: h_def fr.c_def morph_comp_def)

(* bottom square commutes is assumption *)
    have \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      using node_commutativity that by blast


    have *: \<open>c' \<circ>\<^sub>\<rightarrow> idM = fr.c \<circ>\<^sub>\<rightarrow> h\<close>
      by (simp add: h_def fr.c_def morph_comp_def comp_def)

  
    interpret frontside: pullback_diagram A C' A D \<open>fr.c \<circ>\<^sub>\<rightarrow> h\<close> idM g' \<open>g \<circ>\<^sub>\<rightarrow> c\<close>
    proof intro_locales
      show \<open>morphism_axioms A C' (fr.c \<circ>\<^sub>\<rightarrow> h)\<close>
        using \<open>c' \<circ>\<^sub>\<rightarrow> idM = fr.c \<circ>\<^sub>\<rightarrow> h\<close> backside.b.morphism_axioms morphism.axioms(3) by auto
    next
      show \<open>morphism_axioms A D (g \<circ>\<^sub>\<rightarrow> c)\<close>
        using c.morphism_axioms g.morphism_axioms morphism_def wf_morph_comp by blast
    next
      show \<open>pullback_diagram_axioms A C' A (fr.c \<circ>\<^sub>\<rightarrow> h) idM g' (g \<circ>\<^sub>\<rightarrow> c)\<close>
      proof
        show \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> (fr.c \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
          using that backside.node_commutativity node_commutativity
          by (simp add: morph_assoc_nodes fr.c_def morph_comp_def h_def)
      next
        show \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> (fr.c \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
          using that backside.edge_commutativity edge_commutativity
          by (simp add: morph_assoc_nodes fr.c_def morph_comp_def h_def)
      next
        show \<open>Ex1M
        (\<lambda>x. morphism A' A x \<and>
             (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
             (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and>
             (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
        A'\<close> 
          if \<open>graph A'\<close> \<open>morphism A' A c'\<close> \<open>morphism A' C' b'\<close>
             \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
             \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> for A' :: "('c,'d) ngraph" and c' b'
        proof -
          interpret c': morphism A' A c'
            using \<open>morphism A' A c'\<close> by assumption

          have \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>f \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
            using that \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> backside.node_commutativity
              c'.morph_node_range h.morph_node_range
            by (simp add: morph_comp_def h_def fr.A_def)

          moreover have \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>f \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
            using that \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> backside.edge_commutativity
              c'.morph_edge_range h.morph_edge_range
            by (simp add: morph_comp_def h_def fr.A_def)


          ultimately show ?thesis
          using backside.universal_property[OF \<open>graph A'\<close> \<open>morphism A' A c'\<close> \<open>morphism A' C' b'\<close> ] *
          by auto
      qed
    qed
  qed



  interpret back_right: pullback_diagram A fr.A A C h idM fr.b c
    proof -
    have \<open>\<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      using that
      by (simp add: fr.b_def h_def morph_comp_def)
    moreover have \<open>\<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
      using that
      by (simp add: fr.b_def h_def morph_comp_def)

    ultimately show \<open>pullback_diagram A fr.A A C h idM fr.b c\<close>
        using pullback_decomposition[OF h.morphism_axioms c.morphism_axioms fr.pb.flip_diagram frontside.pullback_diagram_axioms]
        by simp
    qed


    (* top face *)
    interpret top: pushout_diagram A A fr.A C' idM h c' fr.c
    proof -
      interpret bottom: pullback_diagram A B C D b c f g
        using pushout_pullback_inj_b[OF b.injective_morphism_axioms c.injective_morphism_axioms]
        by assumption

      interpret bls: pullback_diagram A C A D \<open>c \<circ>\<^sub>\<rightarrow> idM\<close> idM g \<open>f \<circ>\<^sub>\<rightarrow> b\<close>
        using pullback_composition[OF bt.pullback_diagram_axioms bottom.flip_diagram]
        by assumption

(* righthand commutative square *)
      have a: \<open>\<^bsub>c \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
        by (simp add: fr.b_def h_def morph_comp_def)
      have b: \<open>\<^bsub>c \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
        by (simp add: fr.b_def h_def morph_comp_def)


      interpret brs: pullback_diagram A C A D \<open>fr.b \<circ>\<^sub>\<rightarrow> h\<close> idM g \<open>g' \<circ>\<^sub>\<rightarrow> c'\<close>
      proof intro_locales
        show \<open>morphism_axioms A C (fr.b \<circ>\<^sub>\<rightarrow> h)\<close>
          using fr.b.morphism_axioms h.morphism_axioms morphism_def wf_morph_comp by blast
      next
        show \<open>morphism_axioms A D (g' \<circ>\<^sub>\<rightarrow> c')\<close>
          using g' morphism.axioms(3) po2.c.morphism_axioms wf_morph_comp by blast
      next
        show \<open>pullback_diagram_axioms A C A (fr.b \<circ>\<^sub>\<rightarrow> h) idM g (g' \<circ>\<^sub>\<rightarrow> c')\<close>
        proof
          show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> (fr.b \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
            using that po2.node_commutativity bls.node_commutativity
            by (simp add: morph_comp_def morph_assoc_nodes fr.b_def h_def)
        next
          show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> (fr.b \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>E e = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
            using that po2.edge_commutativity bls.edge_commutativity
            by (simp add: morph_comp_def morph_assoc_nodes fr.b_def h_def)
        next
          show \<open>Ex1M (\<lambda>x. morphism A' A x 
                  \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) 
                  \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) 
                  \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'a\<^esub>\<^sub>V v) 
                  \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'a\<^esub>\<^sub>E e)) A'\<close>
            if \<open>graph A'\<close> \<open>morphism A' A c'a\<close> \<open>morphism A' C b'\<close> 
               \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>V v\<close>
               \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>E e\<close>
            for A' :: "('c,'d) ngraph" and c'a b'
          proof -
            interpret c'a: morphism A' A c'a
              using \<open>morphism A' A c'a\<close> by assumption

            interpret b': morphism A' C b'
              using \<open>morphism A' C b'\<close> by assumption

            have a: \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>f \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
              using that \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>V v\<close> po2.node_commutativity
              by (simp add: morph_comp_def  c'a.morph_node_range)

            have b: \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>f \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
              using that  \<open>\<And>ea. ea \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E ea = \<^bsub>g' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>E ea\<close> po2.edge_commutativity
              by (simp add: morph_comp_def  c'a.morph_edge_range)
            
            have s: \<open>(\<lambda>x. morphism A' A x \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'a\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'a\<^esub>\<^sub>E e)) = (\<lambda>x. morphism A' A x \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'a\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'a\<^esub>\<^sub>E e))\<close>
              by (simp add: morph_comp_def fr.b_def h_def)

            show  ?thesis
              using ex1m_eq_surrogate[OF s bls.universal_property[OF \<open>graph A'\<close> \<open>morphism A' A c'a\<close> \<open>morphism A' C b'\<close> a b]]
              by simp
          qed
        qed
      qed

      interpret top_pb: pullback_diagram A A fr.A C' idM h c' fr.c
        using pullback_decomposition[OF _ _ fr.pb.pullback_diagram_axioms brs.pullback_diagram_axioms]
        using "*" h.morphism_axioms po2.c.morphism_axioms pullback_diagram.flip_diagram by force

      interpret h: injective_morphism A fr.A h
      proof
        show \<open>inj_on \<^bsub>h\<^esub>\<^sub>V V\<^bsub>A\<^esub>\<close>
          using c.inj_nodes
          by (simp add: h_def inj_on_def)
      next
        show \<open>inj_on \<^bsub>h\<^esub>\<^sub>E E\<^bsub>A\<^esub>\<close>
          using c.inj_edges
          by (simp add: h_def inj_on_def)
      qed

      have a:\<open>(\<exists>v\<in>V\<^bsub>A\<^esub>. \<^bsub>c'\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>V v = x)\<close> if \<open>x \<in> V\<^bsub>C'\<^esub>\<close> for x
        using that
        apply (simp add: fr.A_def fr.c_def)
        using b.injective_morphism_axioms c' joint_surjectivity_nodes po2.g.morph_node_range po2.reduced_chain_condition_nodes by blast

      have b: \<open>(\<exists>e\<in>E\<^bsub>A\<^esub>. \<^bsub>c'\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>E e = x)\<close> if \<open>x \<in> E\<^bsub>C'\<^esub>\<close> for x
        using that
        apply (simp add: fr.A_def fr.c_def)
        using b.injective_morphism_axioms c' g' joint_surjectivity_edges morphism.morph_edge_range po2.reduced_chain_condition_edges by blast

      interpret k_inj: injective_morphism fr.A C' fr.c
        using pullback_diagram.g_inj_imp_b_inj[OF fr.pb.flip_diagram b_inj_imp_g_inj[OF b.injective_morphism_axioms]]
        by assumption

      have a': \<open>(\<exists>v\<in>V\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>A\<^esub>. \<^bsub>c'\<^esub>\<^sub>V v = x)\<close> if \<open>x \<in> V\<^bsub>C'\<^esub>\<close> for x
        using that a by auto
      have b': \<open>(\<exists>e\<in>E\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>A\<^esub>. \<^bsub>c'\<^esub>\<^sub>E e = x)\<close> if \<open>x \<in> E\<^bsub>C'\<^esub>\<close> for x
        using that b by auto 

      show \<open>pushout_diagram A A fr.A C' idM h c' fr.c\<close>
        using po_characterization[of A A idM fr.A h C' c' fr.c]
        using a' b' b.G.idm.injective_morphism_axioms c' h.injective_morphism_axioms k_inj.injective_morphism_axioms top_pb.edge_commutativity top_pb.node_commutativity top_pb.reduced_chain_condition_edges top_pb.reduced_chain_condition_nodes by fastforce
    qed


    interpret k_bij: bijective_morphism fr.A C' fr.c
      using top.b_bij_imp_g_bij[OF b.G.idm.bijective_morphism_axioms]
      by assumption

    (* here starts l *)
    interpret h: injective_morphism fr.A C fr.b
      using fr.pb.g_inj_imp_b_inj[OF po2.b_inj_imp_g_inj[OF b.injective_morphism_axioms]]
      by assumption

    interpret br: pushout_diagram A fr.A A C h idM fr.b c
    proof -
      have a: \<open>\<exists>a\<in>V\<^bsub>A\<^esub>. (\<^bsub>h\<^esub>\<^sub>V a = x \<and> \<^bsub>idM\<^esub>\<^sub>V a = y)\<close> if \<open>x \<in> V\<^bsub>fr.A\<^esub>\<close> \<open> y \<in> V\<^bsub>A\<^esub>\<close> \<open> \<^bsub>fr.b\<^esub>\<^sub>V x = \<^bsub>c\<^esub>\<^sub>V y \<close> for x y
        using back_right.reduced_chain_condition_nodes[OF that]
        by simp
      
      have b: \<open>\<exists>a\<in>E\<^bsub>A\<^esub>. (\<^bsub>h\<^esub>\<^sub>E a = x \<and> \<^bsub>idM\<^esub>\<^sub>E a = y)\<close> if \<open>x \<in> E\<^bsub>fr.A\<^esub>\<close> \<open> y \<in> E\<^bsub>A\<^esub>\<close> \<open> \<^bsub>fr.b\<^esub>\<^sub>E x = \<^bsub>c\<^esub>\<^sub>E y \<close> for x y
        using back_right.reduced_chain_condition_edges[OF that] by simp

      have cc: \<open>(\<exists>v\<in>V\<^bsub>A\<^esub>. \<^bsub>c\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>fr.A\<^esub>. \<^bsub>fr.b\<^esub>\<^sub>V v = x)\<close> if \<open>x \<in> V\<^bsub>C\<^esub> \<close> for x
        using that
        by (metis b.injective_morphism_axioms c fr.reduced_chain_condition_nodes g.morph_node_range po2.joint_surjectivity_nodes reduced_chain_condition_nodes)

      have dd: \<open>(\<exists>e\<in>E\<^bsub>A\<^esub>. \<^bsub>c\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>fr.A\<^esub>. \<^bsub>fr.b\<^esub>\<^sub>E e = x)\<close> if \<open>x \<in> E\<^bsub>C\<^esub> \<close> for x
        using that
        by (metis b.injective_morphism_axioms c fr.reduced_chain_condition_edges g.morph_edge_range po2.joint_surjectivity_edges reduced_chain_condition_edges)

      show \<open>pushout_diagram A fr.A A C h idM fr.b c\<close>
        using po_characterization[ OF back_right.g_inj_imp_b_inj[OF c] b.G.idm.injective_morphism_axioms h.injective_morphism_axioms
            c back_right.node_commutativity back_right.edge_commutativity]
        using back_right.reduced_chain_condition_nodes back_right.reduced_chain_condition_edges
        using cc dd by blast
          
    qed

    interpret l_bij: bijective_morphism fr.A C fr.b
    proof -
      interpret pushout_diagram A A fr.A C idM h c fr.b
        using br.flip_diagram by assumption

      show \<open>bijective_morphism fr.A C fr.b\<close>
        using b_bij_imp_g_bij[OF b.G.idm.bijective_morphism_axioms]
        by assumption
    qed

    show \<open>\<exists>u. bijective_morphism C C' u\<close>
    proof -
      obtain linv where linv:\<open>bijective_morphism C fr.A linv\<close>
        using l_bij.ex_inv
        by fastforce

      show ?thesis
        using bij_comp_bij_is_bij[OF linv k_bij.bijective_morphism_axioms]
        by (rule_tac x = \<open>fr.c \<circ>\<^sub>\<rightarrow> linv\<close> in exI) assumption      
    qed
  qed
qed

end (* pushout_diagram *)

end
