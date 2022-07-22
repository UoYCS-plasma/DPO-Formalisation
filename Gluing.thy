theory Gluing
  imports Morphism Pushout
begin

locale gluing =
  d: injective_morphism K D d +
  r: injective_morphism K R r 
  for K D R d r
begin

abbreviation V where \<open>V \<equiv> Inl ` V\<^bsub>D\<^esub> \<union> Inr ` (V\<^bsub>R\<^esub> - \<^bsub>r\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>)\<close>
abbreviation E where \<open>E \<equiv> Inl ` E\<^bsub>D\<^esub> \<union> Inr ` (E\<^bsub>R\<^esub> - \<^bsub>r\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>)\<close>

fun s where
 "s (Inl e) = Inl (s\<^bsub>D\<^esub> e)"
|"s (Inr e) = (if e \<in> (E\<^bsub>R\<^esub> - \<^bsub>r\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) \<and> (s\<^bsub>R\<^esub> e \<in> \<^bsub>r\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>) 
  then Inl (\<^bsub>d\<^esub>\<^sub>V ((inv_into V\<^bsub>K\<^esub> \<^bsub>r\<^esub>\<^sub>V) (s\<^bsub>R\<^esub> e))) else Inr (s\<^bsub>R\<^esub> e))"

fun t where
 "t (Inl e) = Inl (t\<^bsub>D\<^esub> e)"
|"t (Inr e) = (if e \<in> (E\<^bsub>R\<^esub> - \<^bsub>r\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>) \<and> (t\<^bsub>R\<^esub> e \<in> \<^bsub>r\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>) 
  then Inl (\<^bsub>d\<^esub>\<^sub>V ((inv_into V\<^bsub>K\<^esub> \<^bsub>r\<^esub>\<^sub>V) (t\<^bsub>R\<^esub> e))) else Inr (t\<^bsub>R\<^esub> e))"

fun l where
  "l (Inl v) = l\<^bsub>D\<^esub> v"
| "l (Inr v) = l\<^bsub>R\<^esub> v"

fun m where
  "m (Inl v) = m\<^bsub>D\<^esub> v"
| "m (Inr v) = m\<^bsub>R\<^esub> v"


abbreviation H where \<open>H \<equiv> \<lparr>nodes=V,edges=E,source=s,target=t,label=l,mark=m\<rparr>\<close>

interpretation h: graph H
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
\<open>h \<equiv> \<lparr>node_map = \<lambda>v. if v \<in> V\<^bsub>R\<^esub> - \<^bsub>r\<^esub>\<^sub>V ` V\<^bsub>K\<^esub> then Inr v else Inl (\<^bsub>d\<^esub>\<^sub>V ((inv_into V\<^bsub>K\<^esub> \<^bsub>r\<^esub>\<^sub>V) v)),
      edge_map = \<lambda>e. if e \<in> E\<^bsub>R\<^esub> - \<^bsub>r\<^esub>\<^sub>E ` E\<^bsub>K\<^esub> then Inr e else Inl (\<^bsub>d\<^esub>\<^sub>E ((inv_into E\<^bsub>K\<^esub> \<^bsub>r\<^esub>\<^sub>E) e))\<rparr>\<close>

interpretation inc_h: injective_morphism R H h
proof
  show \<open>\<^bsub>h\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
    using d.morph_edge_range r.inj_edges that by auto
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^esub>\<close> if \<open>v \<in> V\<^bsub>R\<^esub>\<close> for v
    using d.morph_node_range r.inj_nodes that by auto
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V (s\<^bsub>R\<^esub> e) = s\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
  proof (cases \<open>(s\<^bsub>R\<^esub> e) \<in> \<^bsub>r\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>)
    case True
    then show ?thesis
      apply (auto simp: d.G.source_integrity d.source_preserve r.source_preserve that)
      using inv_into_f_f r.inj_nodes r.inj_edges r.source_preserve d.G.source_integrity d.source_preserve
      by metis
  next
    case False
    then show ?thesis
      using d.G.source_integrity image_iff r.H.source_integrity r.source_preserve that by fastforce
  qed
next
  show \<open>\<^bsub>h\<^esub>\<^sub>V (t\<^bsub>R\<^esub> e) = t\<^bsub>H\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>R\<^esub>\<close> for e
  proof (cases \<open>e \<in> E\<^bsub>R\<^esub> - \<^bsub>r\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close>)
    case True
    then show ?thesis 
      by (simp add: graph.target_integrity r.H.graph_axioms)
  next
    case False
    then show ?thesis 
      apply simp
      by (smt (verit, ccfv_threshold) d.G.graph_axioms d.target_preserve graph.target_integrity image_iff inv_into_f_f r.inj_edges r.inj_nodes r.target_preserve that)
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

abbreviation c where 
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



interpretation pushout_diagram K R D H r d h c
proof
  show \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> r\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>K\<^esub>\<close> for v
    using r.inj_nodes that 
    by (simp add: morph_comp_def)
next
  show \<open>\<^bsub>h \<circ>\<^sub>\<rightarrow> r\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>K\<^esub>\<close> for e
    using r.inj_edges that 
    by (simp add: morph_comp_def)
next
  show \<open>Ex1M
            (\<lambda>xa. morphism H D' xa \<and>
                   (\<forall>v\<in>V\<^bsub>R\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
                   (\<forall>e\<in>E\<^bsub>R\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
            H \<close> if
    \<open>graph D'\<close> \<open>morphism R D' x\<close> \<open>morphism D D' y\<close> 
    \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> r\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> r\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close> 
  for D' x y
  proof -
    define u where \<open>u \<equiv> \<lparr>node_map = case_sum \<^bsub>y\<^esub>\<^sub>V \<^bsub>x\<^esub>\<^sub>V, edge_map = case_sum \<^bsub>y\<^esub>\<^sub>E \<^bsub>x\<^esub>\<^sub>E\<rparr>\<close>

    show ?thesis
    proof (rule_tac x = u in exI, rule conjI)

      show \<open>morphism H D' u 
        \<and> (\<forall>v\<in>V\<^bsub>R\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>R\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) 
        \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
        show \<open>morphism H D' u\<close>
        proof
          show \<open>finite V\<^bsub>D'\<^esub>\<close> and \<open>finite E\<^bsub>D'\<^esub>\<close>
            using graph.finite_nodes[OF that(1)] graph.finite_edges[OF that(1)]
            by simp_all
        next
          show \<open>s\<^bsub>D'\<^esub> e \<in> V\<^bsub>D'\<^esub>\<close> if \<open>e \<in> E\<^bsub>D'\<^esub>\<close> for e
            by (simp add: \<open>graph D'\<close> graph.source_integrity that)
        next
          show \<open>t\<^bsub>D'\<^esub> e \<in> V\<^bsub>D'\<^esub>\<close> if \<open>e \<in> E\<^bsub>D'\<^esub>\<close> for e
            by (simp add: \<open>graph D'\<close> graph.target_integrity that)
        next
          show \<open>\<^bsub>u\<^esub>\<^sub>E e \<in> E\<^bsub>D'\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
          proof (cases e)
            case (Inl a)
            then show ?thesis
              using that morphism.morph_edge_range[OF \<open>morphism D D' y\<close>, of a]
              by (auto simp add: u_def)
          next
            case (Inr b)
            then show ?thesis 
              using that morphism.morph_edge_range[OF \<open>morphism R D' x\<close>, of b]
              by (auto simp add: u_def)
          qed
            next
              show \<open>\<^bsub>u\<^esub>\<^sub>V v \<in> V\<^bsub>D'\<^esub>\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
              proof (cases v)
            case (Inl a)
            then show ?thesis
              using that morphism.morph_node_range[OF \<open>morphism D D' y\<close>, of a]
              by (auto simp add: u_def)
          next
            case (Inr b)
            then show ?thesis 
              using that morphism.morph_node_range[OF \<open>morphism R D' x\<close>, of b]
              by (auto simp add: u_def)
          qed
        next
          show \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>H\<^esub> e) = s\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
          proof (cases e)
            case (Inl a)
            have \<open>\<^bsub>y\<^esub>\<^sub>V (s\<^bsub>D\<^esub> a) = s\<^bsub>D'\<^esub> (\<^bsub>y\<^esub>\<^sub>E a)\<close> if \<open>a \<in> E\<^bsub>D\<^esub>\<close>
              by (simp add: \<open>morphism D D' y\<close> morphism.source_preserve that)
  
            thus ?thesis      
              using that
              by (auto simp add: u_def Inl)
          next
            case (Inr b)
  
            have \<open>\<^bsub>y\<^esub>\<^sub>V (\<^bsub>d\<^esub>\<^sub>V (inv_into V\<^bsub>K\<^esub> \<^bsub>r\<^esub>\<^sub>V (s\<^bsub>R\<^esub> b))) = s\<^bsub>D'\<^esub> (\<^bsub>x\<^esub>\<^sub>E b)\<close>
              if \<open>b \<in> E\<^bsub>R\<^esub>\<close> and \<open>b \<notin> \<^bsub>r\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> and \<open>s\<^bsub>R\<^esub> b \<in> \<^bsub>r\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>
              using that \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> r\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>  morphism.source_preserve[OF \<open>morphism R D' x\<close>] r.inj_nodes
              by (fastforce simp add: morph_comp_def)
              
            moreover have \<open>\<^bsub>x\<^esub>\<^sub>V (s\<^bsub>R\<^esub> b) = s\<^bsub>D'\<^esub> (\<^bsub>x\<^esub>\<^sub>E b)\<close> if \<open>b \<in> E\<^bsub>R\<^esub>\<close>          
              by (simp add: that \<open>morphism R D' x\<close> morphism.source_preserve)
  
            ultimately show ?thesis 
              using \<open>e \<in> E\<^bsub>H\<^esub>\<close>
              by (auto simp add: u_def Inr)
          qed
        next
          show \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>H\<^esub> e) = t\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
          proof (cases e)
            case (Inl a)
            have \<open>\<^bsub>y\<^esub>\<^sub>V (t\<^bsub>D\<^esub> a) = t\<^bsub>D'\<^esub> (\<^bsub>y\<^esub>\<^sub>E a)\<close> if \<open>a \<in> E\<^bsub>D\<^esub>\<close>
              by (simp add: \<open>morphism D D' y\<close> morphism.target_preserve that)
  
            thus ?thesis      
              using that
              by (auto simp add: u_def Inl)
          next
            case (Inr b)
  
            have \<open>\<^bsub>y\<^esub>\<^sub>V (\<^bsub>d\<^esub>\<^sub>V (inv_into V\<^bsub>K\<^esub> \<^bsub>r\<^esub>\<^sub>V (t\<^bsub>R\<^esub> b))) = t\<^bsub>D'\<^esub> (\<^bsub>x\<^esub>\<^sub>E b)\<close>
              if \<open>b \<in> E\<^bsub>R\<^esub>\<close> and \<open>b \<notin> \<^bsub>r\<^esub>\<^sub>E ` E\<^bsub>K\<^esub>\<close> and \<open>t\<^bsub>R\<^esub> b \<in> \<^bsub>r\<^esub>\<^sub>V ` V\<^bsub>K\<^esub>\<close>
              using that \<open>\<forall>v\<in>V\<^bsub>K\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> r\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>  morphism.target_preserve[OF \<open>morphism R D' x\<close>] r.inj_nodes
              by (fastforce simp add: morph_comp_def)
              
            moreover have \<open>\<^bsub>x\<^esub>\<^sub>V (t\<^bsub>R\<^esub> b) = t\<^bsub>D'\<^esub> (\<^bsub>x\<^esub>\<^sub>E b)\<close> if \<open>b \<in> E\<^bsub>R\<^esub>\<close>          
              by (simp add: that \<open>morphism R D' x\<close> morphism.target_preserve)
  
            ultimately show ?thesis 
              using \<open>e \<in> E\<^bsub>H\<^esub>\<close>
              by (auto simp add: u_def Inr)
          qed
        next
          show \<open>l\<^bsub>H\<^esub> v = l\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
          proof (cases v)
            case (Inl a)
            then show ?thesis 
              using that 
              by (fastforce simp add: u_def morphism.label_preserve[OF \<open>morphism D D' y\<close>])
          next
            case (Inr b)
            then show ?thesis 
              using that 
              by (simp add: u_def image_iff morphism.label_preserve[OF \<open>morphism R D' x\<close>])
          qed
        next
          show \<open>m\<^bsub>H\<^esub> e = m\<^bsub>D'\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
          proof (cases e)
            case (Inl a)
            then show ?thesis
              using that 
              by (fastforce simp add: u_def morphism.mark_preserve[OF \<open>morphism D D' y\<close>])
          next
            case (Inr b)
            then show ?thesis
              using that 
              by (simp add: u_def image_iff morphism.mark_preserve[OF \<open>morphism R D' x\<close>])
          qed
        qed
      next
        show \<open>\<forall>v\<in>V\<^bsub>R\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
          using that
          by (force simp add: morph_comp_def u_def r.inj_nodes)
      next
        show \<open>\<forall>e\<in>E\<^bsub>R\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
          using that
          by (force simp add: morph_comp_def u_def r.inj_edges)
      next
        show \<open>\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          by (simp add: morph_comp_def u_def)
      next
        show \<open>\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          by (simp add: morph_comp_def u_def)
      qed

  next
    show \<open>\<forall>ya. morphism H D' ya 
        \<and> (\<forall>v\<in>V\<^bsub>R\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>R\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) 
        \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) 
        \<longrightarrow> (\<forall>e\<in>E\<^bsub>H\<^esub>. \<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>H\<^esub>. \<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v)\<close>
      by (auto simp add: morph_comp_def u_def)
  qed
qed
qed

  end
end
