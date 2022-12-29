theory Morphism
  imports Graph 
begin

record ('v\<^sub>1,'v\<^sub>2,'e\<^sub>1,'e\<^sub>2) pre_morph =
  node_map :: "'v\<^sub>1 \<Rightarrow> 'v\<^sub>2"
  edge_map :: "'e\<^sub>1 \<Rightarrow> 'e\<^sub>2"

notation node_map ("\<^bsub>_\<^esub>\<^sub>V")
notation edge_map ("\<^bsub>_\<^esub>\<^sub>E")

locale morphism =
  G: graph G +
  H: graph H for
    G :: "('v\<^sub>1::countable,'e\<^sub>1::countable,'l,'m) pre_graph" and 
    H :: "('v\<^sub>2::countable,'e\<^sub>2::countable,'l,'m) pre_graph" +
  fixes 
    f :: "('v\<^sub>1,'v\<^sub>2,'e\<^sub>1,'e\<^sub>2) pre_morph"  
  assumes
    morph_edge_range: "e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^esub>" and
    morph_node_range: "v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^esub>" and
    source_preserve : "e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>V (s\<^bsub>G\<^esub> e) = s\<^bsub>H\<^esub> (\<^bsub>f\<^esub>\<^sub>E e)" and
    target_preserve : "e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>V (t\<^bsub>G\<^esub> e) = t\<^bsub>H\<^esub> (\<^bsub>f\<^esub>\<^sub>E e)" and
    label_preserve  : "v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> l\<^bsub>G\<^esub> v = l\<^bsub>H\<^esub> (\<^bsub>f\<^esub>\<^sub>V v)" and
    mark_preserve   : "e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> m\<^bsub>G\<^esub> e = m\<^bsub>H\<^esub> (\<^bsub>f\<^esub>\<^sub>E e)"

definition morph_comp
  :: "('v\<^sub>2,'v\<^sub>3,'e\<^sub>2,'e\<^sub>3) pre_morph 
  \<Rightarrow>  ('v\<^sub>1,'v\<^sub>2,'e\<^sub>1,'e\<^sub>2) pre_morph 
  \<Rightarrow>('v\<^sub>1,'v\<^sub>3,'e\<^sub>1,'e\<^sub>3) pre_morph" (infixl "\<circ>\<^sub>\<rightarrow>" 55) where
"g \<circ>\<^sub>\<rightarrow> f = \<lparr>node_map = \<^bsub>g\<^esub>\<^sub>V \<circ> \<^bsub>f\<^esub>\<^sub>V, edge_map = \<^bsub>g\<^esub>\<^sub>E \<circ> \<^bsub>f\<^esub>\<^sub>E\<rparr>"

lemma wf_morph_comp:
  assumes
    f: \<open>morphism G H f\<close> and
    g: \<open>morphism H K g\<close>
  shows \<open>morphism G K (g \<circ>\<^sub>\<rightarrow> f)\<close>
proof (intro_locales)
  show \<open>graph G\<close> by (fact morphism.axioms[OF f])
next
  show \<open>graph K\<close> by (fact morphism.axioms[OF g])
next
  show \<open>morphism_axioms G K (g \<circ>\<^sub>\<rightarrow> f)\<close> 
  proof
    show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e \<in> E\<^bsub>K\<^esub>\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
      by (simp add: morph_comp_def morphism.morph_edge_range[OF g] morphism.morph_edge_range[OF f] that)
  next
    show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v \<in> V\<^bsub>K\<^esub>\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
      by (simp add: morph_comp_def morphism.morph_node_range[OF g] morphism.morph_node_range[OF f] that)
  next
    show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V (s\<^bsub>G\<^esub> e) = s\<^bsub>K\<^esub> (\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
      by (simp add: morph_comp_def 
            morphism.morph_edge_range[OF f] 
            morphism.morph_edge_range[OF g] 
            morphism.source_preserve[OF f] 
            morphism.source_preserve[OF g] that)
  next
    show \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V (t\<^bsub>G\<^esub> e) = t\<^bsub>K\<^esub> (\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
      by (simp add: morph_comp_def 
            morphism.morph_edge_range[OF f] 
            morphism.morph_edge_range[OF g] 
            morphism.target_preserve[OF f] 
            morphism.target_preserve[OF g] that)
  next
    show \<open>l\<^bsub>G\<^esub> v = l\<^bsub>K\<^esub> (\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
      by (simp add: morph_comp_def 
          morphism.label_preserve[OF f]
          morphism.label_preserve[OF g]
          morphism.morph_node_range[OF f] that)
  next
    show \<open>m\<^bsub>G\<^esub> e = m\<^bsub>K\<^esub> (\<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
      by (simp add: morph_comp_def 
          morphism.mark_preserve[OF f]
          morphism.mark_preserve[OF g]
          morphism.morph_edge_range[OF f] that)
  qed
qed

lemma morph_assoc_nodes:
  assumes \<open>v \<in> V\<^bsub>H\<^esub>\<close>
  shows \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> (g \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>V v = \<^bsub>(f \<circ>\<^sub>\<rightarrow> g) \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
  by (simp add: morph_comp_def)

lemma morph_assoc_edges:
  assumes \<open>e \<in> E\<^bsub>H\<^esub>\<close>
  shows \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> (g \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>E e = \<^bsub>(f \<circ>\<^sub>\<rightarrow> g) \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close>
  by (simp add: morph_comp_def)


locale injective_morphism = morphism +
  assumes 
    inj_nodes: "inj_on \<^bsub>f\<^esub>\<^sub>V V\<^bsub>G\<^esub>" and
    inj_edges: "inj_on \<^bsub>f\<^esub>\<^sub>E E\<^bsub>G\<^esub>"

lemma inj_comp_fg_g_inj:
  assumes \<open>morphism G H g\<close> \<open>morphism H K f\<close> \<open>injective_morphism G H (f \<circ>\<^sub>\<rightarrow> g)\<close>
  shows \<open>injective_morphism G H g\<close>
proof intro_locales
  show \<open>graph G\<close>
    using morphism.axioms(1)[OF assms(1)] by assumption
next
  show \<open>graph H\<close>
    using morphism.axioms(2)[OF assms(1)] by assumption
next
  show \<open>morphism_axioms G H g\<close>
    using morphism.axioms(3)[OF assms(1)] by assumption
next
  show \<open>injective_morphism_axioms G g \<close>
  proof
    show \<open>inj_on \<^bsub>g\<^esub>\<^sub>V V\<^bsub>G\<^esub>\<close>
      using injective_morphism.inj_nodes[OF assms(3)]
      by (auto simp add: inj_on_imageI2 morph_comp_def)
  next
    show \<open>inj_on \<^bsub>g\<^esub>\<^sub>E E\<^bsub>G\<^esub>\<close>
      using injective_morphism.inj_edges[OF assms(3)]
      by (auto simp add: inj_on_imageI2 morph_comp_def)
  qed
qed

locale surjective_morphism = morphism +
  assumes
    surj_nodes: \<open>v \<in> V\<^bsub>H\<^esub> \<Longrightarrow> \<exists>v' \<in> V\<^bsub>G\<^esub>. \<^bsub>f\<^esub>\<^sub>V v' = v\<close> and
    surj_edges: \<open>e \<in> E\<^bsub>H\<^esub> \<Longrightarrow> \<exists>e' \<in> E\<^bsub>G\<^esub>. \<^bsub>f\<^esub>\<^sub>E e' = e\<close>

locale bijective_morphism = morphism +
  assumes
    bij_nodes: "bij_betw \<^bsub>f\<^esub>\<^sub>V V\<^bsub>G\<^esub> V\<^bsub>H\<^esub>" and
    bij_edges: "bij_betw \<^bsub>f\<^esub>\<^sub>E E\<^bsub>G\<^esub> E\<^bsub>H\<^esub>"
begin

lemma ex_inv:
  obtains f' where \<open>bijective_morphism H G f'\<close> 
    and \<open>\<forall>v \<in> V\<^bsub>G\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> f \<^esub>\<^sub>V v = v\<close>  \<open>\<forall>e \<in> E\<^bsub>G\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> f \<^esub>\<^sub>E e = e\<close>
    and \<open>\<forall>v \<in> V\<^bsub>H\<^esub>. \<^bsub>f  \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = v\<close>  \<open>\<forall>e \<in> E\<^bsub>H\<^esub>. \<^bsub>f  \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = e\<close>
proof -
  let ?f' = \<open>\<lparr>node_map = inv_into V\<^bsub>G\<^esub> \<^bsub>f\<^esub>\<^sub>V, edge_map = inv_into E\<^bsub>G\<^esub> \<^bsub>f\<^esub>\<^sub>E\<rparr>\<close>
  have \<open>bijective_morphism H G ?f'\<close>
  proof
    show \<open>\<^bsub>?f'\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
    proof -
      have \<open>\<^bsub>?f'\<^esub>\<^sub>E `E\<^bsub>H\<^esub> =  E\<^bsub>G\<^esub>\<close>
        using bij_betw_inv_into[OF bij_edges]
        by (simp add: bij_betw_imp_surj_on)

     thus ?thesis
       using that by auto
   qed
 next
   show \<open>\<^bsub>?f'\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
    proof -
      have \<open>\<^bsub>?f'\<^esub>\<^sub>V ` V\<^bsub>H\<^esub> =  V\<^bsub>G\<^esub>\<close>
        using bij_betw_inv_into[OF bij_nodes]
        by (simp add: bij_betw_imp_surj_on)

     thus ?thesis
       using that by auto
   qed
 next
   show \<open>\<^bsub>?f'\<^esub>\<^sub>V (s\<^bsub>H\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
   proof -
     have \<open>injective_morphism H G ?f'\<close>
     proof
       show \<open>\<^bsub>?f'\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
         using bij_betwE[OF bij_betw_inv_into[OF bij_edges]] that
         by simp
     next
       show \<open>\<^bsub>?f'\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
         using bij_betwE[OF bij_betw_inv_into[OF bij_nodes]] that
         by simp
     next
       show \<open>\<^bsub>?f'\<^esub>\<^sub>V (s\<^bsub>H\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
       proof -
         obtain v' where \<open>v' = s\<^bsub>H\<^esub> e\<close> and \<open>v' \<in> V\<^bsub>H\<^esub>\<close>
           by (simp add: H.source_integrity \<open>e \<in> E\<^bsub>H\<^esub>\<close>)
         obtain e' where \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> and \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           using \<open>e \<in> E\<^bsub>H\<^esub>\<close> bij_betwE bij_betw_inv_into bij_edges by fastforce

         have \<open>\<^bsub>?f'\<^esub>\<^sub>V v' = s\<^bsub>G\<^esub> e'\<close>
           using 
             bij_betw_inv_into_right[OF bij_nodes, of v'] 
             bij_betw_inv_into_right[OF bij_edges, of e]
             graph.source_integrity[of H e]
             graph.source_integrity[of G e']
             source_preserve[of e'] that
             \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = s\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
             G.graph_axioms
             bij_betw_inv_into_left[OF bij_nodes]
           by fastforce

         thus ?thesis
           using  \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = s\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           by simp
       qed
     next
       show \<open>\<^bsub>?f'\<^esub>\<^sub>V (t\<^bsub>H\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
       proof -
         obtain v' where \<open>v' = t\<^bsub>H\<^esub> e\<close> and \<open>v' \<in> V\<^bsub>H\<^esub>\<close>
           by (simp add: H.target_integrity \<open>e \<in> E\<^bsub>H\<^esub>\<close>)
         obtain e' where \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> and \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           using \<open>e \<in> E\<^bsub>H\<^esub>\<close> bij_betwE bij_betw_inv_into bij_edges by fastforce

         have \<open>\<^bsub>?f'\<^esub>\<^sub>V v' = t\<^bsub>G\<^esub> e'\<close>
           using 
             bij_betw_inv_into_right[OF bij_nodes, of v'] 
             bij_betw_inv_into_right[OF bij_edges, of e]
             graph.target_integrity[of H e]
             graph.target_integrity[of G e']
             target_preserve[of e'] that
             \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = t\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
             G.graph_axioms
             bij_betw_inv_into_left[OF bij_nodes]
           by fastforce

         thus ?thesis
           using  \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = t\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           by simp
       qed
     next
       show \<open>l\<^bsub>H\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
         using bij_betw_inv_into[OF bij_nodes] bij_betw_inv_into_right[OF bij_nodes, of v] label_preserve that
         by (simp add: bij_betwE)
     next
       show \<open>m\<^bsub>H\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
         using bij_betw_inv_into[OF bij_edges] bij_betw_inv_into_right[OF bij_edges, of e] mark_preserve that
         by (simp add: bij_betwE)
     next
       show \<open>inj_on \<^bsub>?f'\<^esub>\<^sub>V V\<^bsub>H\<^esub>\<close>
         using bij_betw_imp_inj_on[OF bij_betw_inv_into[OF bij_nodes]]
         by simp
     next
       show \<open>inj_on \<^bsub>?f'\<^esub>\<^sub>E E\<^bsub>H\<^esub>\<close>
         using bij_betw_imp_inj_on[OF bij_betw_inv_into[OF bij_edges]]
         by simp
     qed

     thus ?thesis
       using morphism.source_preserve[of H G ?f'] that injective_morphism.axioms
       by blast    
   qed     
 next
   show \<open>\<^bsub>?f'\<^esub>\<^sub>V (t\<^bsub>H\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
   proof -
\<comment> \<open>duplication from source\<close>
     have \<open>injective_morphism H G ?f'\<close>
     proof
       show \<open>\<^bsub>?f'\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
         using bij_betwE[OF bij_betw_inv_into[OF bij_edges]] that
         by simp
     next
       show \<open>\<^bsub>?f'\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
         using bij_betwE[OF bij_betw_inv_into[OF bij_nodes]] that
         by simp
     next
       show \<open>\<^bsub>?f'\<^esub>\<^sub>V (s\<^bsub>H\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
       proof -
         obtain v' where \<open>v' = s\<^bsub>H\<^esub> e\<close> and \<open>v' \<in> V\<^bsub>H\<^esub>\<close>
           by (simp add: H.source_integrity \<open>e \<in> E\<^bsub>H\<^esub>\<close>)
         obtain e' where \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> and \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           using \<open>e \<in> E\<^bsub>H\<^esub>\<close> bij_betwE bij_betw_inv_into bij_edges by fastforce

         have \<open>\<^bsub>?f'\<^esub>\<^sub>V v' = s\<^bsub>G\<^esub> e'\<close>
           using 
             bij_betw_inv_into_right[OF bij_nodes, of v'] 
             bij_betw_inv_into_right[OF bij_edges, of e]
             graph.source_integrity[of H e]
             graph.source_integrity[of G e']
             source_preserve[of e'] that
             \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = s\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
             G.graph_axioms
             bij_betw_inv_into_left[OF bij_nodes]
           by fastforce

         thus ?thesis
           using  \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = s\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           by simp
       qed
     next
       show \<open>\<^bsub>?f'\<^esub>\<^sub>V (t\<^bsub>H\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
       proof -
         obtain v' where \<open>v' = t\<^bsub>H\<^esub> e\<close> and \<open>v' \<in> V\<^bsub>H\<^esub>\<close>
           by (simp add: H.target_integrity \<open>e \<in> E\<^bsub>H\<^esub>\<close>)
         obtain e' where \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> and \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           using \<open>e \<in> E\<^bsub>H\<^esub>\<close> bij_betwE bij_betw_inv_into bij_edges by fastforce

         have \<open>\<^bsub>?f'\<^esub>\<^sub>V v' = t\<^bsub>G\<^esub> e'\<close>
           using 
             bij_betw_inv_into_right[OF bij_nodes, of v'] 
             bij_betw_inv_into_right[OF bij_edges, of e]
             graph.target_integrity[of H e]
             graph.target_integrity[of G e']
             target_preserve[of e'] that
             \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = t\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
             G.graph_axioms
             bij_betw_inv_into_left[OF bij_nodes]
           by fastforce

         thus ?thesis
           using  \<open>e'=\<^bsub>?f'\<^esub>\<^sub>E e\<close> \<open>v' = t\<^bsub>H\<^esub> e\<close>  \<open>e' \<in> E\<^bsub>G\<^esub>\<close>
           by simp
       qed
     next
       show \<open>l\<^bsub>H\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
         using bij_betw_inv_into[OF bij_nodes] bij_betw_inv_into_right[OF bij_nodes, of v] label_preserve that
         by (simp add: bij_betwE)
     next
       show \<open>m\<^bsub>H\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
         using bij_betw_inv_into[OF bij_edges] bij_betw_inv_into_right[OF bij_edges, of e] mark_preserve that
         by (simp add: bij_betwE)
     next
       show \<open>inj_on \<^bsub>?f'\<^esub>\<^sub>V V\<^bsub>H\<^esub>\<close>
         using bij_betw_imp_inj_on[OF bij_betw_inv_into[OF bij_nodes]]
         by simp
     next
       show \<open>inj_on \<^bsub>?f'\<^esub>\<^sub>E E\<^bsub>H\<^esub>\<close>
         using bij_betw_imp_inj_on[OF bij_betw_inv_into[OF bij_edges]]
         by simp
     qed

     thus ?thesis
       using morphism.target_preserve[of H G ?f'] that injective_morphism.axioms
       by blast    
   qed     

 next
   show \<open>l\<^bsub>H\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
     using bij_betw_inv_into[OF bij_nodes] bij_betw_inv_into_right[OF bij_nodes, of v] label_preserve that
     by (simp add: bij_betwE)
 next   
   show \<open>m\<^bsub>H\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>?f'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
     using bij_betw_inv_into[OF bij_edges] bij_betw_inv_into_right[OF bij_edges, of e] mark_preserve that
     by (simp add: bij_betwE)
 next
   show \<open>bij_betw \<^bsub>?f'\<^esub>\<^sub>V V\<^bsub>H\<^esub> V\<^bsub>G\<^esub>\<close>
     by (simp add: bij_betw_inv_into[OF bij_nodes])
 next
   show \<open>bij_betw \<^bsub>?f'\<^esub>\<^sub>E E\<^bsub>H\<^esub> E\<^bsub>G\<^esub>\<close>
     by (simp add: bij_betw_inv_into[OF bij_edges])
 qed

  moreover have \<open>\<forall>v \<in> V\<^bsub>G\<^esub>. \<^bsub>?f' \<circ>\<^sub>\<rightarrow> f \<^esub>\<^sub>V v = v\<close>  \<open>\<forall>e \<in> E\<^bsub>G\<^esub>. \<^bsub>?f' \<circ>\<^sub>\<rightarrow> f \<^esub>\<^sub>E e = e\<close>
    using bij_betw_inv_into_left bij_nodes bij_edges
    by (fastforce simp add: morph_comp_def)+

  moreover have \<open>\<forall>v \<in> V\<^bsub>H\<^esub>. \<^bsub>f  \<circ>\<^sub>\<rightarrow> ?f'\<^esub>\<^sub>V v = v\<close>  \<open>\<forall>e \<in> E\<^bsub>H\<^esub>. \<^bsub>f  \<circ>\<^sub>\<rightarrow> ?f'\<^esub>\<^sub>E e = e\<close>
    using bij_betw_inv_into_right bij_nodes bij_edges
    by (fastforce simp add: morph_comp_def)+

  ultimately show ?thesis ..
qed
 
end

sublocale bijective_morphism \<subseteq> injective_morphism
proof
  show \<open>inj_on \<^bsub>f\<^esub>\<^sub>V V\<^bsub>G\<^esub>\<close>
    by (blast intro: bij_betw_imp_inj_on bij_nodes)
next
  show \<open>inj_on \<^bsub>f\<^esub>\<^sub>E E\<^bsub>G\<^esub>\<close>
    by (blast intro: bij_betw_imp_inj_on bij_edges)
qed

sublocale bijective_morphism \<subseteq> surjective_morphism
proof
  show \<open>\<exists>v'\<in>V\<^bsub>G\<^esub>. \<^bsub>f\<^esub>\<^sub>V v' = v\<close> if \<open>v \<in> V\<^bsub>H\<^esub>\<close> for v
  proof -
    have \<open>\<^bsub>f\<^esub>\<^sub>V ` V\<^bsub>G\<^esub> = V\<^bsub>H\<^esub>\<close>
      using bij_nodes
      by (simp add: bij_betw_def)

    thus ?thesis
      using that
      by force
  qed
next
  show \<open>\<exists>e'\<in>E\<^bsub>G\<^esub>. \<^bsub>f\<^esub>\<^sub>E e' = e\<close> if \<open>e \<in> E\<^bsub>H\<^esub>\<close> for e
  proof -
    have \<open>\<^bsub>f\<^esub>\<^sub>E ` E\<^bsub>G\<^esub> = E\<^bsub>H\<^esub>\<close>
      using bij_edges
      by (simp add: bij_betw_def)

    thus ?thesis
      using that
      by force
  qed
qed
  

locale identity_morphism = 
  bijective_morphism G G f for G f +
assumes
  id_nodes: \<open>v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>V v = v\<close> and
  id_edges: \<open>e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f\<^esub>\<^sub>E e = e\<close>

abbreviation idM where \<open>idM \<equiv> \<lparr>node_map = id, edge_map = id\<rparr>\<close>

locale inclusion_morphism =
  bijective_morphism G H idM for G H
begin

lemma nodes_g_in_h[iff]:
  \<open>x \<in> V\<^bsub>G\<^esub> \<longleftrightarrow> x \<in> V\<^bsub>H\<^esub>\<close>
  using bij_betw_imp_surj_on bij_nodes 
  by fastforce

lemma edges_g_in_h[iff]:
  \<open>x \<in> E\<^bsub>G\<^esub> \<longleftrightarrow> x \<in> E\<^bsub>H\<^esub>\<close>
  using bij_betw_imp_surj_on bij_edges
  by fastforce

end



context graph begin
sublocale idm: identity_morphism G idM
proof
 show \<open>\<^bsub>idM\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
    by (simp add: that)
next
  show \<open>\<^bsub>idM\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
    by (simp add: that)
next
  show \<open>\<^bsub>idM\<^esub>\<^sub>V (s\<^bsub>G\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>idM\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
    by simp
next
  show \<open>\<^bsub>idM\<^esub>\<^sub>V (t\<^bsub>G\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>idM\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
    by simp
next
  show \<open>l\<^bsub>G\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>idM\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
    by simp
next
  show \<open>m\<^bsub>G\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>idM\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
    by simp
next
  show \<open>bij_betw \<^bsub>idM\<^esub>\<^sub>V V\<^bsub>G\<^esub> V\<^bsub>G\<^esub>\<close>
    by simp
next
  show \<open>bij_betw \<^bsub>idM\<^esub>\<^sub>E E\<^bsub>G\<^esub> E\<^bsub>G\<^esub>\<close>
    by simp
next
  show \<open>\<^bsub>idM\<^esub>\<^sub>V v = v\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v 
    by simp
next
  show \<open>\<^bsub>idM\<^esub>\<^sub>E e = e\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
    by simp
qed
end

(* lemma id_comp[simp]: 
  \<open>\<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V = \<^bsub>f\<^esub>\<^sub>V\<close> and \<open>\<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E = \<^bsub>f\<^esub>\<^sub>E\<close>
  \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V = \<^bsub>f\<^esub>\<^sub>V\<close> and \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E = \<^bsub>f\<^esub>\<^sub>E\<close>
  by (simp_all add: morph_comp_def)
 *)
lemma left_identity_composition[simp]:
  assumes 
    f: \<open>morphism G H f\<close> and
    i: \<open>identity_morphism H id\<^sub>L\<close>
  shows
    \<open>v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>id\<^sub>L \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> and
    \<open>e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>id\<^sub>L \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> 
proof -
  show \<open>\<^bsub>id\<^sub>L \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close>    
    using assms that
    by (simp add: identity_morphism.id_nodes morph_comp_def morphism.morph_node_range)
next
  show \<open>\<^bsub>id\<^sub>L \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close>
    using assms that
    by (simp add: identity_morphism.id_edges morph_comp_def morphism.morph_edge_range)
qed

lemma right_identity_composition[simp]:
  assumes 
    f: \<open>morphism G H f\<close> and
    i: \<open>identity_morphism G id\<^sub>R\<close>
  shows
    \<open>v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> id\<^sub>R\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> and
    \<open>e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> \<^bsub>f\<circ>\<^sub>\<rightarrow> id\<^sub>R\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> 
proof -
  show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> id\<^sub>R\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close>    
    using assms that
    by (simp add: identity_morphism.id_nodes morph_comp_def morphism.morph_node_range)
next
  show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> id\<^sub>R\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close>
    using assms that
    by (simp add: identity_morphism.id_edges morph_comp_def morphism.morph_edge_range)
qed

lemma inj_surj_morph_is_bijI:
  assumes
  inj : \<open>injective_morphism G H g\<close> and
  surj: \<open>surjective_morphism G H g\<close>
shows \<open>bijective_morphism G H g\<close>
proof intro_locales
  show \<open>graph G\<close>
    using inj
    by (simp add: injective_morphism_def morphism_def)
next
  show \<open>graph H\<close>
    using inj
    by (simp add: injective_morphism_def morphism_def)
next
  show \<open>morphism_axioms G H g\<close>
    using inj
    by (simp add: injective_morphism_def morphism_def)
next
  show \<open>bijective_morphism_axioms G H g\<close>
  proof
    show \<open>bij_betw \<^bsub>g\<^esub>\<^sub>V V\<^bsub>G\<^esub> V\<^bsub>H\<^esub>\<close>
    proof -
      have \<open>inj_on \<^bsub>g\<^esub>\<^sub>V V\<^bsub>G\<^esub>\<close>
        by (blast intro: inj injective_morphism.inj_nodes)

      moreover have \<open>\<^bsub>g\<^esub>\<^sub>V ` V\<^bsub>G\<^esub> = V\<^bsub>H\<^esub>\<close>
        using surj
        by (fastforce simp add: surjective_morphism_def surjective_morphism_axioms_def morphism.morph_node_range)

      ultimately show ?thesis 
        by (simp add: bij_betw_def)
    qed
  next
    show \<open>bij_betw \<^bsub>g\<^esub>\<^sub>E E\<^bsub>G\<^esub> E\<^bsub>H\<^esub>\<close>
    proof -
      have \<open>inj_on \<^bsub>g\<^esub>\<^sub>E E\<^bsub>G\<^esub>\<close>
        by (blast intro: inj injective_morphism.inj_edges)

      moreover have \<open>\<^bsub>g\<^esub>\<^sub>E ` E\<^bsub>G\<^esub> = E\<^bsub>H\<^esub>\<close>
        using surj
        by (fastforce simp add: surjective_morphism_def surjective_morphism_axioms_def morphism.morph_edge_range)

      ultimately show ?thesis 
        by (simp add: bij_betw_def)
    qed
  qed
qed

lemma bijective_morphismE:
  fixes A B b
  assumes 
    major: \<open>bijective_morphism A B b\<close> and
    minor: \<open>\<lbrakk>injective_morphism A B b; surjective_morphism A B b\<rbrakk> \<Longrightarrow> R\<close>
  shows R
  proof (rule minor)
    show \<open>injective_morphism A B b\<close> 
    proof -
      interpret b: bijective_morphism A B b
        using major by assumption

      show ?thesis ..
    qed
  next
    show \<open>surjective_morphism A B b\<close>
    proof -
      interpret b: bijective_morphism A B b
        using major by assumption

      show ?thesis ..
    qed
qed
     
lemma inj_comp_inj:
  assumes \<open>injective_morphism G H g\<close> and \<open>injective_morphism H K f\<close>
  shows \<open>injective_morphism G K (f \<circ>\<^sub>\<rightarrow> g)\<close>
proof (intro_locales)
  show \<open>graph G\<close>
    using assms
    by (simp add: injective_morphism_def morphism_def)
next
  show \<open>graph K\<close>
    using assms
    by (simp add: injective_morphism_def morphism_def)
next
  show \<open>morphism_axioms G K (f \<circ>\<^sub>\<rightarrow> g)\<close>
    using wf_morph_comp assms injective_morphism.axioms(1)[of G H g] injective_morphism.axioms(1)[of H K f] morphism_def
    by blast
  show \<open>injective_morphism_axioms G (f \<circ>\<^sub>\<rightarrow> g)\<close>
  proof
    show \<open>inj_on \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V V\<^bsub>G\<^esub>\<close>
      using assms
      by (auto simp add: injective_morphism_def injective_morphism_axioms_def morph_comp_def inj_on_def morphism.morph_node_range)
  next
    show \<open>inj_on \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E E\<^bsub>G\<^esub>\<close>
      using assms
      by (auto simp add: injective_morphism_def injective_morphism_axioms_def morph_comp_def inj_on_def morphism.morph_edge_range)
  qed
qed

lemma f_comp_g_inj_f_inj:
  assumes 
    f: \<open>morphism G H f\<close> and 
    g: \<open>morphism H K g\<close> and \<open>injective_morphism G K (g \<circ>\<^sub>\<rightarrow> f)\<close>
  shows \<open>injective_morphism G H f\<close>
  using assms
  by (auto simp add: morph_comp_def injective_morphism_def injective_morphism_axioms_def intro: inj_on_imageI2)

lemma bij_comp_bij_is_bij:
  assumes 
    f: \<open>bijective_morphism A B f\<close> and 
    g: \<open>bijective_morphism B C g\<close>
  shows \<open>bijective_morphism A C (g\<circ>\<^sub>\<rightarrow> f)\<close>
proof -
  interpret f: bijective_morphism A B f
    using f by assumption

  interpret g: bijective_morphism B C g
    using g by assumption

  interpret c: morphism A C "g\<circ>\<^sub>\<rightarrow> f"
    using wf_morph_comp[OF f.morphism_axioms g.morphism_axioms]
    by assumption

  show ?thesis
  proof
    show \<open>bij_betw \<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V V\<^bsub>A\<^esub> V\<^bsub>C\<^esub>\<close>
      using bij_betw_trans[OF f.bij_nodes g.bij_nodes]
      by (simp add: morph_comp_def)
  next
    show \<open> bij_betw \<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E E\<^bsub>A\<^esub> E\<^bsub>C\<^esub>\<close>
      using bij_betw_trans[OF f.bij_edges g.bij_edges]
      by (simp add: morph_comp_def)
  qed
qed

lemma f_comp_g_surj_g_surj:
  assumes 
    f: \<open>morphism G H f\<close> and 
    g: \<open>morphism H K g\<close> and \<open>surjective_morphism G K (g \<circ>\<^sub>\<rightarrow> f)\<close>
  shows \<open>surjective_morphism H K g\<close>
  using assms
  by (fastforce simp add: morph_comp_def surjective_morphism_def surjective_morphism_axioms_def morphism.morph_edge_range morphism.morph_node_range)

lemma morph_comp_id[simp]:
  shows  \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V = \<^bsub>f\<^esub>\<^sub>V\<close> 
    and  \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E = \<^bsub>f\<^esub>\<^sub>E\<close>
    and  \<open>\<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V = \<^bsub>f\<^esub>\<^sub>V\<close>
    and  \<open>\<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E = \<^bsub>f\<^esub>\<^sub>E\<close>
  by (simp_all add: morph_comp_def)

lemma morph_assoc[simp]: 
  \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> (y \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>V = \<^bsub>(x \<circ>\<^sub>\<rightarrow> y) \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V\<close> and \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> (y \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>E = \<^bsub>(x \<circ>\<^sub>\<rightarrow> y) \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E\<close>
  by (auto simp: morph_comp_def)

(* TODO *)
lemma xx2:
\<open>graph G \<Longrightarrow> identity_morphism G idM\<close>
  by (simp add: bijective_morphism.intro bijective_morphism_axioms_def identity_morphism_axioms_def identity_morphism_def morphism.intro morphism_axioms.intro)

lemma xx3:
  assumes \<open>graph G\<close>
  shows \<open>identity_morphism G idM\<close>
  by (simp add: assms bijective_morphism.intro bijective_morphism_axioms.intro identity_morphism.intro identity_morphism_axioms_def morphism.intro morphism_axioms_def)

lemma xx:
  assumes \<open>graph G\<close>
  obtains \<open>identity_morphism G idM\<close>
  by (simp add: assms bijective_morphism.intro bijective_morphism_axioms.intro identity_morphism.intro identity_morphism_axioms_def morphism.intro morphism_axioms_def)
 
lemma comp_id_bij:
  assumes
    f: \<open>morphism G H f\<close> and
    g: \<open>morphism H G g\<close> and
    \<open>\<forall>v \<in> V\<^bsub>G\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = v\<close> and \<open>\<forall>e \<in> E\<^bsub>G\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = e\<close> and
    \<open>\<forall>v \<in> V\<^bsub>H\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = v\<close> and \<open>\<forall>e \<in> E\<^bsub>H\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = e\<close>
  shows \<open>bijective_morphism G H f\<close>
proof intro_locales
  show \<open>graph G\<close>
    using f
    by (simp add: morphism_def)
next
  show \<open>graph H\<close>
    using f
    by (simp add: morphism_def)
next
  show \<open>morphism_axioms G H f\<close>
    using f
    by (simp add: morphism_def)
next
  show \<open>bijective_morphism_axioms G H f\<close>
  proof
    show \<open>bij_betw \<^bsub>f\<^esub>\<^sub>V V\<^bsub>G\<^esub> V\<^bsub>H\<^esub>\<close>
    proof -
      have \<open>inj_on \<^bsub>f\<^esub>\<^sub>V V\<^bsub>G\<^esub>\<close>
        using assms
        by (fastforce simp add: morph_comp_def intro: inj_on_inverseI)

      moreover have \<open>\<forall>v \<in> V\<^bsub>H\<^esub>. \<exists>v' \<in> V\<^bsub>G\<^esub>. \<^bsub>f\<^esub>\<^sub>V v' = v\<close>
        using assms
        by (fastforce simp add: morph_comp_def morphism.morph_node_range[OF g])

      ultimately show ?thesis 
        by (fast intro: bij_betwI' morphism.morph_node_range[OF f] dest: inj_onD)
    qed
  next
    show \<open>bij_betw \<^bsub>f\<^esub>\<^sub>E E\<^bsub>G\<^esub> E\<^bsub>H\<^esub>\<close>
    proof -
      have \<open>inj_on \<^bsub>f\<^esub>\<^sub>E E\<^bsub>G\<^esub>\<close>
        using assms
        by (fastforce simp add: morph_comp_def intro: inj_on_inverseI)

      moreover have \<open>\<forall>e \<in> E\<^bsub>H\<^esub>. \<exists>e' \<in> E\<^bsub>G\<^esub>. \<^bsub>f\<^esub>\<^sub>E e' = e\<close>
        using assms
        by (fastforce simp add: morph_comp_def morphism.morph_edge_range[OF g])

      ultimately show ?thesis 
        by (fast intro: bij_betwI' morphism.morph_edge_range[OF f] dest: inj_onD)
    qed
  qed
qed

end