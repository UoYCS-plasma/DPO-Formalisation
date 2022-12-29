theory DirectDerivation
  imports Rule Gluing Deletion
begin


(* GRAT PDF P. 114 *)
locale direct_derivation = 
  r: rule r +
 (*  m: injective_morphism "interf r" D m  +
  *)
  g: injective_morphism "lhs r" G g  +
  po1: pushout_diagram "interf r" "lhs r" D G idM m g c +
  po2: pushout_diagram "interf r" "rhs r" D H idM m f h
  for r G g D m c H f h
begin

theorem
  assumes 
    po3: \<open>pushout_diagram (interf r) (lhs r) D' G idM m' g c'\<close> and
    po4: \<open>pushout_diagram (interf r) (rhs r) D' H' idM m' f' h'\<close>
  shows \<open>(\<exists>u. bijective_morphism D D' u) \<and> (\<exists>u. bijective_morphism H H' u)\<close>
proof -
  interpret po3: pushout_diagram "interf r" "lhs r" D' G idM m' g c'
    using po3 by assumption

  interpret m: injective_morphism "interf r" D m
  proof
    show \<open>inj_on \<^bsub>m\<^esub>\<^sub>V V\<^bsub>interf r\<^esub>\<close>
      using po1.node_commutativity g.inj_nodes r.k.nodes_g_in_h
      by (simp add: morph_comp_def inj_on_def)
  next
    show \<open>inj_on \<^bsub>m\<^esub>\<^sub>E E\<^bsub>interf r\<^esub>\<close>
      using po1.edge_commutativity g.inj_edges r.k.edges_g_in_h
      by (simp add: morph_comp_def inj_on_def)
  qed
     
  interpret m': injective_morphism "interf r" D' m'
  proof
    show \<open>inj_on \<^bsub>m'\<^esub>\<^sub>V V\<^bsub>interf r\<^esub>\<close>
      using po3.node_commutativity g.inj_nodes r.k.nodes_g_in_h
      by (simp add: morph_comp_def inj_on_def)
  next
    show \<open>inj_on \<^bsub>m'\<^esub>\<^sub>E E\<^bsub>interf r\<^esub>\<close>
      using po3.edge_commutativity g.inj_edges r.k.edges_g_in_h
      by (simp add: morph_comp_def inj_on_def)
  qed
  thm po1.uniqueness_pc
  have u:\<open>\<exists>u. bijective_morphism D D' u\<close>
    using po1.uniqueness_pc[OF r.k.injective_morphism_axioms m.injective_morphism_axioms 
                               po3.c.H.graph_axioms m'.injective_morphism_axioms
                               po3.g.morphism_axioms] po3
    by simp


  (* rhs *)
  interpret po4: pushout_diagram "interf r" "rhs r" D' H' idM m' f' h'
    using po4 by assumption

  obtain u where u:\<open>bijective_morphism D D' u\<close>
    using u
    by blast

  interpret u: bijective_morphism D D' u
    using u by assumption

  have \<open>\<exists>u. bijective_morphism H H' u\<close>
    by (meson bij_comp_bij_is_bij bijective_morphism.ex_inv po2.b_bij_imp_g_bij po4.b_bij_imp_g_bij r.r.bijective_morphism_axioms u)

  show ?thesis
    using \<open>\<exists>u. bijective_morphism H H' u\<close> u by blast
    
qed


end

locale direct_derivation_construction =
  r: rule r +
  d: deletion "interf r" G "lhs r" g idM +
  g: gluing "interf r" d.D "rhs r" g idM for G r g H +
assumes \<open>H = g.H\<close>
begin

corollary
    \<open>pushout_diagram (interf r) (lhs r) d.D G idM d.d g d.c'\<close> and \<open>pushout_diagram (interf r) (rhs r) d.D g.H idM g g.h g.c\<close> 
  using 
    d.po.pushout_diagram_axioms
    g.po.pushout_diagram_axioms
  by simp_all


(* sublocale direct_derivation r G g d.D d.d d.c' g.H g.h g.c ..
 *)
end

end