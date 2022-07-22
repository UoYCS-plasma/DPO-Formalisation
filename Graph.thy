theory Graph
imports Main
begin

record ('v,'e,'l,'m) pre_graph =
  nodes  :: "'v set"
  edges  :: "'e set"
  source :: "'e \<Rightarrow> 'v"
  target :: "'e \<Rightarrow> 'v"
  label  :: "'v \<Rightarrow> 'l"
  mark   :: "'e \<Rightarrow> 'm"


notation nodes  ("V\<^bsub>_\<^esub>")
notation edges  ("E\<^bsub>_\<^esub>")
notation source ("s\<^bsub>_\<^esub>")
notation target ("t\<^bsub>_\<^esub>")
notation label  ("l\<^bsub>_\<^esub>")
notation mark   ("m\<^bsub>_\<^esub>")

locale graph =
  fixes G :: "('v,'e,'l,'m) pre_graph"
  assumes 
    finite_nodes: "finite V\<^bsub>G\<^esub>" and
    finite_edges: "finite E\<^bsub>G\<^esub>" and
    source_integrity: "e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> s\<^bsub>G\<^esub> e \<in> V\<^bsub>G\<^esub>" and
    target_integrity: "e \<in> E\<^bsub>G\<^esub> \<Longrightarrow> t\<^bsub>G\<^esub> e \<in> V\<^bsub>G\<^esub>"

end