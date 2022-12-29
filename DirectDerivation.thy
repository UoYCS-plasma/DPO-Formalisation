theory DirectDerivation
  imports Rule Gluing Deletion
begin

locale direct_derivation =
  r: rule L K R +
  d: deletion K G L g idM +
  g: gluing K d.D R g idM for G L K R g

begin

corollary 
    \<open>pushout_diagram K L d.D G idM d.d g d.c'\<close> and \<open>pushout_diagram K R d.D g.H idM g g.h g.c\<close> 
  using 
    d.po.pushout_diagram_axioms
    g.po.pushout_diagram_axioms
  by simp_all

end

notation direct_derivation ("_ \<Rightarrow>\<^bsub>_ \<leftarrow> _ \<rightarrow> _, _\<^esub>")

end