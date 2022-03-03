theory DirectDerivation
  imports Rule Deletion Gluing
begin
 
locale direct_derivation =
  r: rule 
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L 
    V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R
    b\<^sub>V b'\<^sub>V b\<^sub>E b'\<^sub>E 
    q\<^sub>V q'\<^sub>V q\<^sub>E q'\<^sub>E +

  G: graph V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G +

  k: injective_morphism 
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L 
    V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G
    f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E +

  d: deletion 
     V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L
     V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
     V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G 
     f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E +

  g: gluing
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K
    V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R
    d.V d.E d.s _ d.t _ d.l _ d.m _

  for 
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L 
    V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R 
    b\<^sub>V b'\<^sub>V b\<^sub>E b'\<^sub>E 
    q\<^sub>V q'\<^sub>V q\<^sub>E q'\<^sub>E
    V\<^sub>G E\<^sub>G s\<^sub>G s'\<^sub>G t\<^sub>G t'\<^sub>G l\<^sub>G l'\<^sub>G m\<^sub>G m'\<^sub>G

end