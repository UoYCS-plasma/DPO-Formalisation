theory Rule
  imports Graph Morphism
begin

locale rule =
  l: inclusion_morphism 
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L 
    b\<^sub>V b'\<^sub>V b\<^sub>E b'\<^sub>E +
  r: inclusion_morphism     
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R 
    q\<^sub>V q'\<^sub>V q\<^sub>E q'\<^sub>E
  for 
    V\<^sub>K E\<^sub>K s\<^sub>K s'\<^sub>K t\<^sub>K t'\<^sub>K l\<^sub>K l'\<^sub>K m\<^sub>K m'\<^sub>K 
    V\<^sub>L E\<^sub>L s\<^sub>L s'\<^sub>L t\<^sub>L t'\<^sub>L l\<^sub>L l'\<^sub>L m\<^sub>L m'\<^sub>L
    V\<^sub>R E\<^sub>R s\<^sub>R s'\<^sub>R t\<^sub>R t'\<^sub>R l\<^sub>R l'\<^sub>R m\<^sub>R m'\<^sub>R
    b\<^sub>V b'\<^sub>V b\<^sub>E b'\<^sub>E 
    q\<^sub>V q'\<^sub>V q\<^sub>E q'\<^sub>E


end