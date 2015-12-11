theory ListRefinement 
imports LinkedList AbstractList
begin

text{* Since both imported theories generate syntax for \verb$.content$, we have to disactivate
       one of the two notations in order to avoid syntactic ambiguities; the original internal name
       remains as alternative. *}
no_notation LinkedList.dot__content ("(_) .content")

term "X .content"

term "LinkedList.dot__content X"

end