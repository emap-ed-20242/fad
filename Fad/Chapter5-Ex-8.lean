/-
Em Haskell, a msort está definida assim:

msort :: Ord a => [a] -> [a]
msort [] = []
msort [x] = [x]
msort xs = merge (msort ys) (msort zs)
  where (ys, zs) = halve xs

onde a função halve divide uma lista
em duas partes aproximadamente iguais.

O exercício pergunta se ambos os casos base da definição
 recursiva de msort são necessários.

 E a resposta é que sim, ambos os casos bases são absolutamente necessários,
 pois se retirarmos qualquer um deles a função entraria em um loop infinito.

Veja que se não tivéssemos que msort [] = [], e em algum determinado
momento ficasse msort [], a função halve [] retornaria ([] , [])
dividindo uma lista vazia em 2 listas vazia e com isso fariamos
merge (msort []) (msort []) e dessa forma a funçao ficaria presa no msort [].

Agora se não tivéssemos que msort [x] = [x], e em algum determinado
momento ficasse msort [x] , a função halve [x] retornaria
([] , [x]) e com isso faríamos merge (msort []) (msort [x])
e dessa forma a função ficaria presa no msort [x].

Portanto ambos os casos bases são absolutamente necessários,
pois como vimos, sem qualquer um deles a função entra em um loop infinito.
-/
