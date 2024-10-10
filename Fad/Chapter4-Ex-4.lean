import Fad.Chapter4

namespace Chapter4

--------------------- 4.4 ---------------------

/-
 Precisamos mostrar que qualquer algoritmo para calcular smallest (a, b) f t
 requer pelo menos ⌈log(n - 1)⌉ comparações, onde n = b - a + 1
 é o número de inteiros no intervalo [a, b].

Sabemos que a estratégia mais eficiente para resolver esse problema é a busca binária,
pois ela reduz o número de elementos no intervalo pela metade a cada comparação,
resultando no menor número de comparações.

Dessa forma, começamos com o intervalo [a, b].
Dividimos o intervalo ao meio, calculando o valor no ponto médio m = (a + b) / 2.
Comparamos t com f(m):
Se t ≤ f(m), sabemos que o valor x que estamos procurando está no intervalo [a, m].
Se t > f(m), o valor x que procuramos está no intervalo [m + 1, b].
Ao dividir o intervalo dessa forma, como falamos, reduzimos o número de possíveis soluções pela metade a cada comparação,
ou seja, reduzimos o número de elementos restantes pela metade até que reste apenas um único elemento.

Agora observe que a quantidade de divisões é proporcional ao logaritmo do número de elementos no intervalo.
pois uma árvore binária com altura h tem no máximo 2^h folhas (cada folha é um possível valor de x).

Para garantir que a árvore tenha folhas suficientes para cobrir todos os n - 1
valores possíveis no intervalo [a, b], precisamos de uma árvore com altura h tal que:
2^h ≥ n − 1

Ou seja, precisamos de uma altura que seja grande o suficiente para garantir que cada valor possível de x seja considerado.

Resolvendo essa desigualdade, chegamos que h  ≥ log_2​ (n−1)

Como estamos interessados no número inteiro de comparações, usamos o teto do logaritmo, o que nos dá:

 h ≥ ⌈ log⁡_2(n − 1)⌉

Isso nos diz que a altura mínima da árvore de decisão (ou seja, o número de comparações necessárias NO PIOR CASO)
é pelo menos ⌈log(n - 1)⌉.

Assim, mostramos que qualquer algoritmo para calcular smallest (a, b) f t
requer, no pior caso, pelo menos ⌈log(n - 1)⌉ comparações da forma t ≤ f(x)
-/

end Chapter4
