/-
    Exercício 12.4 Detalhe a prova de que:
    filter (all ok) · parts = foldr (concatMap · okextendl) [[]]
    fornecido que ok é fechado por sufixo.
    Dica: provavelmente é melhor expressar a condição de fusão em termos de compreensões de lista.)
-/


/-
    Temos que provar que a expressão `filter (all ok) · parts` é equivalente a `foldr (concatMap · okextendl) [[]]`,
    dado que a função `ok` é fechada por sufixo. Vamos usar uma condição de fusão para mostrar que essas duas expressões
    são idênticas. A condição de fusão pode ser expressa em termos de compreensão de listas.

    A condição de fusão pode ser escrita da seguinte forma:

                                        `[p' | p ← ps, p' ← extendl x p, all ok p']`,

    que é quivalente a:

                                  `[p' | p ← ps, all ok p, p' ← extendl x p, ok (head p')]`.

    Esta condição deve ser válida para todas as partições `ps` de uma lista.

    Para provar a equivalência, precisamos mostrar que as operações feitas pela função `cons` e pela função `glue` no
    exercício satisfazem essa condição. Vamos trabalhar separadamente com cada uma dessas operações.

    1. A operação `cons` (adiciona o elemento `x` no início da partição):

        Queremos mostrar que a seguinte expressão:

                                        `[cons x p | p ← ps, all ok (cons x p)]`

        é equivalente a:

                                `[cons x p | p ← ps, all ok p ∧ ok (head (cons x p))]`.

        - Sabemos que `cons x p = [x] : p`. Ou seja, a operação `cons` adiciona o elemento `x` no início da lista `p`.
        Além disso, a condição `all ok (cons x p)` significa que todas as sublistas em `cons x p` devem satisfazer a
        condição `ok`. Como `cons x p` resulta em uma lista de listas onde o primeiro elemento é `[x]`, a condição
        `all ok (cons x p)` é equivalente a `all ok p ∧ ok [x]`, ou seja, a condição sobre a partição de `p` e a
        condição de que o primeiro elemento de `cons x p` (que é `[x]`) também satisfaz a condição `ok`.

        --> Portanto, a primeira condição está validada.

    Agora, vamos ver o segundo ponto:

    2. A operação `glue` (adiciona o elemento `x` à primeira sublista da partição):

        Queremos mostrar que a seguinte expressão:

                              `[glue x (s : p) | s : p ← ps, all ok (glue x (s : p))]`

        é equivalente a:

                      `[glue x (s : p) | s : p ← ps, all ok (s : p) ∧ ok (head (glue x (s : p)))]`

        - Novamente, sabemos que `glue x (s : p) = (x : s) : p`. Ou seja, a operação `glue` adiciona o elemento `x` ao
        início da sublista `s` dentro da lista `p`. Outrossim, a condição `all ok (glue x (s : p))` significa que todas
        as sublistas em `glue x (s : p)` devem satisfazer a condição `ok`. Como `glue x (s : p)` resulta em uma lista com
        `x` no início da sublista `s`, a condição `all ok (glue x (s : p))` pode ser reescrita como `all ok p ∧ ok (x : s)`,
        que é equivalente a `all ok (s : p) ∧ ok (x : s)`, uma vez que, dada a propriedade de fechamento por sufixo de `ok`,
        a condição `ok (x : s)` implica que `ok s`.

        Dessarte, a segunda condição também é validada.

    Uma vez que mostramos que ambas as condições de fusão são satisfeitas para as operações `cons` e `glue`, concluímos que

                            `filter (all ok) · parts = foldr (concatMap · okextendl) [[]]`,

    ou seja, a expressão `filter (all ok) · parts` é de fato equivalente a `foldr (concatMap · okextendl) [[]]` quando `ok`
    é fechado por sufixo.
-/
