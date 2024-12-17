-- Exercício 12.2 Por que a cláusula `parts [] = [[]]` é necessária na primeira definição de `parts`

/-

Explicação intuitiva:
    A cláusula `parts [] = [[]]` é essencial na definição inicial da função `parts` porque garante que a
    lista vazia tenha exatamente uma partição válida: ela própria. Sem essa cláusula, ao definir `parts xs`
    apenas com a cláusula recursiva `parts xs = [ys :: yss | (ys, zs) ← splits xs, yss ← parts zs]`,
    obteríamos `parts [] = []`. Isso levaria a um problema onde, para qualquer lista `xs`, a aplicação da
    definição recursiva resultaria em `parts xs = []`, eliminando todas as possíveis partições das listas
    não vazias.

Formalização matemática:
    - Caso base:
        Definimos `parts [] = [[]]` para assegurar que a lista vazia possui uma única partição válida que
        é a própria lista vazia.

    - Passo indutivo:
        Para uma lista não vazia `xs`, a função `parts xs` é definida em termos das partições das sublistas
        `zs` obtidas após realizar um split `(ys, zs)`.

        Se omitirmos o caso base `parts [] = [[]]`, então, ao tentar particionar uma lista que eventualmente
        reduz a uma lista vazia, `parts zs` seria `[]`. Consequentemente, a compreensão de listas

                                `[ys :: yss | (ys, zs) ← splits xs, yss ← parts zs]`

        também resultaria em `[]`, eliminando todas as partições possíveis.

-/
