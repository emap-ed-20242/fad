-- Exercício 12.1 Quantas partições de uma lista de tamanho n > 0 existem?

/-

Explicação intuitiva:
    Para uma lista de comprimento n > 0, queremos determinar o número de maneiras de particioná-la.
    Uma partição de uma lista divide a lista em sublistas consecutivas. Por exemplo, para a lista
    [a, b, c], as possíveis partições são:
        [a, b, c], [a], [b, c], [a, b], [c], [a], [b], [c].
    Observamos que entre cada par de elementos consecutivos da lista, podemos ou não fazer uma
    partição. Como há n - 1 posições possíveis para dividir uma lista de comprimento n, e cada
    posição tem 2 opções (dividir ou não), o número total de partições é 2^(n - 1).

Formalização matemática:
    Considere uma lista L de n elementos, onde n > 0. Para particionar L, consideramos as n - 1
    posições entre os elementos onde podemos inserir uma divisão. Em cada uma dessas posições, temos
    duas opções: Inserir uma divisão (partição) ou não inserir uma divisão. Portanto, para cada uma
    das n - 1 posições, temos 2 escolhas independentes.
    Portanto, o número total de combinações de escolhas é 2^(n - 1).

-/
