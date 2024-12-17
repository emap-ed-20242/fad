/-
    Exercício 12.5 Quais dos seguintes predicados sobre sequências não vazias de
    números positivos são fechados por prefixo e quais são fechados por sufixo?

    - leftmin xs = all (head xs ≤) xs
    - rightmax xs = all (≤ last xs) xs
    - ordered xs = and (zipWith (≤) xs (tail xs))
    - nomatch xs = and (zipWith (≠) xs [0..])

    Os predicados valem para listas unitárias?
-/

/-
    Para cada um dos predicados fornecidos, precisamos determinar se eles são fechados por prefixo ou por sufixo.
    VAmos lembrar dessas definições:
        - Um predicado é fechado por prefixo se, dado que ele vale para uma lista, ele também vale para qualquer
        prefixo da lista.
        - Um predicado é fechado por sufixo se ele vale para a lista e também para qualquer sufixo da lista.

    1. `leftmin xs = all (head xs ≤) xs`:
      - Verifica se todos os elementos de `xs` são maiores ou iguais ao primeiro elemento (`head xs`).
      - `Fechado por prefixo`: Sim, se a condição vale para a lista inteira, ela também vale para qualquer prefixo
      da lista, pois todos os prefixos terão seu primeiro elemento maior ou igual ao primeiro elemento da lista.
      - `Não fechado por sufixo`: Não, para qualquer sufixo de `xs`, a condição pode não ser verdadeira, pois o
      sufixo pode ter um valor maior do que o primeiro valor de `xs`.

    2. `rightmax xs = all (≤ last xs) xs`:
      - Verifica se todos os elementos de `xs` são menores ou iguais ao último elemento (`last xs`).
      - `Fechado por sufixo`: Sim, se a condição vale para a lista inteira, ela também vale para qualquer sufixo da
      lista, porque todos os elementos de qualquer sufixo serão menores ou iguais ao último elemento da lista.
      - `Não fechado por prefixo`: Não, para um prefixo de `xs`, o prefixo pode ter um valor maior do que o último
      valor de `xs`.

    3. `ordered xs = and (zipWith (≤) xs (tail xs))`:
      - Verifica se os elementos de `xs` estão em ordem não decrescente.
      - `Fechado por prefixo`: Sim, se a lista está ordenada, qualquer prefixo dela também estará ordenado.
      - `Fechado por sufixo`: Sim, se a lista está ordenada, qualquer sufixo dela também estará ordenado, pois a
      condição de ordem não decrescente é mantida em todos os sufixos.

    4. `nomatch xs = and (zipWith (≠) xs [0..])`:
      - Verifica se os elementos de `xs` são diferentes dos índices correspondentes da lista `[0..]`.
      - `Fechado por prefixo`: Sim, se a condição vale para a lista inteira, ela também vale para qualquer prefixo
      da lista, pois os elementos do prefixo ainda serão diferentes dos índices correspondentes da lista `[0..]`.
      - `Não fechado por sufixo`: Não, para um sufixo de `xs`, o predicado pode não valer, pois o sufixo pode ter 
      um valor igual ao índice correspondente.
-/
