import Fad.Chapter5

namespace Chapter5

/- 5.7 : Provar que T(m,n) <= m + n -/

/-
Prova por indução dupla:

Base da indução:
1) Quando m = 0, temos T(0, n) = 0, o que satisfaz a desigualdade 0 <= 0 + n.
2) Quando n = 0, temos T(m, 0) = 0, o que satisfaz a desigualdade 0 <= m + 0.

Passo indutivo:
Suponha que a desigualdade seja válida para T(m', n) <= m' + n e T(m, n') <= m + n', onde m' < m e n' < n. Agora, provamos que ela vale para T(m, n).

A relação de recorrência dada é:
T(m, n) = 1 + max(T(m-1, n), T(m, n-1))

Pela hipótese de indução, temos:
T(m-1, n) <= (m-1) + n
T(m, n-1) <= m + (n-1)

Substituindo na recorrência:
T(m, n) <= 1 + max((m-1) + n, m + (n-1))

Avaliando o máximo:
max((m-1) + n, m + (n-1)) = m + n - 1

Portanto:
T(m, n) <= 1 + (m + n - 1) <= m + n

Conclusão:
Por indução dupla, mostramos que T(m, n) <= m + n para todos os m e n.
-/


end Chapter5
