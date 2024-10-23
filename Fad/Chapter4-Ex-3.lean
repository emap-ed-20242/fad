import Fad.Chapter4

namespace Chapter4


/-
Vamos provar por indução que

T(x) = ⌈log(n-1)⌉.

Para o caso base (n=2)

T(2) = ⌈log(2-1)⌉ = ⌈log(1)⌉ = ⌈0⌉ = 0.

Supondo valido para k < n, vamos provar para n.
Como ⌈(n+1)/2⌉ < n, vale a hipotese de indução, então temos que provar que:

T(n) = ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 = ⌈log(n-1)⌉.

Podemos mostrar por desigualdade indireta, mostrando que o lado esquerdo é
menor que k se e somente o lado direito é menor que k, para qualquer k natural.
Pelo lado direito temos que ⌈log(n-1)⌉ <= k <=> n-1 <= 2^k.
Pelo lado esquerdo:

    ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 <= k <=> ⌈log(⌈(n+1)/2⌉ -1)⌉ <= k-1,
                                 <=> log(⌈(n+1)/2⌉ -1) <= k-1,
                                 <=> ⌈(n+1)/2⌉ -1 <= 2^(k-1),
                                 <=> ⌈(n+1)/2⌉ <= 2^(k-1) + 1,
                                 <=> (n+1)/2 <= 2^(k-1) + 1,
                                 <=> n+1 <= 2^k + 2,
                                 <=> n-1 <= 2^k.

O que completa a prova, uma vez que ambos os lados chegam na mesma proposição.
-/

end Chapter4
