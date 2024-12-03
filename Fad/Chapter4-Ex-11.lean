/-
4.1 - Consider the recurrences

B(n+1) = 2B(n/2) + Θ(n)
W(n+1) = W(n) + Θ(n)

for the best and worst cases for building a binary search tree by partitioning the input. Prove that B(n) = Θ(n log n) and W(n) = Θ(n2).


Resposta:

Podemos entender a recursão com essas funções: Em ambos o caso, se n = 0, nosso custo será O(1). Se n ≠ 0, faremos a recursão dada

def B : Nat → Nat
| 0     => 1
| (n+1) => 2 * B (n/2) + n

def W : Nat → Nat
| 0     => 1
| (n+1) => W n + n

· B → Vamos expandir a recursão para obersar um padrão:

  B(n+1) = 2 * B(n/2) + n
  B(n+1) = 2 * 2 * B((((n/2) - 1) / 2) + (n/2)-1)) + n

  Perceba que se continuaremos assim ficarão algo muito complexo. Por isso, vamos tentar provar o limite superior e o inferior, de modo que, se forem iguais, temos nosso θ.

  Continuaremos com a expansão acima, mas agora eliminaremos o -1. Fazendo isso acharemos o limite superior

  B(n+1) ≤ 2 * 2 * B(n/2/2 + n/2) + n
  B(n+1) ≤ 4 * B(n/4 + n/2) + n
  .           .
  .           .
  .           .
  B(n+1) ≤ 2^k * B(n/2^k) + kn

  A última iteração será com B(1). Logo, 2^k precisa ser igual a n. 2^k = n  =>  k = logn

  Temos, portanto:

  B(n+1) ≤ n * B(1) + n * logn

  Concluimos que B(n) = O(n * logn).

  Como achamos o limite superior apenas somando 1 em cada iteração, e fazemos isso logn vezez. Então, podemos ser conservadores e dizer que

  B(n+1) ≥ 1/2 * n * (B(1) + logn)
  B(n+1) ≥ 1/2 * n * logn

  E, assintoticamente falando, isso é Ω(n * logn)

  Concluimos, assi, que B(n) = θ(n * logn)


· W → Vamos expandir a recursão para observar um padrão:

  W(n+1) = W(n) + n
  W(n+1) = W(n-1) + (n-1) + n
  W(n+1) = W(n-2) + (n-2) + (n-1) + n
  .           .
  .           .
  .           .
  W(n+1) = W(0) + 0 + 1 + ... + (n-1) + n
  W(n+1) = 1 + 0 + 1 + ... + (n-2) + (n-1)
  W(n+1) = 1 + [(n+1) * n]/2
  W(n+1) = 1 + (n^2 - n)/2

  Considerando a notação θ, isso claramente é θ(n^2)
-/
