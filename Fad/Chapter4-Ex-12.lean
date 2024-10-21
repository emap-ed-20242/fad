import Fad.Chapter4

namespace Chapter4

/- Show that log (n!) = Ω(n log n) without using
 Stirling’s approximation -/

/-
Precisamos mostrar que log(n!) >= c * (n log n)

Para n par
1. Expandindo o logaritmo do fatorial como a soma dos logaritmos de cada termo:

log(n!) = log(n) + log(n-1) + log(n-2) + ... + log(1)

2. Focando na metade maior: Em vez de trabalhar com todos os termos,
 foco nos primeiros n/2 termos:

log(n!) >= log(n) + log(n-1) + log(n-2) + ... + log(n/2)

3. Cada termo dessa metade é maior ou igual a n/2
   então substituo todos por n/2

log(n!) >= log(n/2) + log(n/2) + log(n/2) + ... + log(n/2)
log(n!) >= n/2 log(n/2)

4. Como n/2 log(n/2) >= n/4 log(n) para n >= 4, então

log(n!) >= 1/4 * n log(n) para n >= 4

Para n ímpar é similar pegando até o (n+1)/2 termo
1. Expandindo o logaritmo do fatorial como a soma dos logaritmos de cada termo:

log(n!) = log(n) + log(n-1) + log(n-2) + ... + log(1)

2. Focando na metade maior: Em vez de trabalhar com todos os termos,
 foco nos primeiros (n+1)/2 termos:

log(n!) >= log(n) + log(n-1) + log(n-2) + ... + log[(n+1)/2]

3. Cada termo dessa metade é maior ou igual a (n+1)/2
   então substituo todos por (n+1)/2

log(n!) >= log[(n+1)/2] + log[(n+1)/2] + log[(n+1)/2] + ... + log[(n+1)/2]
log(n!) >= (n+1)/2 log[(n+1)/2]

4. Como (n+1)/2 log[(n+1)/2] >= (n+1)/4 log(n+1) para n >= 3, então

log(n!) >= (n+1)/4 log(n+1) >= 1/4 * nlog(n) para n >= 3


Portanto log(n!) >= 1/4 * nlog(n) para n >= 3, assim log(n!) = Ω(nlogn)

-/
end Chapter4
