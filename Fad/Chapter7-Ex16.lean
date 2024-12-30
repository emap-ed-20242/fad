import Fad.«Chapter7-Ex12»

namespace Chapter7

/- Exercício 16 -/

def ds_UR := [100, 50, 20, 15, 5, 1]


#eval mkchange_greedy ds_UR 30 -- [0, 0, 1, 0, 2, 0]


#eval mkchange2 ds_UR 30       -- [0, 0, 0, 2, 0, 0]


/-
  Como vimos, com o exemplo, não é sempre que o algoritmo
  guloso funciona perfeitamente. Neste caso, e como
  geralmente acontece, o motivo é a existência de moedas
  que apresentam fatores diferentes, no caso o 15, assim
  temos formas diferentes de formar alguns valores, sendo
  que alguns deles (Ex 30, 80) não são necesáriamente com
  as moedas de maior valor.
-/

end Chapter7
