namespace Chapter4

/- 4.16 | Breno Russo Guedes de Souza Melo
  Give the definition of balanceL.
  A função balanceL serve para equilibrar uma árvore binária quando a
  subárvore da direita está muito mais alta que a da esquerda.
  Ela vai descendo pela subárvore da direita e ajustando as subárvores
  ao longo do caminho até achar um ponto onde as alturas ficam mais próximas.
  Isso garante que a árvore fique mais balanceada, mesmo quando uma das subárvores
  é bem maior, ajudando a manter a árvore eficiente para fazer buscas e inserções.
-/
def balanceL : Tree α → α → Tree α → Tree α
| t1 x (Node l y r) :=
  if height l ≥ height t1 + 2 then
    balance (balanceL t1 x l) y r
  else
    balance (Node t1 x l) y r
| t1 x Leaf := Node t1 x Leaf

end Chapter4
