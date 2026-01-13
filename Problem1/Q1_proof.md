# Proof of Q1
## Constructure of $\mathcal{F}$
For any $x\in E$, by condition (A), there exists $\alpha \in I$ such that $x\in E_\alpha$, so we can define:
$$
\mathcal{F} (x) \coloneqq f_\alpha (x).
$$

## $\mathcal{F}$ is well defined
Suppose $x\in E_\alpha \cap E_\beta$, then by condition (B), $f_\alpha (x) = f_\beta (x)$, so the definition does not depend on the choice of $\alpha$.

## Linearly
Let $(x,y)\in E^2$ and $\lambda\in K$. By condition (C), there exists $\gamma \in I$, such that $(x,y)\in E_\gamma^2$. Then,
$$
\mathcal{F} (x + \lambda y) = f_\gamma (x + \lambda y) = f_\gamma (x) + \lambda f_\gamma (y) = \mathcal{F} (x) +\lambda \mathcal{F} (y).
$$

## Uniqueness
Let $\mathcal{G}$ be another linear mapping that satisfies the condition. For any $x\in E$, suppose $x\in E_\alpha$, then,
$$ \mathcal{G}(x) = f_\alpha (x) = \mathcal{F}(x).
$$
So, $\mathcal{G}=\mathcal{F}$.