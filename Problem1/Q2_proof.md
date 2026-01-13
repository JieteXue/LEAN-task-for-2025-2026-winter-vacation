# Proof of Q2
Since $\mathcal{F}$ is linear, it is suffices to check that $\mathcal{F}$ is bounded.

(in lean, use theorem: continuous_of_linear_of_bound.)

We take $x\in E_\alpha$. By definition,
$$
||f_\alpha|| = \sup_{x\in E_\alpha} \frac{||f_\alpha (x)||}{||x||}\le C,
$$
so,
$$
||\mathcal{F}(x)|| = ||f_\alpha (x)|| \le ||f_\alpha||\cdot ||x|| \le C \cdot ||x||.
$$

Hence,
$$ ||\mathcal{F}|| =\sup_{x\in E} \frac{||\mathcal{F}(x)||}{||x||} \le C,$$
$\mathcal{F}$ is bounded.