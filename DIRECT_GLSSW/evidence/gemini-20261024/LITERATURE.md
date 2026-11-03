# External Literature Consulted During Audit

1. **Guevara, Lupsasca, Skinner, Strominger, Weil (GLSSW 2026)**
   - **Citation**: A. Guevara, A. Lupsasca, D. Skinner, A. Strominger, and K. Weil, *Single-minus gluon tree amplitudes are nonzero*, arXiv:2602.12176 (2026).
   - **URL**: `https://arxiv.org/abs/2602.12176`
   - **Date consulted**: 2026-10-24
   - **Purpose and Claim Verified**: Verified the half-collinear $(2,2)$ Klein-space / real planar momentum-polygon formulation of the single-minus tree-level Berends–Giele / marked-tree recursion:
     - External momenta $\widetilde\lambda_i = q_{i+1} - q_i$ form a closed polygon in $\mathbb{R}^2$ with spinor brackets $[u, v]$ given by planar 2D determinants.
     - Ordinary internal vertices $V^+$ and the single marked root vertex $V^-$ (or $\bar{V}$) are built from sign factors and Heaviside step functions $\Theta(\mp [K_u K_v]/[K_a K_b])$, which on generic non-collinear configurations reduce to the $\{0, \pm 1\}$ gate products $\prod_{\nu} \operatorname{sgn}(\cdot) \Theta(\cdot) = \prod_{\nu} \frac{D_\nu \mp H_\nu}{2}$.
     - Cyclic / root independence of the single-minus tree amplitude on the generic locus is a theorem of GLSSW (`arXiv:2602.12176`), which `direct_glssw_corner_proof.tex` takes as its sole external amplitude input (`GLSSWRootIndependence`).

2. **Labastida, Mariño, Vafa (LMV 2000)**
   - **Citation**: J. M. F. Labastida, M. Mariño, and C. Vafa, *Knots, links and branes at large $N$*, JHEP **11** (2000) 007, arXiv:hep-th/0010102.
   - **URL**: `https://arxiv.org/abs/hep-th/0010102`
   - **Date consulted**: 2026-10-24
   - **Purpose and Claim Verified**: Verified the HOMFLY skein normalization ($a H_{L_+} - a^{-1} H_{L_-} = z H_{L_0}$, $H_{\bigcirc} = 1$, split-union factor $(a - a^{-1})/z$) and the Lickorish–Millett lowest-$z$-row link factorization $[z^{1-k}] H_L = a^{-2\Lambda(L)} (a - a^{-1})^{k-1} \prod_{i=1}^k [z^0] H_{D_i}$ (Eq. 4.64 of LMV, corresponding to Lemma 4.2 / Eq. 4.11 of `direct_glssw_corner_proof.tex`).
