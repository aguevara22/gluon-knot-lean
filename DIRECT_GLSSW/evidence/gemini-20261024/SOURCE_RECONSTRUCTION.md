# Independent Source Reconstruction

**Manuscript**: `project/reference/direct_glssw_corner_proof.tex`
**SHA-256**: `32689ac5920b295347579bbf2f59883a0163bab8368e18c530b4fd8484cabefd`
**Title**: *Marked polygon currents and the HOMFLY corner: A direct sewing argument for the GLSSW state sum* (dated 13 September 2026)
**Reconstructed before inspecting prior audit reports or producer graph**: Yes.

---

## 1. Main Theorem Statement and Quantifier Scope

The manuscript's main theorem is **Theorem 1.1 (Direct sewing identity)** (lines 157–162), completed on the entire generic locus in **Section 5** (lines 1246–1290):

> **Theorem 1.1 (Direct sewing identity).**
> For every generic oriented polygon $P = (q_0, \ldots, q_{n-1})$ in the oriented affine plane $\mathbb{R}^2$ ($n \ge 3$, satisfying G1 and G2), assuming GLSSW root independence (cyclic invariance of the finite marked-tree amplitude), the GLSSW amplitude satisfies
> $$A(P) = C(P)$$
> with conventions (1.1)–(1.5).

### Outer-to-Inner Logical and Quantifier Structure
1. **Global Normalized HOMFLY Evaluator ($H$)**:
   - The HOMFLY invariant $H_L(a, z) \in \mathbb{Z}[a^{\pm 1}, (a - a^{-1})/z, z]$ (or Laurent series/polynomial ring in $a, z$ indexed by $(d_a, d_z) \in \mathbb{Z} \times \mathbb{Z}$) is defined globally for all oriented PL link diagrams prior to and independently of any polygon $P$ or the GLSSW root-independence hypothesis.
   - Its defining conventions (Eq. 1.2, lines 109–115; Section 4.3, lines 988–1037) are:
     - Unknot normalization: $H_{\bigcirc} = 1$.
     - Skein relation: $a H_{L_+} - a^{-1} H_{L_-} = z H_{L_0}$.
     - Decoupled unknot / split-union relation: $H_{L \sqcup \bigcirc} = \frac{a - a^{-1}}{z} H_L$ (so a $k$-component split unlink has value $\bigl(\frac{a - a^{-1}}{z}\bigr)^{k-1}$).
     - Descending skein evaluation makes $H$ uniquely determined on all oriented PL link diagrams, invariant under diagram isomorphism, choice of basepoint traversal order, and regular colinear vertex deletion/insertion.
2. **Global GLSSW Root Independence (RI) Hypothesis**:
   - Stated as an explicit input from GLSSW [1] (lines 87–89, 189–190): for every generic cyclic polygon $P$, the finite marked-tree amplitude $A(P)$ is independent of which edge of $P$ is chosen as the marked root edge.
   - Notably, RI is assumed *only* as cyclic/root invariance of the finite marked-tree recursion—it does *not* assume equality with any knot invariant, wall-crossing law, or chamber constancy of $C(P)$.
3. **Universal Quantification over the Full Generic Locus**:
   - For every integer $n \ge 3$ and every cyclic polygon $P = (q_0, \ldots, q_{n-1}) : \mathrm{Fin}\,n \to \mathbb{R}^2$ satisfying **(G1)** and **(G2)**:
     $$A(P) = C(P).$$

---

## 2. Domain and Standing Conventions

### 2.1 Parent Polygon and the Generic Locus (Lines 61–73)
- **Carrier**: An oriented cyclic polygon $P = (q_0, \ldots, q_{n-1})$ with $n \ge 3$ vertices in the oriented affine plane $\mathbb{R}^2$.
- **Edges**: Directed edges $e_i$ from $q_i$ to $q_{i+1}$ (indices $\bmod\,n$), with edge vectors $\widetilde\lambda_i = q_{i+1} - q_i$.
- **Turns and Left-Turn Count**:
  - A corner at vertex $q_i$ is a **left turn** iff $\det(\widetilde\lambda_{i-1}, \widetilde\lambda_i) > 0$, and a **right turn** iff $\det(\widetilde\lambda_{i-1}, \widetilde\lambda_i) < 0$.
  - $\ell(P)$ is the number of left turns of $P$.
  - A polygon is **uniform** iff every turn is left or every turn is right.
- **Generic Locus Conditions**:
  - **(G1) Noncollinearity**: No three distinct original vertices $q_i, q_j, q_k$ ($i, j, k$ pairwise distinct in $\mathrm{Fin}\,n$) are collinear; equivalently, $\det(q_j - q_i, q_k - q_i) \ne 0$.
  - **(G2) No Triple Intersections**: No point in $\mathbb{R}^2$ lies in the relative interiors of three distinct edges of $P$.
  - **Consequences of G1 + G2**: All vertices are distinct, all corner turns are nonzero ($\ne 0, \pi$), no vertex lies on a non-incident edge, and all intersections between non-incident edges occur at transverse interior double points (crossings).
- **Auxiliary Generic Domain vs. Full Generic Locus (Lines 73–83, 1266–1290)**:
  - Sections 2–4 first establish $A(P) = C(P)$ on an open dense *auxiliary generic domain* inside each chamber of the generic locus (where auxiliary determinants involving crossing points and moving secant lines are also nonzero).
  - Section 5 (lines 1266–1290) removes the auxiliary genericity restriction by proving that the auxiliary generic domain is dense in the generic locus and that both $A(P)$ and $C(P)$ are locally constant (chamber-constant) on the full G1–G2 generic locus.
  - Therefore, the final theorem holds on the **entire G1–G2 generic locus** with no auxiliary-genericity hypothesis.

---

## 3. Left-Hand Side: The GLSSW Amplitude $A(P)$

### 3.1 Published GLSSW Recursion and Equivalent Matrix/Tree Formulations (Lines 84–94, 203–240)
- In GLSSW (`arXiv:2602.12176`, `\vseven{threebrackets}`, `\vseven{amplitudevertex}`, `\vseven{amplitude}`), a cyclic polygon $P = (q_0, \ldots, q_{n-1})$ is opened at a chosen root edge (for $A(P)$, root edge $0$, giving the open boundary word $(w_0, \ldots, w_{n-1}) = (q_1, \ldots, q_{n-1}, q_0)$ of $n-1$ edges joining $n$ vertices $w_0, \ldots, w_N$ with $N = n-1$).
- **Determinant / Spinor-Bracket Sign Convention (Eq. 2.1, line 206)**:
  - For $0 \le i < k < j \le N$:
    $$H(i, k, j) = \operatorname{sgn}\det(w_k - w_j, w_i - w_j) \in \{+1, -1\}.$$
  - In the spinor-bracket gate formulation (`DirectGLSSW/SpinorGates.lean` / GLSSW `\vseven{threebrackets}`), $[u, v] = -\det(u, v)$, and at each internal cut $r_\nu$ of a subdivision $i = r_0 < r_1 < \cdots < r_m = j$:
    - The near vector is $u_\nu = (w_{r_\nu} - w_{r_{\nu-1}}) \text{ or } (w_{r_{\nu+1}} - w_{r_\nu})$ with near sign $D(r_{\nu-1}, r_\nu, r_{\nu+1}) = H(r_{\nu-1}, r_\nu, r_{\nu+1})$.
    - The far sign is $H(i, r_\nu, j)$.
    - Because $D, H \in \{+1, -1\}$ are strictly nonzero under G1, the GLSSW step-function gates satisfy (Eq. 2.2, line 213):
      $$D \Theta(-H D) = \frac{D - H}{2}, \qquad D \Theta(H D) = \frac{D + H}{2}.$$
- **Ordinary Preamplitude / Current $b_{ij}$ and Marked Amplitude $A$ (Eqs. 2.3–2.4, lines 222–235)**:
  - For any strictly upper triangular array $X$ on $\{0, \ldots, N\}$:
    $$\Phi_{D, H}(X)_{ij} = \sum_{i = r_0 < r_1 < \cdots < r_m = j} \left(\prod_{\nu=1}^{m-1} \frac{D(r_{\nu-1}, r_\nu, r_{\nu+1}) - H(i, r_\nu, j)}{2}\right) \prod_{\nu=1}^m X_{r_{\nu-1}, r_\nu}.$$
  - On one-edge intervals $j = i + 1$, $E_{i, i+1} = 1$, and $E_{ij} = 0$ for $j > i + 1$.
  - The ordinary preamplitude/current $b$ satisfies $\Phi_{D, H}(b) = E$, i.e. $b_{i, i+1} = 1$ and for $j - i \ge 2$:
    $$b_{ij} = -\sum_{\substack{i = r_0 < \cdots < r_m = j \\ m \ge 2}} V^+_{\text{ord}}(r_0, \ldots, r_m) \prod_{\nu=1}^m b_{r_{\nu-1}, r_\nu}.$$
    (Ordinary internal vertices carry $-V^+$ and exclude unary $m=1$ insertions.)
  - The marked root carries $V^-$ and retains the unary ($m=1$) term:
    $$A(w_0, \ldots, w_N) = \Phi_{D, -H}(b)_{0N} = -\sum_{\substack{0 = r_0 < \cdots < r_m = N \\ m \ge 1}} \bigl(V^+_{\text{ord}}(r_0, \ldots, r_m) - V^-_{\text{marked}}(r_0, \ldots, r_m)\bigr) \prod_{\nu=1}^m b_{r_{\nu-1}, r_\nu}.$$
    (Since $\sum_{m \ge 1} V^+_{\text{ord}} \prod b = \Phi_{D, H}(b)_{0N} = E_{0N} = 0$ for $N \ge 2$, $\Phi_{D, -H}(b)_{0N} = -\sum_{m \ge 1} (V^+ - V^-) \prod b$.)

---

## 4. Right-Hand Side: Separating Decompositions, Daughters $K_Q$, and Corner State Sum $C(P)$

### 4.1 Crossings, Separating Supports $\mathcal{D}(P)$, and Uniform Supports $\mathcal{D}_{\mathrm{u}}(P)$ (Lines 129–155)
- **Crossings**: Unordered pairs of distinct non-adjacent edges $\{e_i, e_j\}$ whose open segments intersect transversely at a point $p_c \in \mathbb{R}^2$.
- **Separating Supports $\mathcal{D}(P)$**: Subsets $S$ of crossings of $P$ whose chords on the oriented parameter circle of $P$ are pairwise non-alternating (do not interlace).
- **Oriented Smoothing $P_S$**: Smoothing every crossing $c \in S$ according to strand orientation partitions the event segments of $P$ into $|S| + 1$ closed oriented polygonal components $Q \in P_S$.
- **Uniform Daughter Condition**: A daughter component $Q \in P_S$ is **uniform** iff all of its corners (both original polygon vertices visited by $Q$ and smoothed crossing corners from $S$) turn in the same direction (all left turns, or all right turns).
- **Uniform Separating Supports $\mathcal{D}_{\mathrm{u}}(P)$**:
  $$\mathcal{D}_{\mathrm{u}}(P) = \{S \in \mathcal{D}(P) \mid \forall Q \in P_S,\ Q \text{ is uniform}\}.$$

### 4.2 Daughter Positive Diagram $K_Q$ on the Full G1–G2 Domain (Lines 98–107, 136–139, 838–846)
- For each daughter $Q \in P_S$:
  - **Vertices and Arcs**: $Q$ is an oriented closed polygonal curve formed by the cycle of event segments in the orbit of the smoothing dart permutation for $S$. Notice that $Q$ may traverse multiple collinear event segments only if they came from different edges, or rather: as noted in lines 838–846, a component of a separating smoothing contains at most one segment of any original edge, *Wait*—within that single segment of an original edge, $Q$ may still have intermediate vertices or crossings with other edges! Specifically, an original edge segment in $Q$ starts at an original vertex or a smoothed crossing in $S$, ends at an original vertex or a smoothed crossing in $S$, and along its interior may pass through *unsmoothed* crossings (either retained self-crossings of $Q$ or ignored mixed crossings with other daughters $Q' \ne Q$). Those points along the same original edge are **collinear**! Therefore, $Q$ viewed with event vertices does **not** satisfy 3-point noncollinearity (G1), even when the parent $P$ satisfies G1 and G2.
  - **Retained Self-Crossings**: Only crossings of $P$ outside $S$ whose two crossing strands both belong to $Q$ are retained as crossings of $K_Q$. Crossings in $S$ are smoothed into corners of $Q$; crossings outside $S$ between $Q$ and a different component $Q' \ne Q$ are ignored (treated as ordinary non-crossing continuation points on $Q$).
  - **Positive Lift (Eq. 1.1, line 100)**: At every retained self-crossing of $Q$, the overpassing strand is chosen so that
    $$\det(t_{\mathrm{over}}, t_{\mathrm{under}}) > 0,$$
    where $t_{\mathrm{over}}, t_{\mathrm{under}}$ are the forward tangent vectors of the two branches of $Q$ at the crossing.

### 4.3 Prescribed Corner Degree $d_Q$ and Corner Coefficient $c(Q)$ (Lines 116–127)
- For each daughter $Q \in P_S$:
  - $m_Q$: number of retained self-crossings of $K_Q$.
  - $r(Q) \in \mathbb{Z}$: signed rotation number (total tangent turning number divided by $2\pi$) of a smooth rounding of $Q$ using corner turns of magnitude strictly less than $\pi$.
  - $R_Q = |r(Q)|$.
  - Prescribed $a$-degree:
    $$d_Q = 1 - m_Q - R_Q = 1 - m_Q - |r(Q)|.$$
  - Prescribed corner coefficient (Eq. 1.3, line 120):
    $$c(Q) = [a^{d_Q} z^0] H_{K_Q}(a, z).$$
  - Crucially, $d_Q$ is the **prescribed** integer $1 - m_Q - |r(Q)|$, *not* defined as $\min\deg_a [z^0] H_{K_Q}$.

### 4.4 Corner State Sum $C(P)$ (Eq. 1.5, Lines 143–148)
- The state sum is
  $$C(P) = (-1)^{\ell(P)} \sum_{S \in \mathcal{D}_{\mathrm{u}}(P)} (-1)^{|S|} \prod_{Q \in P_S} c(Q).$$

---

## 5. Summary of the Manuscript's Proof Architecture

1. **Section 2 (Finite currents and transport of a marked endpoint)**:
   - Establishes near-data gauge freedom $\Phi_{D, H} = \mathcal{F}_H \circ \mathcal{G}_D$ (Lemma 2.1).
   - Proves the exact short-edge insertion identity $A(\text{polygon with } B) = \kappa A(\text{core})$ (Lemma 2.2) and exposed left-corner truncation sign flip (Lemma 2.3).
   - Computes the endpoint cut-list jump $\Delta F$ across secant lines (Section 2.3) and derives the line-cap Wronskian / nilpotent jump identity $S_C X + X S_C + 2 X S_C X = 0$, $K S_C + S_C K = 2 S_C$ for $K = (I + X)^{-1}$ (Lemma 2.4, Eqs. 2.25–2.27).
   - Deduces **Theorem 2.5 (Mixed-edge recursion)**: if an edge $e$ of $P$ has opposite endpoint turns, then $A(P) = \sum_{\varnothing \ne T \subset \{\text{crossings on } e\}, T \text{ separating}} (-1)^{|T|+1} \prod_{Q \in P_T} A(Q)$.
   - Establishes boundary crossing transport $\Delta M = \delta_c A(c, q_1, \ldots, q_k) M(c, q_{k+1}, \ldots, q_n)$ (Lemma 2.6) and the short-edge turn projector at $q_1$: factor $-1$ at a left turn, $0$ at a right turn (Lemma 2.7).
2. **Section 3 (Separating-smoothing inversion and nonuniform support)**:
   - Defines the separating primitive $\Gamma_X(P) = \sum_{T \in \mathcal{D}(P)} (-1)^{|T|} \prod_{Q \in P_T} X(Q)$ and proves Boolean inclusion-exclusion inversion $X(P) = \sum_{S \in \mathcal{D}(P)} \prod_{Q \in P_S} \Gamma_X(Q)$ (Lemma 3.1).
   - Proves **Proposition 3.2**: if $P$ is not uniform, it has a mixed edge $e$, and grouping $\Gamma_A(P)$ by crossings outside $e$ cancels identically by Theorem 2.5, so $\Gamma_A(P) = 0$.
3. **Section 4 (The uniform primitive is the HOMFLY corner)**:
   - For a uniformly left-turning polygon $Q$ (after optional exposed-corner truncation, which preserves $\nu_A(Q) = (-1)^{\ell(Q)} \Gamma_A(Q)$ and $c(Q)$), initializes the open-arc primitive current $\Gamma_M(\gamma) = \Gamma_A(Q)$ on an exposed supporting edge.
   - Proves **Lemma 4.1**: across a boundary crossing $c$ on the first physical edge, subtracting separating smoothings cancels first-over jumps ($\delta = +1$) and yields $\Delta \Gamma_M = \frac{\delta - 1}{2} \Gamma_A(Q_c) \Gamma_M(\gamma_c)$, so $f(\gamma) = (-1)^{v(\gamma)} \Gamma_M(\gamma)$ satisfies $f_{\mathrm{before}} = f_{\mathrm{after}} - \nu_A(Q_c) f(\gamma_c)$ at first-under crossings ($\delta = -1$), is invariant across original left corners, and equals $1$ at the terminal 1-edge arc.
   - Proves **Lemma 4.2 (Lowest link row)** $[z^{1-k}] H_L = a^{-2\Lambda(L)} (a - a^{-1})^{k-1} \prod_{i=1}^k h_{D_i}(a)$ and the framed $z^0$-row skein relation $\mathcal{B}_D = \mathcal{B}_{D^{\mathrm{sw}}} + \mathcal{B}_{D_L} \mathcal{B}_{D_R}$ for $\mathcal{B}_D(a) = a^{w(D)+r(D)}(a - a^{-1}) [z^0] H_D(a, z)$.
   - Uses Whitney's turning-number / writhe identity $w(D_{\mathrm{terminal}}) + r(D_{\mathrm{terminal}}) = 1$ on the terminal descending diagram with fixed exposed basepoint to obtain $\mathcal{B}_{D_{\mathrm{terminal}}} = a(a - a^{-1}) = y = a^2 - 1$, proving $\mathcal{B}_Q = y F_Q(y)$ with $F_Q(y) \in \mathbb{Z}[y]$ and $c(Q) = F_Q(-1) = -\mathcal{B}_Q|_{a=0}$.
   - Inducts on $(m_Q, \text{active traversal steps})$ to conclude $\nu_A(Q) = c(Q)$ for uniformly left-turning $Q$, and extends to uniformly right-turning $Q$ by global orientation reversal (Proposition 4.3).
4. **Section 5 (Reconstruction of the amplitude and continuation to the whole generic locus)**:
   - Combines Lemma 3.1, Proposition 3.2, Proposition 4.3, and the left-turn sum identity $\sum_{Q \in P_S} \ell(Q) = \ell(P) + |S|$ (Eq. 1.6) to obtain $A(P) = C(P)$ on the auxiliary generic domain.
   - Extends $A(P) = C(P)$ from the open dense auxiliary generic domain to the **entire G1–G2 generic locus** using local constancy / chamber constancy of both $A(P)$ and $C(P)$.
