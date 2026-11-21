# Relationship to the earlier Rule 110 and channel-memory work

This note accompanies [Essential Inputs and Memory after Coalescence in Rule 110](../paper/rule110-continuation-en.pdf).
It separates prior results, the continuation's formal results, and additional
mathematical deductions. The deductions below are not included in the 79 Lean
axiom reports.

## 1. Provenance and what the continuation adds

| Continuation result | Earlier result | Addition in this package |
| --- | --- | --- |
| Seven-site ring | Paper I gives finite-ring criteria and an exhaustive N=20 example at time 121 | Exact eventual image, minimal common preperiod 7 and period 14, and all seven essential inputs at every time from 7 onward |
| Crystal with arbitrary right tail | Paper I uses periodic backgrounds and finite transition certificates for unbounded time | A four-bit boundary window, 63 reachable certificate states, and a universal two-phase half-line invariant |
| Minimal merger time 4 | Observer monograph section 4.3 already states the threshold, eight merging environments, and the same four histories | Exact pattern classification plus a single compiled theorem joining the lower bound to the concrete witness |
| Persistent parity register | Observer theorem T4 distinguishes an immediate report from state retained for a later action | An explicit recurrence, arbitrary finite/infinite external schedules, and counterfactual inversion of all later outputs |

Primary predecessors:

- [Paper I and its verification scope](https://github.com/Dnarts/rule110-dependency-fronts/blob/046eeed7f323d3d5f973e43d5e92cfe2b8ad5429/README.md).
- [Observer theory T1-T4](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/sections/02-theory.tex).
- [Observer four-history construction and its existing minimality argument](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/sections/04-witnesses.tex).
- [Earlier open task: formalizing the 4096 environments and the return witness](https://github.com/Dnarts/rule110-dependency-fronts/blob/v2.2.1-monograph-multilingual/sections/07-discussion.tex).

The supplied Russian PDF names `MergeThreshold.lean`, but that file was absent
from the uploaded sources. The publication's [bridge](../lean/MergeThreshold.lean)
was newly constructed and compiled. This provenance is recorded in the
[verification report](../verification/REPORT.md); the four supplied mathematical
modules are preserved byte-for-byte.

## 2. One common criterion: distinguish histories that need different answers

Let U be a set of allowed histories, Y:U→{0,1} the required past bit, R the
available present observation, and M the retained memory. Exact decoding is
possible precisely when

$$R(u)=R(v)\ \Longrightarrow\ Y(u)=Y(v).$$

Writing ker for the equivalence relation induced by a map, memory restores
access precisely when

$$\ker(R,M)=\ker R\cap\ker M\subseteq\ker Y.$$

This is an application of Observer theorem T1. In the four-history witness,
R is the complete lattice at time 4. Its value is identical within each
fixed-context pair, so R alone does not determine Y. The sensor bit is retained
outside that lattice, and the remaining context supplies a decoder:

$$Z=K\oplus Y,\qquad Y=K\oplus Z.$$

The enlarged system (lattice, register) therefore never loses the relevant
distinction. No recovery from an identical total isolated deterministic state
is being asserted.

## 3. A direct channel-topology construction

For a fixed context, the Y→Z channels are

$$C^{(0)}=\begin{pmatrix}1&0\\0&1\end{pmatrix},\qquad
C^{(1)}=\begin{pmatrix}0&1\\1&0\end{pmatrix}.$$

These are in opposite components of the labeled informative binary-channel
space X₂,₂. In coordinates a=P(Z=1|Y=0), b=P(Z=1|Y=1), the sign of b−a
distinguishes the components. A continuous path between the two channels must
cross a=b, where the rows coincide.

This is the binary instance of the channel-work theorem

$$\mathfrak C_{N,K}\setminus D\simeq S^{(N-1)(K-1)-1}.$$

[Canonical topology statement and its scope](https://github.com/Dnarts/channel-topology-and-memory/blob/02f7577c6e01df1ecef6b4bc0c7d872d1878e291/compression-channel-topology/papers/sections/topology.tex).

### Forgetting versus retaining context

Choose K independent of Y with P(K=1)=λ. This is an additional probabilistic
model, not an assumption needed by the paper's exact four-history theorem.
Forgetting K gives

$$C_\lambda=\begin{pmatrix}1-\lambda&\lambda\\
\lambda&1-\lambda\end{pmatrix}.$$

At λ=1/2 both rows equal (1/2,1/2), so this channel is in D. Retaining the
output (K,Z), ordered 00,01,10,11, gives instead

$$\widetilde C_\lambda=
\begin{pmatrix}1-\lambda&0&0&\lambda\\
0&1-\lambda&\lambda&0\end{pmatrix}.$$

The two rows have disjoint supports for every λ∈[0,1]; Y=K⊕Z remains an exact
decoder throughout. For the uniform four-history distribution:

$$I(Y;K)=I(Y;Z)=0,\quad I(Y;Z\mid K)=I(Y;K,Z)=1\text{ bit}.$$

| Input and recorded output | Channel size | Property under the uniform four-history law |
| --- | --- | --- |
| H=(K,Y) → Z | 4×2 | Retains one bit about the full historical source |
| Y → Z, with K hidden | 2×2 | Identical rows; zero information about Y |
| Y → (K,Z) | 2×4 | Disjoint row supports; exact recovery of Y |

The matrices must not be identified with one another. The continuous family
in λ is a constructed family of observation channels, not the discrete time
evolution of Rule 110. It does not prove the four-step lower bound. Nor does
the topology of the full stochastic-channel space automatically describe the
subset of channels realizable by a particular cellular automaton.

## 4. An exact illustration of incremental memory value

The [memory paper](https://github.com/Dnarts/channel-topology-and-memory/blob/02f7577c6e01df1ecef6b4bc0c7d872d1878e291/compression-channel-topology/papers/sections/memory.tex)
defines an actual law p(h)C(m|h)π(a|m)T(h'|h,a), and a reference replacing
the policy by an independent action with the same action marginal. Its score is

$$\Lambda_{\mathrm{strict}}=
I(H;H')_{\mathrm{actual}}-I(H;H')_{\mathrm{reference}}.$$

Choose the four histories uniformly and define the episode-level model

$$H=(K,Y),\quad M=K\oplus Y,\quad A=M,\quad
H'=(K,K\oplus A).$$

The policy uses only M; context K is in the environment's transition. H is
the historical source label of an episode, not a claim that Y survives in the
physical lattice at time 4. Actually H'=H, so the first mutual information is
2 bits. In the reference the action is an independent fair bit; only K is
retained, giving 1 bit. Thus Λstrict=1 bit.

For comparison, memory M=K also retains one bit about H but cannot recover Y
through this mechanism. For every policy using only this M, the actual and
reference H' retain exactly K, so its optimized increment is zero. Equal
representation information can therefore have different task value.

This is a derived example in the paper's general framework. It is not an
instance of the full separation claims B/B′: those use a different source and
transition, and B′ adds an action budget. Here the useful XOR register itself
maximizes information in a binary representation of the uniform source.

## 5. Explicit temporal coupling

The [persistent-memory section](https://github.com/Dnarts/channel-topology-and-memory/blob/02f7577c6e01df1ecef6b4bc0c7d872d1878e291/compression-channel-topology/papers/sections/synthesis.tex)
requires a joint update mechanism rather than one-time channel marginals.
The continuation supplies

$$q_{n+1}=q_n\oplus Z_n,\qquad
O_n=q_{n+1}\oplus K_n=q_n\oplus Y_n.$$

The corresponding deterministic update kernel is

$$Q(q'\mid q,k,y)=\mathbf1\{q'=q\oplus k\oplus y\}.$$

The register carries the parity of past readings. Inverting q₀ inverts every
later output under the same schedule. The rule stays fixed while the carried
state changes. The lattice is reinitialized by the external schedule between
episodes; an autonomous uninterrupted binary Rule 110 realization remains a
separate task. The output need not equal Yₙ once qₙ has changed.

## 6. Influence, capacity, and robust phase storage

Seven essential input coordinates do not imply seven recoverable bits. On
the seven-site ring the late image has 15 elements, so an exact fixed-length
state code needs four bits. The deterministic channel to the complete reached
state has capacity log₂15; its entropy under a specified input law need not
equal that capacity. One observed cell is still a binary output.

The crystal result has different quantifiers from unrestricted essentiality.
Essentiality provides a witness for each coordinate and time. The crystal
theorem fixes one of two backgrounds and quantifies over every right tail.
At time 2j, the window [−j−14,−j−1] distinguishes the two phases independently
of the tail. It is a moving readout of a phase initially encoded over an
infinite half-line, not a theorem about a bounded stationary register.

## 7. Verification boundary

The continuation's [Lean audit](../verification/REPORT.md) covers its stated
formal declarations. The probabilistic channel constructions in sections 3–4
are deductions with explicit assumptions and finite checks in
[check_finite.py](../scripts/check_finite.py). They are not Lean theorems in this
package. The channel project's own [formalization scope](https://github.com/Dnarts/channel-topology-and-memory/blob/02f7577c6e01df1ecef6b4bc0c7d872d1878e291/compression-channel-topology/lean/FORMALIZATION.md)
likewise separates its geometric proof from its information-theoretic results.
