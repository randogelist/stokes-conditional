# NSE Leray–Hopf → GP/BKQR → M7 → Serrin

We consider the three-dimensional incompressible Navier–Stokes equations

$$
\partial_t u + (u\cdot\nabla)u
=
-\nabla p + \nu \Delta u + f,
$$

with

$$
\nabla\cdot u = 0,
\qquad
u(\cdot,0)=u_0.
$$

For the Clay-A regime,

$$
f=0,
$$

and the initial datum \(u_0\) is smooth, divergence-free, and rapidly decaying on \(\mathbb R^3\).

---

## Main theorem chain

$$
u_0
\longrightarrow
u_{\mathrm{LH}}
\longrightarrow
\mathrm{Enc}(u)
\longleftrightarrow
\mathrm{GP}(u)
\longleftrightarrow
\mathrm{BKQR}(u)
\longrightarrow
M7(u)
\longrightarrow
\mathrm{Serrin}(u)
\longrightarrow
\mathrm{Continuation}(u).
$$

The same Leray–Hopf trajectory \(u\) is retained throughout the chain.

---

## 1. Leray–Hopf entrance

For admissible initial data \(u_0\), Leray–Hopf existence gives a global weak solution

$$
u=u_{\mathrm{LH}}(x,t),
\qquad
u(\cdot,0)=u_0.
$$

Thus

$$
u_0
\longrightarrow
u_{\mathrm{LH}}.
$$

The framework is formulated for the Leray–Hopf solution class itself, rather than only for one special family of initial data.

---

## 2. Leray–Hopf encoding

A Leray–Hopf trajectory is mapped into the structural encoding:

$$
\mathrm{LH}(u)
\longrightarrow
\mathrm{Enc}(u).
$$

This encoding refers to the same physical spacetime trajectory \(u\).

---

## 3. GP / BKQR representation

The encoded trajectory admits the GP and BKQR representations

$$
\mathrm{Enc}(u)
\iff
\mathrm{GP}(u)
\iff
\mathrm{BKQR}(u).
$$

These representations expose the interaction structure used by the M7 argument.

---

## 4. M7 critical-energy mechanism

The GP/BKQR representation feeds the M7 detector and energy-injection mechanism:

$$
\mathrm{GP}(u)
\;\longleftrightarrow\;
\mathrm{BKQR}(u)
\longrightarrow
M7(u).
$$

At this stage the formal development isolates the physical-realization and payment interfaces required by the M7 argument.

---

## 5. M7 implies Serrin control

The M7 estimate produces a Serrin-class spacetime bound

$$
u\in L^q_t L^p_x,
$$

for an admissible Serrin pair satisfying

$$
\frac{2}{q}+\frac{3}{p}\leq 1,
\qquad
p>3.
$$

Therefore

$$
M7(u)
\longrightarrow
\mathrm{Serrin}(u).
$$

---

## 6. Serrin continuation

Serrin regularity excludes a finite-time loss of regularity for the same solution:

$$
\mathrm{Serrin}(u)
\longrightarrow
\mathrm{Continuation}(u).
$$

Hence the Leray–Hopf trajectory enters the regular/strong regime.

Once regularity is obtained, weak–strong uniqueness identifies the resulting regular trajectory uniquely with its initial datum.

---

# Combined conditional theorem

The currently verified logical form is

$$
\mathrm{LH}(u)
\land
H_{\mathrm{phys}}(u)
\land
H_{\mathrm{payment}}(u)
\land
H_{\mathrm{same}}(u)
\Longrightarrow
\mathrm{Continuation}(u).
$$

Its internal theorem chain is

$$
\mathrm{LH}(u)
\longrightarrow
\mathrm{Enc}(u)
\longleftrightarrow
\mathrm{GP}(u)
\longleftrightarrow
\mathrm{BKQR}(u)
\longrightarrow
M7(u)
\longrightarrow
\mathrm{Serrin}(u)
\longrightarrow
\mathrm{Continuation}(u).
$$

---

# Clay-A specialization

Let

$$
\mathcal D_{\mathrm{Clay}}
=
\left\{
u_0\in C^\infty_\sigma(\mathbb R^3)
:
u_0
\text{ is rapidly decaying}
\right\}.
$$

For every

$$
u_0\in\mathcal D_{\mathrm{Clay}},
$$

Leray–Hopf existence gives at least one trajectory

$$
u\in\mathcal{LH}(u_0).
$$

The Clay-A Leray–Hopf trajectories form a subclass of the full Leray–Hopf regime:

$$
\bigcup_{u_0\in\mathcal D_{\mathrm{Clay}}}
\mathcal{LH}(u_0)
\subseteq
\mathcal{LH}(\mathbb R^3).
$$

Therefore a theorem applying to all Leray–Hopf solutions automatically applies to the Clay-A subclass.

The desired specialization is

$$
u_0
\longrightarrow
u_{\mathrm{LH}}
\longrightarrow
\mathrm{GP/BKQR}
\longrightarrow
M7
\longrightarrow
\mathrm{Serrin}
\longrightarrow
\mathrm{smooth\ continuation}
\longrightarrow
\mathrm{uniqueness}.
$$

---

## Formal status

The native Lean development verifies the same-solution conditional chain

$$
\mathrm{LH}
\longrightarrow
\mathrm{Enc}
\longleftrightarrow
\mathrm{GP}
\longleftrightarrow
\mathrm{BKQR}
\longrightarrow
M7
\longrightarrow
\mathrm{Serrin}
\longrightarrow
\mathrm{Continuation}.
$$

The remaining interfaces should remain explicit until they are discharged universally:

$$
H_{\mathrm{phys}},
\qquad
H_{\mathrm{payment}},
\qquad
H_{\mathrm{same}}.
$$

The unconditional target is

$$
\forall u\in\mathcal{LH}(\mathbb R^3),
\qquad
\mathrm{LH}(u)
\Longrightarrow
M7(u)
\Longrightarrow
\mathrm{Serrin}(u)
\Longrightarrow
\mathrm{Continuation}(u).
$$

For Clay-A initial data, this theorem would apply by restriction to the corresponding Leray–Hopf subclass.
