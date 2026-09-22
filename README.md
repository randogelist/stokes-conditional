# NSE Leray–Hopf → GP/BKQR → M7 → Serrin

We consider the three-dimensional incompressible Navier–Stokes equations

```math
\partial_t u + (u\cdot\nabla)u
=
-\nabla p + \nu \Delta u + f
```

with

```math
\nabla\cdot u = 0,
\qquad
u(\cdot,0)=u_0.
```

For the Clay-A regime,

```math
f=0,
```

with \(u_0\) smooth, divergence-free, and rapidly decaying on \(\mathbb R^3\).

---

## Main theorem chain

```math
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
```

The same Leray–Hopf trajectory \(u\) is retained throughout the chain.

---

## 1. Leray–Hopf entrance

For admissible initial data \(u_0\), Leray–Hopf existence gives a global weak solution

```math
u=u_{\mathrm{LH}}(x,t),
\qquad
u(\cdot,0)=u_0.
```

Hence

```math
u_0
\longrightarrow
u_{\mathrm{LH}}.
```

The framework is formulated on the full Leray–Hopf solution class.

---

## 2. Leray–Hopf encoding

Every represented Leray–Hopf trajectory admits the structural encoding

```math
\mathrm{LH}(u)
\longrightarrow
\mathrm{Enc}(u).
```

The encoding retains the original spacetime solution \(u\).

---

## 3. GP / BKQR representation

The encoded trajectory admits equivalent GP and BKQR representations:

```math
\mathrm{Enc}(u)
\iff
\mathrm{GP}(u)
\iff
\mathrm{BKQR}(u).
```

These representations expose the interaction structure used by the M7 mechanism.

---

## 4. M7 critical-energy mechanism

The GP/BKQR representation feeds the M7 detector and critical-energy mechanism:

```math
\mathrm{GP}(u)
\longleftrightarrow
\mathrm{BKQR}(u)
\longrightarrow
M7(u).
```

The formal development isolates the physical-realization and payment interfaces required at this step.

---

## 5. M7 to Serrin

The M7 estimate yields Serrin-class spacetime control:

```math
u\in L^q_t L^p_x,
```

for an admissible Serrin pair satisfying

```math
\frac{2}{q}+\frac{3}{p}\leq 1,
\qquad
p>3.
```

Therefore

```math
M7(u)
\longrightarrow
\mathrm{Serrin}(u).
```

---

## 6. Serrin continuation

Serrin regularity excludes a finite-time loss of regularity for the same solution:

```math
\mathrm{Serrin}(u)
\longrightarrow
\mathrm{Continuation}(u).
```

Thus the Leray–Hopf trajectory enters the regular/strong regime.

Weak–strong uniqueness then identifies the regular trajectory uniquely with its initial datum.

---

# Combined theorem

The current conditional logical form is

```math
\mathrm{LH}(u)
\land
H_{\mathrm{phys}}(u)
\land
H_{\mathrm{payment}}(u)
\land
H_{\mathrm{same}}(u)
\Longrightarrow
\mathrm{Continuation}(u).
```

Its theorem spine is

```math
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
```

---

# Clay-A specialization

Let

```math
\mathcal D_{\mathrm{Clay}}
=
\left\{
u_0\in C^\infty_\sigma(\mathbb R^3)
:
u_0 \text{ is rapidly decaying}
\right\}.
```

For every

```math
u_0\in\mathcal D_{\mathrm{Clay}},
```

Leray–Hopf existence gives at least one trajectory

```math
u\in\mathcal{LH}(u_0).
```

The Clay-A Leray–Hopf trajectories form a subclass of the full Leray–Hopf regime:

```math
\bigcup_{u_0\in\mathcal D_{\mathrm{Clay}}}
\mathcal{LH}(u_0)
\subseteq
\mathcal{LH}(\mathbb R^3).
```

Therefore any theorem established for all Leray–Hopf solutions automatically applies to the Clay-A subclass.

The resulting chain is

```math
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
```

---

## Formal status

The native Lean development verifies the same-solution conditional chain

```math
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
```

The remaining explicit interfaces are

```math
H_{\mathrm{phys}},
\qquad
H_{\mathrm{payment}},
\qquad
H_{\mathrm{same}}.
```

The unconditional target is

```math
\forall u\in\mathcal{LH}(\mathbb R^3),
\qquad
\mathrm{LH}(u)
\Longrightarrow
M7(u)
\Longrightarrow
\mathrm{Serrin}(u)
\Longrightarrow
\mathrm{Continuation}(u).
```

For Clay-A initial data, this applies by restriction to the corresponding Leray–Hopf subclass.
