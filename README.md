# NSE Leray–Hopf → GP/BKQR → M7 → Serrin

We work with the three-dimensional incompressible Navier–Stokes equations

$$
\partial_t u +(u\cdot\nabla)u
=
-\nabla p+\nu\Delta u+f,
\qquad
\nabla\cdot u=0,
\qquad
u(\cdot,0)=u_0 .
$$

For the Clay-A regime we specialize to

$$
f=0,
\qquad
u_0\in C^\infty_\sigma(\mathbb R^3)
$$

with the required decay at spatial infinity.

---

## Main chain

$$
\boxed{
u_0
\longrightarrow
u_{\mathrm{LH}}
\longrightarrow
\mathrm{Enc}(u)
\longleftrightarrow
\mathrm{GP}
\longleftrightarrow
\mathrm{BKQR}
\longrightarrow
M7
\longrightarrow
\mathrm{Serrin}
\longrightarrow
\mathrm{Continuation}(u)
}
$$

The same Leray–Hopf trajectory \(u\) is preserved throughout the chain.

---

## Theorem 1 — Leray–Hopf entrance

For admissible initial data \(u_0\), there exists a global Leray–Hopf weak solution

$$
u=u_{\mathrm{LH}}(x,t),
\qquad
u(\cdot,0)=u_0 .
$$

Thus

$$
u_0
\longrightarrow
u_{\mathrm{LH}} .
$$

The framework is formulated on the full Leray–Hopf solution class, so the solutions arising from Clay-admissible initial data form a subclass of the represented regime.

---

## Theorem 2 — Leray–Hopf encoding

Every represented Leray–Hopf trajectory admits the structural encoding

$$
\mathrm{LH}(u)
\longrightarrow
\mathrm{Enc}(u).
$$

The encoding retains the original spacetime solution \(u\); it does not replace it by a different solution.

---

## Theorem 3 — GP / BKQR equivalence

The encoded solution admits equivalent GP and BKQR representations:

$$
\boxed{
\mathrm{Enc}(u)
\iff
\mathrm{GP}(u)
\iff
\mathrm{BKQR}(u)
}
$$

These representations expose the interaction structure used by the later M7 argument.

---

## Theorem 4 — M7 critical-energy mechanism

From the GP/BKQR representation, together with the required physical-realization and payment hypotheses, the M7 detector/injection mechanism applies:

$$
\mathrm{GP/BKQR}(u)
\longrightarrow
M7(u).
$$

Schematically, M7 supplies the critical control needed to prevent an uncontrolled concentration cascade.

---

## Theorem 5 — M7 to Serrin

The M7 estimate yields a Serrin-class spacetime bound:

$$
M7(u)
\longrightarrow
u\in L^q_tL^p_x,
$$

for an admissible Serrin pair satisfying

$$
\frac{2}{q}+\frac{3}{p}\le 1,
\qquad
p>3.
$$

Hence

$$
\boxed{
M7(u)\longrightarrow \mathrm{Serrin}(u).
}
$$

---

## Theorem 6 — Serrin continuation

Serrin regularity prevents a finite-time singular endpoint of the same solution:

$$
\mathrm{Serrin}(u)
\longrightarrow
\mathrm{Continuation}(u).
$$

Consequently the Leray–Hopf trajectory upgrades to the regular/strong regime on the interval under consideration.

By weak–strong uniqueness, once this upgrade is available the regular trajectory associated with the initial datum is unique.

---

# Combined theorem

The formal chain has the schematic form

$$
\boxed{
\mathrm{LH}(u)
\land
H_{\mathrm{phys}}(u)
\land
H_{\mathrm{payment}}(u)
\land
H_{\mathrm{same}}(u)
\Longrightarrow
\mathrm{Continuation}(u).
}
$$

Expanded,

$$
\boxed{
\mathrm{LH}(u)
\to
\mathrm{Enc}(u)
\leftrightarrow
\mathrm{GP}
\leftrightarrow
\mathrm{BKQR}
\to
M7
\to
\mathrm{Serrin}
\to
\mathrm{Continuation}(u).
}
$$

---

## Clay-A specialization

Let

$$
\mathcal D_{\mathrm{Clay}}
=
\left\{
u_0\in C^\infty_\sigma(\mathbb R^3)
:
u_0 \text{ has the required decay}
\right\}.
$$

Then

$$
u_0\in\mathcal D_{\mathrm{Clay}}
\Longrightarrow
\exists\,u_{\mathrm{LH}}
\Longrightarrow
u_{\mathrm{LH}}\in\mathcal{LH}(\mathbb R^3).
$$

Since

$$
\bigcup_{u_0\in\mathcal D_{\mathrm{Clay}}}
\mathcal{LH}(u_0)
\subseteq
\mathcal{LH}(\mathbb R^3),
$$

the Clay-A solution class is contained in the larger Leray–Hopf regime handled by the framework.

Thus the intended closure is

$$
\boxed{
u_0
\to
u_{\mathrm{LH}}
\to
\mathrm{GP/BKQR}
\to
M7
\to
\mathrm{Serrin}
\to
\mathrm{smooth\ continuation}
\to
\mathrm{uniqueness}.
}
$$

---

## Current formal boundary

The Lean development verifies the same-solution conditional chain and the structural Leray–Hopf / GP / BKQR / M7 / Serrin interfaces.

The remaining hypotheses should be kept explicit until discharged universally:

$$
\boxed{
H_{\mathrm{phys}},
\qquad
H_{\mathrm{payment}},
\qquad
H_{\mathrm{same}}.
}
$$

The final unconditional target is therefore

$$
\boxed{
\forall u\in\mathcal{LH}(\mathbb R^3),
\qquad
\mathrm{LH}(u)
\Longrightarrow
M7(u)
\Longrightarrow
\mathrm{Serrin}(u)
\Longrightarrow
\mathrm{Continuation}(u).
}
$$

For Clay-A data this specializes directly to the desired global regularity route.
