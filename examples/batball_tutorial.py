"""Tutorial: the bat-and-ball example of the paper, from design to estimate.

Run with `python examples/batball_tutorial.py`. It prints every step and saves the
contamination curve to `examples/contamination_curve.png`.
"""

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

import aicontam as ac

# 1. Design. How many participants does a two-arm design need for a standard error of
#    2 percentage points, if 30% use AI with the friction relaxed and 5% with it kept?
plan = ac.plan_sample_size(0.02, alpha=(0.30, 0.05), mu=0.5, ai_mean=0.0, fpr=0.1, tpr=0.9,
                           shares=(0.5, 0.5), m=300)
print("1. Design:", plan)

# Three arms make Theorem 2(iv) and the homogeneity test possible.
z = ac.assign_arms(6000, [1 / 3, 1 / 3, 1 / 3], seed=1)
print("   arms assigned:", [int((z == a).sum()) for a in range(3)])

# 2. The survey. Here we simulate it. Columns `arm`, `wrong` and `flagged` are what a
#    researcher sees. The type of each participant is hidden.
d = ac.simulate_batball(6000, arms=z, seed=1)
print("\n2. Data:\n", d[["arm", "wrong", "flagged"]].head())

# 3. Calibrate the detector on 300 answers written before AI.
fpr = ac.estimate_fpr(ac.pre_ai_signals(300, seed=2))
print(f"\n3. FPR = {fpr.value:.3f} (se {fpr.se:.3f}, from {fpr.n:.0f} pre-AI answers)")

# 4. Diagnose. The arms are the points of the contamination curve.
print("\n4. Arms:\n", ac.arm_table(d.wrong, d.flagged, d.arm))
print("\n   First stage:\n", ac.first_stage(d.flagged, d.arm))
print("\n   Is the middle arm on the line? (homogeneity test)\n",
      ac.homogeneity_test(d.wrong, d.flagged, d.arm, n_boot=499))

# The drop from arm 1 to arm 2 is small (t below 3), so the Anderson-Rubin set is the one to
# report. The middle arm lies below the line, so the curve is convex: Theorem 2(iv) applies.

# 5. Estimate. The truth is 50% wrong. No correction and deletion are biased downward.
print("\n5.", ac.friction_iv(d.wrong, d.flagged, d.arm, fpr))
print("\n   Three methods side by side:\n", ac.compare(d.wrong, d.flagged, d.arm, fpr))

# 6. Bounds that do not assume homogeneity (Theorem 2(ii)-(iv)). In the population of
#    Figure 1 they are [0.49, 0.51]; the ci columns account for sampling noise.
tpr = ac.Rate(0.9, 300)  # TPR from 300 AI answers
print("\n6. Bounds:\n", ac.bounds(d.wrong, d.flagged, d.arm, fpr, tpr, n_boot=499))

ax = ac.plot_curve(d.wrong, d.flagged, d.arm, fpr)
ax.axhline(0.5, color="gray", ls=":", lw=0.8)
plt.tight_layout()
plt.savefig("examples/contamination_curve.png", dpi=150)
print("\nSaved examples/contamination_curve.png")
