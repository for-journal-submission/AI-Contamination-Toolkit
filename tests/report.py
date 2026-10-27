"""Print the numbers behind the unit tests. Run `python tests/report.py > tests/RESULTS.md`."""

import numpy as np

import aicontam as ac

pop = ac.batball_population()
t = ac.arm_table(pop.wrong, pop.flagged, pop.arm)
b = ac.bounds(pop.wrong, pop.flagged, pop.arm, fpr=0.1, tpr=0.9).rows
print("# Test results\n")
print("## Paper numbers (exact population of Figure 1)\n")
print("| Quantity | Paper | Package |\n|---|---|---|")
for z, (s, g) in enumerate(zip([0.34, 0.18, 0.14], [0.35, 0.43, 0.46])):
    print(f"| arm {z} (flagged, wrong) | ({s}, {g}) | ({t.flagged[z]:.2f}, {t['mean[mean]'][z]:.2f}) |")
th01 = ac.friction_iv(pop.wrong, pop.flagged, pop.arm, 0.1, arms=(0, 1)).estimate[0]
th12 = ac.friction_iv(pop.wrong, pop.flagged, pop.arm, 0.1).estimate[0]
print(f"| theta_01 | 0.47 | {th01:.2f} |\n| theta_12 | 0.49 | {th12:.2f} |")
for name, paper in [("(ii) arm 1", "[0.43, 0.53]"), ("(ii) arm 2", "[0.46, 0.51]"), ("intersection", "[0.49, 0.51]")]:
    lo, hi = b[name]
    print(f"| bound {name} | {paper} | [{lo[0]:.2f}, {hi[0]:.2f}] |")
y0 = np.r_[np.ones(50), np.zeros(50)]
w = np.r_[np.ones(25), np.zeros(75)]
yobs = np.where(w == 1, 0, y0)
print(f"| Table 1 no correction | 25% | {100 * yobs.mean():.0f}% |")
print(f"| Table 1 delete, perfect detector | 33% | {100 * yobs[w == 0].mean():.0f}% |")

print("\n## Inference (truth 0.5, homogeneous effect, N = 3,000, 400 surveys)\n")
hw = ha = 0
for rep in range(400):
    d = ac.simulate_batball(3000, (0.4, 0.3, 0.3), wrong=[0.5] * 4, seed=rep)
    r = ac.friction_iv(d.wrong, d.flagged, d.arm, ac.estimate_fpr(ac.pre_ai_signals(300, seed=10_000 + rep)))
    lo, hi = r.ci()[0]
    hw += lo <= 0.5 <= hi
    ha += any(a <= 0.5 <= c for a, c in r.ar_sets[0])
print(f"- Wald coverage {hw / 4:.1f}%, Anderson-Rubin coverage {ha / 4:.1f}% (nominal 95%)")

plan = ac.plan_sample_size(0.03, (0.30, 0.05), 0.5, 0.0, 0.1, 0.9)
n = int(np.ceil(plan.n))
est = []
for rep in range(300):
    rng = np.random.default_rng(rep)
    z = ac.assign_arms(n, [0.5, 0.5], seed=rng)
    w = rng.uniform(size=n) < np.where(z == 0, 0.30, 0.05)
    y = np.where(w, 0, rng.uniform(size=n) < 0.5).astype(int)
    s = np.where(w, rng.uniform(size=n) < 0.9, rng.uniform(size=n) < 0.1).astype(int)
    est.append(ac.friction_iv(y, s, z, 0.1).estimate[0])
print(f"- Sample-size plan: N = {n:,} for SE 0.030; simulated SE {np.std(est):.3f} (300 surveys)")

print("\n## Extensions\n")
rng = np.random.default_rng(0)
m = 200_000
human = rng.choice(["pay", "management", "culture"], size=m, p=[0.5, 0.3, 0.2])
llm = np.where(human == "culture", "pay", human)
llm = np.where(rng.uniform(size=m) < 0.1, rng.choice(["pay", "management", "culture"], size=m), llm)
pi = np.where(rng.uniform(size=m) < 0.5, 0.05, 0.2)
xi = ac.draw_human_coding(pi, seed=1)
Yt, _ = ac.pseudo_outcome(llm, np.where(xi == 1, human, None), xi, pi, categories=["pay", "management", "culture"])
raw = [(llm == c).mean() for c in ["pay", "management", "culture"]]
print("- AI coding (truth 50/30/20%): LLM alone " + "/".join(f"{100 * v:.1f}" for v in raw)
      + "%, corrected " + "/".join(f"{100 * v:.1f}" for v in Yt.mean(0)) + "%")

rng = np.random.default_rng(7)
m = 20_000
c = (rng.uniform(size=m) < 0.4).astype(int)
w = rng.uniform(size=m) < np.array([0.1, 0.5])[c]
target = np.where(w, rng.uniform(size=m) < 0.05, rng.uniform(size=m) < np.array([0.2, 0.7])[c]).astype(int)
other = [(rng.uniform(size=m) < np.array([0.15, 0.85])[c]).astype(int) for _ in range(3)]
s = np.where(w, rng.uniform(size=m) < 0.9, rng.uniform(size=m) < 0.1).astype(int)
truth = np.mean(np.where(c == 1, 0.7, 0.2))
r = ac.latent_ipw(np.column_stack([target] + other), s, 0.1, 0.9, ai_free=(1, 2, 3), seed=1)
print(f"- Latent class IPW (truth {100 * truth:.1f}%): IPW {100 * r.ipw[1]:.1f}%, "
      f"delete flagged {100 * target[s == 0].mean():.1f}%, no correction {100 * target.mean():.1f}%")
