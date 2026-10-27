import matplotlib

matplotlib.use("Agg")

import aicontam as ac


def test_plot_runs():
    d = ac.simulate_batball(3000, seed=0)
    ax = ac.plot_curve(d.wrong, d.flagged, d.arm, fpr=0.1)
    assert ax.get_xlabel() == "flagged share"
