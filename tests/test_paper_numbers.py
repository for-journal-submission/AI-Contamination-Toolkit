"""The numbers of Figure 1 and Appendix D of the paper."""

import numpy as np
import pytest

import aicontam as ac


@pytest.fixture(scope="module")
def pop():
    return ac.batball_population()


def test_arms(pop):
    t = ac.arm_table(pop.wrong, pop.flagged, pop.arm)
    assert np.allclose(t["flagged"], [0.34, 0.18, 0.14])
    assert np.allclose(t["mean[mean]"], [0.35, 0.43, 0.46])


def test_theta(pop):
    assert ac.friction_iv(pop.wrong, pop.flagged, pop.arm, 0.1, arms=(0, 1)).estimate[0] == pytest.approx(0.47)
    assert ac.friction_iv(pop.wrong, pop.flagged, pop.arm, 0.1).estimate[0] == pytest.approx(0.49)


def test_bounds(pop):
    r = ac.bounds(pop.wrong, pop.flagged, pop.arm, fpr=0.1, tpr=0.9).rows
    assert np.allclose(np.r_[r["(ii) arm 0"]], [0.35, 0.65])
    assert np.allclose(np.r_[r["(ii) arm 1"]], [0.43, 0.53])
    assert np.allclose(np.r_[r["(ii) arm 2"]], [0.46, 0.51])
    assert r["(iii) MTR"][0][0] == pytest.approx(0.46)
    assert r["(iv) MTS"][0][0] == pytest.approx(0.49)
    assert np.allclose(np.r_[r["intersection"]], [0.49, 0.51])


def test_mts_side(pop):
    h = ac.homogeneity_test(pop.wrong, pop.flagged, pop.arm, n_boot=50)
    assert h["gap"].iloc[0] == pytest.approx(0.43 - 0.438)
    assert h["side"].iloc[0] == "below"

