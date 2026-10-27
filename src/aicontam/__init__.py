"""aicontam: estimate the distribution of human answers when some participants use AI.

Implements "Dealing with AI Contamination in Behavioral Research".
"""

from .bounds import bounds
from .calibrate import Rate, estimate_fpr, estimate_tpr, flag, threshold_for_fpr
from .coding import draw_human_coding, human_coding_probs, pseudo_outcome
from .datasets import batball_population, deletion_bias, pre_ai_signals, simulate_batball
from .design import assign_arms, iv_se, plan_sample_size
from .diagnose import arm_table, first_stage, homogeneity_test, plot_curve
from .estimate import compare, delete_flagged, friction_iv, no_correction
from .latent import latent_ipw

__version__ = "0.1.0"
__all__ = ["Rate", "arm_table", "assign_arms", "batball_population", "bounds", "compare", "delete_flagged",
           "deletion_bias", "draw_human_coding", "estimate_fpr", "estimate_tpr", "first_stage", "flag",
           "friction_iv", "homogeneity_test", "human_coding_probs", "iv_se", "latent_ipw", "no_correction",
           "plan_sample_size", "plot_curve", "pre_ai_signals", "pseudo_outcome", "simulate_batball",
           "threshold_for_fpr"]
