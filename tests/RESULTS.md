# Test results

## Paper numbers (exact population of Figure 1)

| Quantity | Paper | Package |
|---|---|---|
| arm 0 (flagged, wrong) | (0.34, 0.39) | (0.34, 0.39) |
| arm 1 (flagged, wrong) | (0.18, 0.43) | (0.18, 0.43) |
| arm 2 (flagged, wrong) | (0.14, 0.46) | (0.14, 0.46) |
| theta_01 | 0.45 | 0.45 |
| theta_12 | 0.49 | 0.49 |
| bound (ii) arm 1 | [0.43, 0.53] | [0.43, 0.53] |
| bound (ii) arm 2 | [0.46, 0.51] | [0.46, 0.51] |
| bound intersection | [0.49, 0.51] | [0.49, 0.51] |

## Inference (truth 0.5, homogeneous effect, N = 3,000, 400 surveys)

- Wald coverage 95.2%, Anderson-Rubin coverage 97.0% (nominal 95%)
- Sample-size plan: N = 892 for SE 0.030; simulated SE 0.028 (300 surveys)

## Extensions

- AI coding (truth 50/30/20%): LLM alone 66.3/30.3/3.3%, corrected 50.1/30.1/19.8%
- Latent class IPW (truth 40.1%): IPW 40.0%, delete flagged 32.9%, no correction 26.3%

## Edge cases

- Equal means in arms 0 and 1 (both 0, flagged 0.34 and 0.18): no monotone-response bound; intersection [0.00, 0.10], which contains a consistent truth of 0.10
- Human-coding budget after the caps: budget 0.9 -> mean pi 0.9000; budget 0.02 -> mean pi 0.0200; budget 0.3 -> mean pi 0.3000

## pytest

```
tests/test_edge_cases.py::test_mtr_equal_means_bound_nothing PASSED [  6%]
tests/test_edge_cases.py::test_coding_budget_spent_after_caps PASSED [ 12%]
tests/test_edge_cases.py::test_coding_budget_out_of_range PASSED [ 18%]
tests/test_extensions.py::test_pseudo_outcome_unbiased_with_bad_llm PASSED [ 25%]
tests/test_extensions.py::test_coding_then_iv PASSED [ 31%]
tests/test_extensions.py::test_latent_ipw_recovers_truth PASSED [ 37%]
tests/test_inference.py::test_se_matches_table2_formula PASSED [ 43%]
tests/test_inference.py::test_coverage_homogeneous PASSED [ 50%]
tests/test_inference.py::test_ar_unbounded_without_first_stage PASSED [ 56%]
tests/test_inference.py::test_plan_matches_simulation PASSED [ 62%]
tests/test_inference.py::test_assign_arms PASSED [ 68%]
tests/test_paper_numbers.py::test_arms PASSED [ 75%]
tests/test_paper_numbers.py::test_theta PASSED [ 81%]
tests/test_paper_numbers.py::test_bounds PASSED [ 87%]
tests/test_paper_numbers.py::test_mts_side PASSED [ 93%]
tests/test_plot.py::test_plot_runs PASSED [100%]
============================== 16 passed in 6.65s ==============================
```
