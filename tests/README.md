# Tests

Run `pytest` from the repository root. `RESULTS.md` records the last run and the numbers behind the tests; rebuild it with `python tests/report.py > tests/RESULTS.md`.

| File | What it checks |
|---|---|
| `test_paper_numbers.py` | The exact population of Figure 1 reproduces the paper: arm points, θ01 = 0.47, θ12 = 0.49, bounds [0.43, 0.53], [0.46, 0.51] and [0.49, 0.51], the side of the middle arm, and Table 1's 25% and 33%. |
| `test_inference.py` | The standard error equals the formula of the Table 2 code, Wald and Anderson–Rubin intervals cover about 95%, the Anderson–Rubin set is unbounded without a first stage, the planned N gives the planned standard error, and arms are assigned in the requested shares. |
| `test_extensions.py` | The AI-coding pseudo-outcome is unbiased with an LLM that miscodes a whole category, it works inside the IV estimator, and latent class IPW recovers the truth where deletion does not. |
| `test_plot.py` | The contamination curve plot runs. |
